import Muon.PowerLaw.Profiles

/-!
# Appendix G: drift asymptotics (work package L-G.6)

Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`: `thm:app-pl-drift`
(l.881-909), `lem:app-pl-tail` (l.1447-1452), `lem:app-pl-head` (l.1498-1502),
`lem:app-pl-cutoff` (l.1536-1550), `lem:app-pl-super` (l.1631-1641); the drift halves of
`thm:app-pl-triple` (l.866-872, helpers `triple_drift_le_one`, `triple_drift_gt_one`); and the
unlabeled claim `approx_drift_lower` (l.1736-1739).
Card: `sections/06-power-law/CARD.md` §2, §3, §5 (L-G.6).

Representation choices:
* Rows. A row of the `n`-th problem is `i : Fin (N n)` with 1-based row number `rowNum i = i + 1`
  (`plSpec` indexes from zero). A row sequence is `i : (n : ℕ) → Fin (N n)` with
  `rowNum (i n) → ∞`. Every ratio `i/N`, `i/i_c` of the source is `rowNum i / N`,
  `rowNum i / icCross`.
* Spectrum `plSpec α (c n) (N n)`, aspect `γ = gammaOf (N n) (B n)`, momentum `β` and the
  regime `assum_app_pl_regime`, all reused. `√2 𝔡_i(0)` is `Real.sqrt 2 * dZero β (B n) μ i`.
* `sqrt2DPiece β B μ i lo hi` is `√2` times the part of `𝔡_i(0)` over `m ∈ (lo,hi)`, the integrand
  of `eqn:app-pl-drift-m`. So `√2 𝔡_i^{>M}` is `sqrt2DPiece … M γ` and `√2 𝔡_i^{≤M}` is
  `sqrt2DPiece … 0 M`. The set integral `∫ m in Ioo lo hi` matches `lem:app-pl-drift-participation`.
* `psiRes α η x` is `Ψ^{[η]}_α(x)`; `profPsi`, `profPhi` and `contV` are reused from Profiles and
  Continuum. `dHatSqrt2` is `√2 d̂_i` of `eqn:app-pl-approx-sub and -super`; `dHatDrift` is `d̂_i`.
* `~` is `Asymptotics.IsEquivalent`, `o(·)` is `IsLittleO`, along `atTop` in `n`. A conditional
  sentence "if i/i_cd → x then …" is one conjunct, with its displayed limit as hypothesis.
* `lem:app-pl-tail` and `lem:app-pl-head` quantify "for fixed M" as `∀ M > 0`. The "limsup ≤ C/M"
  of the tail is stated in the equivalent form `∀ ε > 0, ∀ᶠ n, ∀ i, |…| ≤ C/M + ε`.
* `lem:app-pl-cutoff` (preamble `Ψ ~ dT^ν`) is `lem_app_pl_cutoff_pre`; its parts (i)-(iii) are
  `_i`, `_ii`, `_iii`. The second clause of (iii) asserts the "applies when" sentence.
* `lem:app-pl-super`: `_i` profile (finite, continuous, positive), `_ii` and `_iii` the two ends,
  `_iv` the joint row statement.
* No certificates (`Muon.External`) are used. No definition has a hypothesis built in.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set Asymptotics
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ## Definitions -/

/-- The 1-based row number `i + 1` of the row `i : Fin N` (`plSpec` indexes rows from zero). -/
def rowNum {N : ℕ} (i : Fin N) : ℝ := ((i : ℕ) : ℝ) + 1

/-- `Ψ^{[η]}_α(x) = c_0 ∫_η^1 √((1-p)/(p V_α(p))) f_x(p) dp`, the restricted bulk profile
(`section.tex` l.1408-1412, the paragraph before `lem:app-pl-Psi`). -/
def psiRes (α η x : ℝ) : ℝ :=
  c0 * ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p

/-- `√2` times the part of `𝔡_i(0)` over `m ∈ (lo, hi)`: `(1/(πγ)) ∫_{lo}^{hi} 𝒜 𝓑_i E ϑ_N dm`
(the integrand of `eqn:app-pl-drift-m`, `section.tex` l.1373-1382). With `(lo, hi) = (0, γ)` it is
`√2 𝔡_i(0)`. -/
def sqrt2DPiece (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (lo hi : ℝ) : ℝ :=
  1 / (Real.pi * gammaOf N B) *
    ∫ m in Ioo lo hi, Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m

/-- `√2 d̂_i`, the approximant of `eqn:app-pl-approx-sub` (0<α≤1) and `eqn:app-pl-approx-super`
(α>1), `section.tex` l.851-862. Here `x = i/N` with `i` the 1-based row. -/
def dHatSqrt2 (α β c : ℝ) (N B : ℕ) (i : Fin N) : ℝ :=
  if α ≤ 1 then
    Real.sqrt (plSpec α c N i / (gammaOf N B * sPow β 2)) +
      aN α c N * profPsi α (rowNum i / (N : ℝ))
  else
    bN α c N B * profPhi α β ((icCross α B / rowNum i) ^ α) * profPsi α (rowNum i / (N : ℝ)) /
      (dAl α * Real.sqrt (Kc α) * (rowNum i / (N : ℝ)) ^ (-(α - 1) / 2))

/-- `d̂_i = (√2 d̂_i)/√2`, the drift approximant of `eqn:app-pl-triple`
(`section.tex` l.866-872). -/
def dHatDrift (α β c : ℝ) (N B : ℕ) (i : Fin N) : ℝ := dHatSqrt2 α β c N B i / Real.sqrt 2

/-- `T` of `lem:app-pl-cutoff`: `log(x^{-α})` for α<1 and `log(1/x)` for α=1. -/
def cutT (α x : ℝ) : ℝ := if α < 1 then Real.log (x ^ (-α)) else Real.log (1 / x)

/-- `ν` of `lem:app-pl-cutoff`: `1` for α<1 and `3/2` for α=1. -/
def cutNu (α : ℝ) : ℝ := if α < 1 then 1 else 3 / 2

/-- `W` of `lem:app-pl-cutoff`: `√(μ_i/(γ 𝔰_2)) / a_N`. -/
def cutW (β α c : ℝ) (N B : ℕ) (i : Fin N) : ℝ :=
  Real.sqrt (plSpec α c N i / (gammaOf N B * sPow β 2)) / aN α c N

/-! ## Statements -/

/-- `lem:app-pl-cutoff`, preamble `Ψ_α(x) ∼ d T^ν` (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[Cutoff estimates]\label{lem:app-pl-cutoff}
Let $0<\alpha\le1$, $c_N=1$, and let $i\to\infty$ with $x=i/N\to0$. Put $\nu\defeq1$ for
$\alpha<1$ and $\nu\defeq3/2$ for $\alpha=1$, and
\[
T\defeq\log(x^{-\alpha})\ (\alpha<1),\quad T\defeq\log(1/x)\ (\alpha=1),\qquad
W\defeq\frac{\sqrt{\mu_i/(\gamma\sw2)}}{a_N}=\sw2^{-1/2}e^{(T-\log\gamma)/2}.
\]
Then $\Psi_\alpha(x)\sim dT^\nu$ with $d$ of \cref{eqn:app-pl-icd}, and for fixed $M$:
\begin{enumerate}[label=(\roman*)]
\item if $W/(\log\gamma)^\nu\to z\in(0,\infty)$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim d(\log\gamma)^\nu\sim\Psi_\alpha(x)$;
\item if $W/(\log\gamma)^\nu\to\infty$, then $\Psi_\alpha(x)+\Psi_\alpha^{[M/\gamma]}(x)=o(W)$;
\item if $T\le\log\gamma+C_1\log\log\gamma$ for a constant $C_1$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim\Psi_\alpha(x)$;
this applies when $W/(\log\gamma)^\nu\to0$, and then $W=o(\Psi_\alpha(x))$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_cutoff_pre {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (hc1 : ∀ n, c n = 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))
      (fun n => icdD α * cutT α (rowNum (i n) / (N n : ℝ)) ^ cutNu α) := by
  have hxpos : ∀ n, 0 < rowNum (i n) / (N n : ℝ) := by
    intro n
    have hr : 0 < rowNum (i n) := by
      unfold rowNum
      positivity
    have hN : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact div_pos hr hN
  have hx' : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hxpos⟩
  rcases hα.lt_or_eq with hlt | heq
  · simpa only [Function.comp_def, icdD, cutT, cutNu, if_pos hlt, Real.rpow_one] using
      (lem_app_pl_Psi_ii_lt hreg.hα hlt).comp_tendsto hx'
  · subst α
    simpa only [Function.comp_def, icdD, cutT, cutNu, if_neg (lt_irrefl (1 : ℝ))] using
      (lem_app_pl_Psi_ii_one rfl).comp_tendsto hx'

private lemma pg6p3_row_pos {N : ℕ} (i : Fin N) : 0 < rowNum i := by
  unfold rowNum
  positivity

private lemma pg6p3_row_le {N : ℕ} (i : Fin N) : rowNum i ≤ (N : ℝ) := by
  unfold rowNum
  exact_mod_cast i.isLt

private lemma pg6p3_W_formula {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    cutW β α c N B i = Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) /
      (gammaOf N B * sPow β 2)) := by
  have hr := pg6p3_row_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    apply div_pos <;> linarith
  have ha : aN α c N = Real.sqrt (c * (N : ℝ) ^ (-α)) := by
    unfold aN
    rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow ((N : ℝ) ^ (-α)), ← Real.rpow_mul hNr.le]
    congr 2
    ring
  have hapos : 0 < aN α c N := by
    rw [ha]
    positivity
  have hH : Real.sqrt (plSpec α c N i / (gammaOf N B * sPow β 2)) =
      aN α c N * Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * sPow β 2)) := by
    rw [ha, ← Real.sqrt_mul (by positivity)]
    congr 1
    change c * rowNum i ^ (-α) / _ = _
    rw [Real.div_rpow hr.le hNr.le]
    have hp : 0 < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hNr _
    field_simp
  unfold cutW
  rw [hH, mul_div_cancel_left₀ _ hapos.ne']

private lemma pg6p3_T_logW {α β c : ℝ} (hα : α ≤ 1) (hc : 0 < c)
    (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    cutT α (rowNum i / (N : ℝ)) = Real.log (gammaOf N B) +
      2 * Real.log (cutW β α c N B i) + Real.log (sPow β 2) := by
  have hr := pg6p3_row_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hx : 0 < rowNum i / (N : ℝ) := div_pos hr hNr
  have hg : 0 < gammaOf N B := div_pos hNr hBr
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    apply div_pos <;> linarith
  rw [pg6p3_W_formula hc hβ0 hβ1 hN hB i,
    Real.log_sqrt (by positivity), Real.log_div (Real.rpow_pos_of_pos hx _).ne' (mul_pos hg hs).ne',
    Real.log_mul hg.ne' hs.ne']
  have ht : cutT α (rowNum i / (N : ℝ)) = Real.log ((rowNum i / (N : ℝ)) ^ (-α)) := by
    unfold cutT
    split_ifs with hlt
    · rfl
    · have heq : α = 1 := le_antisymm hα (not_lt.1 hlt)
      subst α
      rw [Real.rpow_neg_one, one_div]
  rw [ht]
  ring

private lemma pg6p3_growth {ν C : ℝ} (hν : 0 < ν) {L W T : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hWp : ∀ n, 0 < W n)
    (hW : Tendsto (fun n => W n / L n ^ ν) atTop atTop)
    (hT : ∀ n, T n = L n + 2 * Real.log (W n) + C) :
    IsLittleO atTop (fun n => T n ^ ν) W := by
  have hWtop : Tendsto W atTop atTop := by
    have hpow := (tendsto_rpow_atTop hν).comp hL
    have hm := Tendsto.atTop_mul_atTop₀ hW hpow
    refine hm.congr' ?_
    filter_upwards [hL.eventually_gt_atTop 0] with n hn
    exact div_mul_cancel₀ _ (Real.rpow_pos_of_pos hn _).ne'
  have hbase : IsLittleO atTop (fun n => L n ^ ν) W :=
    IsLittleO.of_tendsto_div_atTop hW
  have hroot : IsLittleO atTop L (fun n => W n ^ (1 / ν)) := by
    have h := hbase.rpow (one_div_pos.2 hν) (Eventually.of_forall (fun n => (hWp n).le))
    refine h.congr' ?_ Filter.EventuallyEq.rfl
    filter_upwards [hL.eventually_ge_atTop 0] with n hn
    rw [← Real.rpow_mul hn, mul_one_div_cancel hν.ne', Real.rpow_one]
  have hlog : IsLittleO atTop (fun n => Real.log (W n)) (fun n => W n ^ (1 / ν)) := by
    simpa only [Function.comp_def] using
      (isLittleO_log_rpow_atTop (one_div_pos.2 hν)).comp_tendsto hWtop
  have hconst : IsLittleO atTop (fun _ : ℕ => C) (fun n => W n ^ (1 / ν)) := by
    simpa only [Function.comp_def, id_eq] using (isLittleO_const_id_atTop (E'' := ℝ) C).comp_tendsto
      ((tendsto_rpow_atTop (one_div_pos.2 hν)).comp hWtop)
  have ht : IsLittleO atTop T (fun n => W n ^ (1 / ν)) :=
    ((hroot.add (hlog.const_mul_left 2)).add hconst).congr (fun n => (hT n).symm) (fun _ => rfl)
  have hp := ht.rpow hν (Eventually.of_forall (fun n => (Real.rpow_pos_of_pos (hWp n) _).le))
  refine hp.congr (fun _ => rfl) (fun n => ?_)
  rw [← Real.rpow_mul (hWp n).le, one_div_mul_cancel hν.ne', Real.rpow_one]

private lemma pg6p3_res_bounds {α x η : ℝ} (hα : 0 < α) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    0 ≤ psiRes α η x ∧ psiRes α η x ≤ profPsi α x := by
  have hc : 0 ≤ c0 := by unfold c0; positivity
  have hint := lem_app_pl_Psi_i_integrable hα x hx
  have h0η := hint.mono_set (show uIcc 0 η ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hη1)
  have hη1i := hint.mono_set (show uIcc η 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hη0 le_rfl)
  have hnn : ∀ p ∈ Icc (0 : ℝ) 1,
      0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    intro p hp
    by_cases hp0 : p = 0
    · simp [hp0]
    by_cases hp1 : p = 1
    · simp [hp1]
    have hp' : p ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_le_of_ne hp.1 (Ne.symm hp0), lt_of_le_of_ne hp.2 hp1⟩
    have hV : ∃ V ∈ Ioi (0 : ℝ), contS α V = p :=
      (def_app_pl_profiles_S_bij hα).2.surjOn hp'
    have hVp : 0 < contV α p := Function.invFunOn_mem hV
    have hxp : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 _
    unfold profF
    positivity
  have hn0 := intervalIntegral.integral_nonneg (μ := volume) hη0 (fun p hp => hnn p ⟨hp.1, hp.2.trans hη1⟩)
  have hn1 := intervalIntegral.integral_nonneg (μ := volume) hη1 (fun p hp => hnn p ⟨hη0.trans hp.1, hp.2⟩)
  constructor
  · exact mul_nonneg hc hn1
  · unfold psiRes profPsi
    rw [← intervalIntegral.integral_add_adjacent_intervals h0η hη1i]
    exact mul_le_mul_of_nonneg_left (by linarith) hc

private lemma pg6p3_prof_cont_on {α V : ℝ} (hα0 : 0 < α) (hV : 0 < V) :
    ContinuousOn (fun t : ℝ => V / (V + t ^ α)) (Set.uIcc 0 1) := by
  apply ContinuousOn.div continuousOn_const
  · exact (continuous_const.add (Real.continuous_rpow_const hα0.le)).continuousOn
  · intro t ht
    have ht' : (0:ℝ) ≤ t := (by rwa [Set.uIcc_of_le (zero_le_one : (0:ℝ) ≤ 1)] at ht : t ∈ Set.Icc (0:ℝ) 1).1
    have h0 : 0 ≤ t ^ α := Real.rpow_nonneg ht' α
    exact (by linarith : (0:ℝ) < V + t ^ α).ne'


private lemma pg6p3_prof_contV_spec {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p ∧ contS α (contV α p) = p := by
  have h : ∃ a ∈ Ioi (0:ℝ), contS α a = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact ⟨Set.mem_Ioi.1 (Function.invFunOn_mem h), Function.invFunOn_eq h⟩


private lemma pg6p3_prof_V_mul_le {α p : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) :
    (1 - p) * contV α p ≤ p := by
  have hV := (pg6p3_prof_contV_spec hα hp).1
  have hS : contV α p / (contV α p + 1) ≤ contS α (contV α p) := by
    unfold contS
    have hint : ∫ t in (0:ℝ)..1, contV α p / (contV α p + 1)
        ≤ ∫ t in (0:ℝ)..1, contV α p / (contV α p + t ^ α) := by
      apply intervalIntegral.integral_mono_on zero_le_one intervalIntegrable_const
        (pg6p3_prof_cont_on hα hV).intervalIntegrable
      intro t ht
      have h1 : t ^ α ≤ 1 := Real.rpow_le_one ht.1 ht.2 hα.le
      have h2 : 0 ≤ t ^ α := Real.rpow_nonneg ht.1 α
      exact div_le_div_of_nonneg_left hV.le (by linarith) (by linarith)
    have hc : ∫ t in (0:ℝ)..1, contV α p / (contV α p + 1)
        = contV α p / (contV α p + 1) := by simp
    rw [hc] at hint
    exact hint
  rw [(pg6p3_prof_contV_spec hα hp).2] at hS
  rw [div_le_iff₀ (by linarith)] at hS
  nlinarith

private lemma pg6p3_prof_u_bound {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioc (0:ℝ) 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ 1 / x ^ α := by
  rcases eq_or_lt_of_le hp.2 with h1 | h1
  · rw [h1]
    simp only [sub_self, zero_div, Real.sqrt_zero, zero_mul]
    exact ⟨le_rfl, (one_div_pos.2 (Real.rpow_pos_of_pos hx α)).le⟩
  · have hp' : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, h1⟩
    have hV := (pg6p3_prof_contV_spec hα hp').1
    have hmul := pg6p3_prof_V_mul_le hα hp'
    have hp0 : 0 < p := hp.1
    have hpn : p ≠ 0 := hp0.ne'
    have hVn : contV α p ≠ 0 := hV.ne'
    have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx α
    unfold profF
    set V := contV α p with hVdef
    have ha : 0 ≤ (1 - p) / (p * V) := div_nonneg (by linarith [hp'.2]) (mul_nonneg hp0.le hV.le)
    have hs2 : Real.sqrt ((1 - p) / (p * V)) ^ 2 = (1 - p) / (p * V) := Real.sq_sqrt ha
    set s := Real.sqrt ((1 - p) / (p * V)) with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hsV : s * V ≤ 1 := by
      have hsq : (s * V) ^ 2 ≤ 1 := by
        have e : (s * V) ^ 2 = (1 - p) * V / p := by
          rw [mul_pow, hs2]
          field_simp
        rw [e, div_le_one hp0]
        exact hmul
      nlinarith [mul_nonneg hs0 hV.le]
    refine ⟨mul_nonneg hs0 (div_nonneg hV.le (by linarith)), ?_⟩
    rw [← mul_div_assoc]
    calc s * V / (V + x ^ α) ≤ 1 / (V + x ^ α) :=
          div_le_div_of_nonneg_right hsV (by linarith)
      _ ≤ 1 / x ^ α := one_div_le_one_div_of_le hD (by linarith)

private lemma pg6p3_res_compare {α x y η : ℝ} (hα : 0 < α)
    (hx : x ∈ Ioc (0 : ℝ) 1) (hy : y ∈ Ioc (0 : ℝ) 1) (hxy : x ≤ y)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) :
    profPsi α y - c0 * (η / y ^ α) ≤ psiRes α η x := by
  have hc : 0 ≤ c0 := by unfold c0; positivity
  have hi := lem_app_pl_Psi_i_integrable hα y hy
  have hi0 := hi.mono_set (show uIcc 0 η ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη0, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl hη1)
  have hi1 := hi.mono_set (show uIcc η 1 ⊆ uIcc (0 : ℝ) 1 by
    rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc hη0 le_rfl)
  have hix := (lem_app_pl_Psi_i_integrable hα x hx).mono_set
    (show uIcc η 1 ⊆ uIcc (0 : ℝ) 1 by
      rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]
      exact Icc_subset_Icc hη0 le_rfl)
  have hhead : (∫ p in (0 : ℝ)..η, Real.sqrt ((1 - p) / (p * contV α p)) * profF α y p) ≤
      η / y ^ α := by
    have hb := intervalIntegral.integral_mono_on_of_le_Ioo hη0 hi0
      (intervalIntegrable_const (c := 1 / y ^ α))
      (fun p hp => (pg6p3_prof_u_bound hα hy.1 ⟨hp.1, hp.2.le.trans hη1⟩).2)
    simpa [div_eq_mul_inv] using hb
  have htail : (∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α y p) ≤
      ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hη1 hi1 hix
    intro p hp
    have hp0 : 0 < p := lt_of_le_of_lt hη0 hp.1
    have hV := (pg6p3_prof_contV_spec hα ⟨hp0, hp.2⟩).1
    have hxα := Real.rpow_pos_of_pos hx.1 α
    have hxyα := Real.rpow_le_rpow hx.1.le hxy hα.le
    apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
    unfold profF
    exact div_le_div_of_nonneg_left hV.le (by positivity) (by linarith)
  unfold profPsi psiRes
  rw [← intervalIntegral.integral_add_adjacent_intervals hi0 hi1]
  nlinarith [mul_le_mul_of_nonneg_left hhead hc, mul_le_mul_of_nonneg_left htail hc]

private lemma pg6p3_T_eq {α x : ℝ} (hα : α ≤ 1) (hx : 0 < x) :
    cutT α x = -α * Real.log x := by
  unfold cutT
  split_ifs with hlt
  · exact Real.log_rpow hx _
  · have he : α = 1 := le_antisymm hα (not_lt.1 hlt)
    subst α
    simp [one_div, Real.log_inv]

private lemma pg6p3_profile {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (profPsi α) (fun x => icdD α * cutT α x ^ cutNu α) := by
  rcases hα1.lt_or_eq with hlt | heq
  · simpa only [icdD, cutT, cutNu, if_pos hlt, Real.rpow_one] using
      lem_app_pl_Psi_ii_lt hα0 hlt
  · subst α
    simpa only [icdD, cutT, cutNu, if_neg (lt_irrefl (1 : ℝ))] using
      lem_app_pl_Psi_ii_one rfl

private lemma pg6p3_d_pos {α : ℝ} (hα : α ≤ 1) : 0 < icdD α := by
  have hc : 0 < c0 := by unfold c0; positivity
  unfold icdD
  split_ifs with hlt
  · exact div_pos hc (Real.sqrt_pos.2 (sub_pos.2 hlt))
  · positivity

private lemma pg6p3_profile_scale {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ n, x n ∈ Ioc (0 : ℝ) 1)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun n => profPsi α (x n ^ q) / profPsi α (x n)) atTop (𝓝 (q ^ cutNu α)) := by
  have hy := hx.rpow_const_nhds_zero hq
  have hx' : Tendsto x atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall (fun n => (hxp n).1)⟩
  have hy' : Tendsto (fun n => x n ^ q) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hy, Eventually.of_forall (fun n => Real.rpow_pos_of_pos (hxp n).1 _)⟩
  have hp := pg6p3_profile hα0 hα1
  have he := (hp.comp_tendsto hy').div (hp.comp_tendsto hx')
  have he' : IsEquivalent atTop
      (fun n => profPsi α (x n ^ q) / profPsi α (x n)) (fun _ => q ^ cutNu α) := by
    refine he.congr_right ?_
    have hxlt := hx.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hxlt] with n hn
    have hT : 0 < cutT α (x n) := by
      rw [pg6p3_T_eq hα1 (hxp n).1]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos hα0) (Real.log_neg (hxp n).1 hn)
    have hTy : cutT α (x n ^ q) = q * cutT α (x n) := by
      rw [pg6p3_T_eq hα1 (Real.rpow_pos_of_pos (hxp n).1 _),
        pg6p3_T_eq hα1 (hxp n).1, Real.log_rpow (hxp n).1]
      ring
    change icdD α * cutT α (x n ^ q) ^ cutNu α /
      (icdD α * cutT α (x n) ^ cutNu α) = q ^ cutNu α
    rw [hTy, Real.mul_rpow hq.le hT.le]
    have hd := (pg6p3_d_pos hα1).ne'
    have ht := (Real.rpow_pos_of_pos hT (cutNu α)).ne'
    field_simp
  exact he'.symm.tendsto_nhds tendsto_const_nhds

private lemma pg6p3_removed_small {α C M : ℝ} (hα : α ≤ 1) {x L : ℕ → ℝ}
    (hx : ∀ n, 0 < x n) (hL : Tendsto L atTop atTop)
    (hT : ∀ᶠ n in atTop, cutT α (x n) ≤ L n + C * Real.log (L n))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Tendsto (fun n => M * Real.exp (-L n) / (x n ^ q) ^ α) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (L n) / L n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL
  have hcoef : Tendsto (fun n => q - 1 + q * C * (Real.log (L n) / L n)) atTop (𝓝 (q - 1)) := by
    simpa using tendsto_const_nhds.add (hlog.const_mul (q * C))
  have hneg := hL.atTop_mul_neg (sub_neg.2 hq1) hcoef
  have he : Tendsto (fun n => Real.exp (-L n + q * cutT α (x n))) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => (Real.exp_pos _).le)) ?_
      (Real.tendsto_exp_atBot.comp hneg)
    filter_upwards [hT, hL.eventually_gt_atTop 0] with n hn hLn
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_left hn hq0.le
    field_simp
    nlinarith
  have hm := he.const_mul M
  simpa only [mul_zero] using hm.congr (fun n => by
    rw [Real.rpow_def_of_pos (Real.rpow_pos_of_pos (hx n) q), Real.log_rpow (hx n),
      pg6p3_T_eq hα (hx n), mul_div_assoc, ← Real.exp_sub]
    congr 2
    ring)

private lemma pg6p3_cutoff {α C M : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x L : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ n, x n ∈ Ioc (0 : ℝ) 1)
    (hL : Tendsto L atTop atTop) (hM : 0 < M)
    (hT : ∀ᶠ n in atTop, cutT α (x n) ≤ L n + C * Real.log (L n)) :
    IsEquivalent atTop (fun n => psiRes α (M * Real.exp (-L n)) (x n)) (fun n => profPsi α (x n)) := by
  have hψpos : ∀ n, 0 < profPsi α (x n) := fun n => lem_app_pl_Psi_i_pos hα0 _ (hxp n)
  have hx' : Tendsto x atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall (fun n => (hxp n).1)⟩
  have hTtop : Tendsto (fun n => cutT α (x n)) atTop atTop := by
    have h := (Real.tendsto_log_nhdsGT_zero.comp hx').const_mul_atBot_of_neg (neg_neg_of_pos hα0)
    exact h.congr (fun n => (pg6p3_T_eq hα1 (hxp n).1).symm)
  have hν : 0 < cutNu α := by unfold cutNu; split_ifs <;> norm_num
  have hψtop : Tendsto (fun n => profPsi α (x n)) atTop atTop := by
    have hpower := ((tendsto_rpow_atTop hν).comp hTtop).const_mul_atTop (pg6p3_d_pos hα1)
    exact ((pg6p3_profile hα0 hα1).comp_tendsto hx').symm.tendsto_atTop hpower
  have hηlim : Tendsto (fun n => M * Real.exp (-L n)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hL)).const_mul M
  have hηsmall := hηlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  apply isEquivalent_of_tendsto_one
  apply tendsto_order.2
  constructor
  · intro a ha
    have hqLim : Tendsto (fun q : ℝ => q ^ cutNu α) (𝓝[<] 1) (𝓝 1) := by
      simpa using (Real.continuousAt_rpow_const (1 : ℝ) (cutNu α) (by left; norm_num)).tendsto.mono_left
        (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    obtain ⟨q, haq, hq⟩ := ((hqLim.eventually (lt_mem_nhds ha)).and
      (Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num))).exists
    have hscale := pg6p3_profile_scale hα0 hα1 hx hxp hq.1
    have hrem := pg6p3_removed_small hα1 (fun n => (hxp n).1) hL hT hq.1 hq.2 (M := M)
    have hrem' : Tendsto (fun n => c0 * (M * Real.exp (-L n) / (x n ^ q) ^ α) /
        profPsi α (x n)) atTop (𝓝 0) := (hrem.const_mul c0).div_atTop hψtop
    have hlo := (hscale.sub hrem').eventually (lt_mem_nhds (by simpa using haq))
    filter_upwards [hlo, hηsmall] with n hn hηn
    have hqxp : x n ^ q ∈ Ioc (0 : ℝ) 1 :=
      ⟨Real.rpow_pos_of_pos (hxp n).1 _, Real.rpow_le_one (hxp n).1.le (hxp n).2 hq.1.le⟩
    have hxy : x n ≤ x n ^ q := by
      simpa using Real.rpow_le_rpow_of_exponent_ge (hxp n).1 (hxp n).2 hq.2.le
    have hb := pg6p3_res_compare hα0 (hxp n) hqxp hxy (by positivity : 0 ≤ M * Real.exp (-L n)) hηn.le
    have hb' := div_le_div_of_nonneg_right hb (hψpos n).le
    simp only [sub_div] at hb'
    exact hn.trans_le hb'
  · intro b hb
    filter_upwards [hηsmall] with n hn
    have hbound := (pg6p3_res_bounds hα0 (hxp n) (by positivity : 0 ≤ M * Real.exp (-L n)) hn.le).2
    exact lt_of_le_of_lt ((div_le_one (hψpos n)).2 hbound) hb

private lemma pg6p3_balanced {ν C z : ℝ} {L W T : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hWp : ∀ n, 0 < W n) (hz : 0 < z)
    (hW : Tendsto (fun n => W n / L n ^ ν) atTop (𝓝 z))
    (hT : ∀ n, T n = L n + 2 * Real.log (W n) + C) :
    Tendsto (fun n => T n / L n) atTop (𝓝 1) := by
  have hlogR := (Real.continuousAt_log hz.ne').tendsto.comp hW
  have hR := hlogR.div_atTop hL
  have hC := (tendsto_const_nhds (x := C)).div_atTop hL
  have hlog : Tendsto (fun n => Real.log (L n) / L n) atTop (𝓝 0) := by
    simpa only [Function.comp_def, id_eq] using Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL
  have h := ((tendsto_const_nhds (x := (1 : ℝ))).add
    ((hlog.const_mul (2 * ν)).add ((hR.const_mul 2).add hC)))
  simp only [mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [hL.eventually_gt_atTop 0] with n hn
  have he : Real.log (W n) = Real.log (W n / L n ^ ν) + ν * Real.log (L n) := by
    rw [Real.log_div (hWp n).ne' (Real.rpow_pos_of_pos hn _).ne', Real.log_rpow hn]
    ring
  rw [hT n, he]
  dsimp only [Function.comp_def]
  field_simp
  ring

private lemma pg6p3_smallW {ν C : ℝ} (hν : 0 < ν) {L W T : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hTtop : Tendsto T atTop atTop) (hWp : ∀ n, 0 < W n)
    (hW : Tendsto (fun n => W n / L n ^ ν) atTop (𝓝 0))
    (hT : ∀ n, T n = L n + 2 * Real.log (W n) + C) :
    (∃ C1 : ℝ, ∀ᶠ n in atTop, T n ≤ L n + C1 * Real.log (L n)) ∧
      IsLittleO atTop W (fun n => T n ^ ν) := by
  constructor
  · refine ⟨2 * ν + |C|, ?_⟩
    filter_upwards [hL.eventually_gt_atTop 0,
      (Real.tendsto_log_atTop.comp hL).eventually_ge_atTop 1,
      hW.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hLn hlog hn
    have hpow := Real.rpow_pos_of_pos hLn ν
    have hw : W n ≤ L n ^ ν := ((div_le_one hpow).1 hn.le)
    have hlw := Real.log_le_log (hWp n) hw
    rw [Real.log_rpow hLn] at hlw
    rw [hT n]
    have hc := le_abs_self C
    have hc' := mul_le_mul_of_nonneg_left hlog (abs_nonneg C)
    dsimp only [Function.comp_def] at hc'
    nlinarith
  · apply (isLittleO_iff_tendsto' ((hTtop.eventually_gt_atTop 0).mono
      (fun n hn hz => False.elim ((Real.rpow_pos_of_pos hn ν).ne' hz)))).2
    have hexp : Tendsto (fun n => Real.exp (-L n / 4 - C / 2)) atTop (𝓝 0) := by
      have hh := (Real.tendsto_exp_atBot.comp
        (hL.const_mul_atTop_of_neg (by norm_num : (-1 / 4 : ℝ) < 0))).mul_const (Real.exp (-C / 2))
      simp only [zero_mul] at hh
      refine hh.congr (fun n => ?_)
      dsimp only [Function.comp_def]
      rw [← Real.exp_add]
      congr 1
      ring
    have hbound : Tendsto (fun n => 2 ^ ν * (W n / L n ^ ν) + Real.exp (-L n / 4 - C / 2))
        atTop (𝓝 0) := by simpa using (hW.const_mul (2 ^ ν)).add hexp
    refine squeeze_zero' ?_ ?_ hbound
    · filter_upwards [hTtop.eventually_gt_atTop 0] with n hn
      exact (div_pos (hWp n) (Real.rpow_pos_of_pos hn _)).le
    · filter_upwards [hL.eventually_gt_atTop 0, hTtop.eventually_ge_atTop 1] with n hLn hTn
      have hTn0 : 0 < T n := lt_of_lt_of_le zero_lt_one hTn
      have hTp := Real.rpow_pos_of_pos hTn0 ν
      have hLp := Real.rpow_pos_of_pos hLn ν
      have hpart : W n / T n ^ ν ≤ 2 ^ ν * (W n / L n ^ ν) ∨
          W n / T n ^ ν ≤ Real.exp (-L n / 4 - C / 2) := by
        by_cases hb : L n / 2 ≤ T n
        · left
          have hh : L n ^ ν ≤ 2 ^ ν * T n ^ ν := by
            rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hTn0.le]
            exact Real.rpow_le_rpow hLn.le (by linarith) hν.le
          rw [div_le_iff₀ hTp]
          calc W n = W n * L n ^ ν / L n ^ ν := by field_simp
            _ ≤ W n * (2 ^ ν * T n ^ ν) / L n ^ ν :=
              div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hh (hWp n).le) hLp.le
            _ = _ := by ring
        · right
          have he : W n ≤ Real.exp (-L n / 4 - C / 2) := by
            rw [← Real.exp_log (hWp n)]
            apply Real.exp_le_exp.2
            have ht := hT n
            linarith
          exact (div_le_self (hWp n).le (Real.one_le_rpow hTn hν.le)).trans he
      rcases hpart with hb | hb
      · exact hb.trans (le_add_of_nonneg_right (Real.exp_pos _).le)
      · exact hb.trans (le_add_of_nonneg_left (mul_nonneg
          (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) ν).le (div_pos (hWp n) hLp).le))

private lemma pg6p3_W_pos {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N) : 0 < cutW β α c N B i := by
  rw [pg6p3_W_formula hc hβ0 hβ1 hN hB]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]
    apply div_pos <;> linarith
  have hx : 0 < rowNum i / (N : ℝ) := div_pos (pg6p3_row_pos i) hNr
  unfold gammaOf
  exact Real.sqrt_pos.2 (div_pos (Real.rpow_pos_of_pos hx _) (mul_pos (div_pos hNr hBr) hs))

private lemma pg6p3_T_top {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1)
    {x : ℕ → ℝ} (hx : Tendsto x atTop (𝓝 0)) (hxp : ∀ n, 0 < x n) :
    Tendsto (fun n => cutT α (x n)) atTop atTop := by
  have hx' : Tendsto x atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall hxp⟩
  have h := (Real.tendsto_log_nhdsGT_zero.comp hx').const_mul_atBot_of_neg (neg_neg_of_pos hα0)
  exact h.congr (fun n => (pg6p3_T_eq hα1 (hxp n)).symm)

private lemma pg6p3_gamma_exp {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (M : ℝ) :
    M * Real.exp (-Real.log (gammaOf N B)) = M / gammaOf N B := by
  have hg : 0 < gammaOf N B := div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  rw [Real.exp_neg, Real.exp_log hg, div_eq_mul_inv]

private lemma pg6p3_boundT {ν C K : ℝ} (hK : 0 < K) {L W T : ℕ → ℝ}
    (hL : Tendsto L atTop atTop) (hWp : ∀ n, 0 < W n)
    (hW : ∀ᶠ n in atTop, W n / L n ^ ν ≤ K)
    (hT : ∀ n, T n = L n + 2 * Real.log (W n) + C) :
    ∃ C1 : ℝ, ∀ᶠ n in atTop, T n ≤ L n + C1 * Real.log (L n) := by
  refine ⟨2 * ν + |2 * Real.log K + C|, ?_⟩
  filter_upwards [hW, hL.eventually_gt_atTop 0,
    (Real.tendsto_log_atTop.comp hL).eventually_ge_atTop 1] with n hn hLn hlog
  have hw : W n ≤ K * L n ^ ν := (div_le_iff₀ (Real.rpow_pos_of_pos hLn _)).1 hn
  have hl := Real.log_le_log (hWp n) hw
  rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hLn _).ne', Real.log_rpow hLn] at hl
  rw [hT n]
  have hc := le_abs_self (2 * Real.log K + C)
  have hc' := mul_le_mul_of_nonneg_left hlog (abs_nonneg (2 * Real.log K + C))
  dsimp only [Function.comp_def] at hc'
  nlinarith

/-- `lem:app-pl-cutoff`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[Cutoff estimates]\label{lem:app-pl-cutoff}
Let $0<\alpha\le1$, $c_N=1$, and let $i\to\infty$ with $x=i/N\to0$. Put $\nu\defeq1$ for
$\alpha<1$ and $\nu\defeq3/2$ for $\alpha=1$, and
\[
T\defeq\log(x^{-\alpha})\ (\alpha<1),\quad T\defeq\log(1/x)\ (\alpha=1),\qquad
W\defeq\frac{\sqrt{\mu_i/(\gamma\sw2)}}{a_N}=\sw2^{-1/2}e^{(T-\log\gamma)/2}.
\]
Then $\Psi_\alpha(x)\sim dT^\nu$ with $d$ of \cref{eqn:app-pl-icd}, and for fixed $M$:
\begin{enumerate}[label=(\roman*)]
\item if $W/(\log\gamma)^\nu\to z\in(0,\infty)$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim d(\log\gamma)^\nu\sim\Psi_\alpha(x)$;
\item if $W/(\log\gamma)^\nu\to\infty$, then $\Psi_\alpha(x)+\Psi_\alpha^{[M/\gamma]}(x)=o(W)$;
\item if $T\le\log\gamma+C_1\log\log\gamma$ for a constant $C_1$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim\Psi_\alpha(x)$;
this applies when $W/(\log\gamma)^\nu\to0$, and then $W=o(\Psi_\alpha(x))$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_cutoff_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (hc1 : ∀ n, c n = 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (M : ℝ) (hM : 0 < M) (z : ℝ) (hz : 0 < z)
    (hW : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 z)) :
    IsEquivalent atTop (fun n => psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
        (fun n => icdD α * Real.log (gammaOf (N n) (B n)) ^ cutNu α) ∧
      IsEquivalent atTop (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))
        (fun n => icdD α * Real.log (gammaOf (N n) (B n)) ^ cutNu α) := by
  have hxp : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    intro n
    have hN : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨div_pos (pg6p3_row_pos _) hN, (div_le_one hN).2 (pg6p3_row_le _)⟩
  have hWp : ∀ n, 0 < cutW β α (c n) (N n) (B n) (i n) := fun n =>
    pg6p3_W_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) _
  have hL := Real.tendsto_log_atTop.comp hreg.hγ
  have hT := fun n => pg6p3_T_logW hα (hreg.hcpos n) hreg.hβ0 hreg.hβ1
    (hreg.hNpos n) (hreg.hBpos n) (i n)
  have hTL := pg6p3_balanced hL hWp hz hW hT
  obtain ⟨C1, hbound⟩ := pg6p3_boundT (by linarith : 0 < z + 1) hL hWp
    ((hW.eventually (gt_mem_nhds (by linarith : z < z + 1))).mono (fun _ hn => hn.le)) hT
  have hcut := pg6p3_cutoff hreg.hα hα hx hxp hL hM hbound
  have hcut' : IsEquivalent atTop
      (fun n => psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ))) :=
    hcut.congr_left (Eventually.of_forall (fun n => by
      change psiRes α (M * Real.exp (-Real.log (gammaOf (N n) (B n)))) _ = _
      rw [pg6p3_gamma_exp (hreg.hNpos n) (hreg.hBpos n)]))
  have hpow : IsEquivalent atTop
      (fun n => cutT α (rowNum (i n) / (N n : ℝ)) ^ cutNu α)
      (fun n => Real.log (gammaOf (N n) (B n)) ^ cutNu α) := by
    apply isEquivalent_of_tendsto_one
    have hh := hTL.rpow_const (p := cutNu α) (Or.inl one_ne_zero)
    rw [Real.one_rpow] at hh
    refine hh.congr' ?_
    filter_upwards [hL.eventually_ge_atTop 0,
      (pg6p3_T_top hreg.hα hα hx (fun n => (hxp n).1)).eventually_ge_atTop 0] with n hLn hTn
    exact Real.div_rpow hTn hLn (cutNu α)
  have hψ := (lem_app_pl_cutoff_pre hreg hα hc1 i hi hx).trans
    ((IsEquivalent.refl (u := fun _ : ℕ => icdD α)).mul hpow)
  exact ⟨hcut'.trans hψ, hψ⟩

/-- `lem:app-pl-cutoff`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[Cutoff estimates]\label{lem:app-pl-cutoff}
Let $0<\alpha\le1$, $c_N=1$, and let $i\to\infty$ with $x=i/N\to0$. Put $\nu\defeq1$ for
$\alpha<1$ and $\nu\defeq3/2$ for $\alpha=1$, and
\[
T\defeq\log(x^{-\alpha})\ (\alpha<1),\quad T\defeq\log(1/x)\ (\alpha=1),\qquad
W\defeq\frac{\sqrt{\mu_i/(\gamma\sw2)}}{a_N}=\sw2^{-1/2}e^{(T-\log\gamma)/2}.
\]
Then $\Psi_\alpha(x)\sim dT^\nu$ with $d$ of \cref{eqn:app-pl-icd}, and for fixed $M$:
\begin{enumerate}[label=(\roman*)]
\item if $W/(\log\gamma)^\nu\to z\in(0,\infty)$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim d(\log\gamma)^\nu\sim\Psi_\alpha(x)$;
\item if $W/(\log\gamma)^\nu\to\infty$, then $\Psi_\alpha(x)+\Psi_\alpha^{[M/\gamma]}(x)=o(W)$;
\item if $T\le\log\gamma+C_1\log\log\gamma$ for a constant $C_1$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim\Psi_\alpha(x)$;
this applies when $W/(\log\gamma)^\nu\to0$, and then $W=o(\Psi_\alpha(x))$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_cutoff_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (hc1 : ∀ n, c n = 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (M : ℝ) (hM : 0 < M)
    (hW : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop) :
    IsLittleO atTop
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) +
        psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
      (fun n => cutW β α (c n) (N n) (B n) (i n)) := by
  have hν : 0 < cutNu α := by unfold cutNu; split_ifs <;> norm_num
  have hxpos : ∀ n, 0 < rowNum (i n) / (N n : ℝ) := fun n =>
    div_pos (pg6p3_row_pos _) (by exact_mod_cast hreg.hNpos n)
  have hWpos : ∀ n, 0 < cutW β α (c n) (N n) (B n) (i n) := by
    intro n
    rw [pg6p3_W_formula (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n)]
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    have hs : 0 < sPow β 2 := by
      rw [sPow_two hreg.hβ0.le hreg.hβ1]
      apply div_pos <;> linarith [hreg.hβ0, hreg.hβ1]
    unfold gammaOf
    exact Real.sqrt_pos.2 (div_pos (Real.rpow_pos_of_pos (hxpos n) _) (mul_pos (div_pos hNr hBr) hs))
  have hsmall := pg6p3_growth hν (Real.tendsto_log_atTop.comp hreg.hγ) hWpos hW
    (fun n => pg6p3_T_logW hα (hreg.hcpos n) hreg.hβ0 hreg.hβ1
      (hreg.hNpos n) (hreg.hBpos n) (i n))
  have hψ := (lem_app_pl_cutoff_pre hreg hα hc1 i hi hx).isBigO.trans_isLittleO
    (hsmall.const_mul_left (icdD α))
  rw [isLittleO_iff] at hψ ⊢
  intro ε hε
  filter_upwards [hψ (half_pos hε), hreg.hγ.eventually_ge_atTop M,
      hreg.hγ.eventually_gt_atTop 0] with n hn hγM hγ0
  have hx1 : rowNum (i n) / (N n : ℝ) ≤ 1 :=
    (div_le_one (by exact_mod_cast hreg.hNpos n)).2 (pg6p3_row_le _)
  have hη : M / gammaOf (N n) (B n) ≤ 1 := (div_le_one hγ0).2 hγM
  obtain ⟨hres0, hres⟩ := pg6p3_res_bounds hreg.hα ⟨hxpos n, hx1⟩
    (div_pos hM hγ0).le hη
  change 0 ≤ psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) at hres0
  change psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) ≤ _ at hres
  have hψ0 := ((lem_app_pl_Psi_i_pos hreg.hα) _ ⟨hxpos n, hx1⟩).le
  rw [Real.norm_of_nonneg hψ0, Real.norm_of_nonneg (hWpos n).le] at hn
  rw [Real.norm_of_nonneg (add_nonneg hψ0 hres0), Real.norm_of_nonneg (hWpos n).le]
  nlinarith

/-- `lem:app-pl-cutoff`, part (iii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[Cutoff estimates]\label{lem:app-pl-cutoff}
Let $0<\alpha\le1$, $c_N=1$, and let $i\to\infty$ with $x=i/N\to0$. Put $\nu\defeq1$ for
$\alpha<1$ and $\nu\defeq3/2$ for $\alpha=1$, and
\[
T\defeq\log(x^{-\alpha})\ (\alpha<1),\quad T\defeq\log(1/x)\ (\alpha=1),\qquad
W\defeq\frac{\sqrt{\mu_i/(\gamma\sw2)}}{a_N}=\sw2^{-1/2}e^{(T-\log\gamma)/2}.
\]
Then $\Psi_\alpha(x)\sim dT^\nu$ with $d$ of \cref{eqn:app-pl-icd}, and for fixed $M$:
\begin{enumerate}[label=(\roman*)]
\item if $W/(\log\gamma)^\nu\to z\in(0,\infty)$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim d(\log\gamma)^\nu\sim\Psi_\alpha(x)$;
\item if $W/(\log\gamma)^\nu\to\infty$, then $\Psi_\alpha(x)+\Psi_\alpha^{[M/\gamma]}(x)=o(W)$;
\item if $T\le\log\gamma+C_1\log\log\gamma$ for a constant $C_1$, then $\Psi_\alpha^{[M/\gamma]}(x)\sim\Psi_\alpha(x)$;
this applies when $W/(\log\gamma)^\nu\to0$, and then $W=o(\Psi_\alpha(x))$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_pl_cutoff_iii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (hc1 : ∀ n, c n = 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    (∀ M : ℝ, 0 < M → ∀ C1 : ℝ,
      (∀ᶠ n in atTop, cutT α (rowNum (i n) / (N n : ℝ)) ≤
        Real.log (gammaOf (N n) (B n)) + C1 * Real.log (Real.log (gammaOf (N n) (B n)))) →
      IsEquivalent atTop (fun n => psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
        (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))) ∧
    (Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
        Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 0) →
      (∃ C1 : ℝ, ∀ᶠ n in atTop, cutT α (rowNum (i n) / (N n : ℝ)) ≤
        Real.log (gammaOf (N n) (B n)) + C1 * Real.log (Real.log (gammaOf (N n) (B n)))) ∧
      IsLittleO atTop (fun n => cutW β α (c n) (N n) (B n) (i n))
        (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  have hxp : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Ioc (0 : ℝ) 1 := by
    intro n
    have hN : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨div_pos (pg6p3_row_pos _) hN, (div_le_one hN).2 (pg6p3_row_le _)⟩
  have hWp : ∀ n, 0 < cutW β α (c n) (N n) (B n) (i n) := fun n =>
    pg6p3_W_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) _
  have hL := Real.tendsto_log_atTop.comp hreg.hγ
  have hT := fun n => pg6p3_T_logW hα (hreg.hcpos n) hreg.hβ0 hreg.hβ1
    (hreg.hNpos n) (hreg.hBpos n) (i n)
  constructor
  · intro M hM C1 hbound
    have hcut := pg6p3_cutoff hreg.hα hα hx hxp hL hM hbound
    exact hcut.congr_left (Eventually.of_forall (fun n => by
      change psiRes α (M * Real.exp (-Real.log (gammaOf (N n) (B n)))) _ = _
      rw [pg6p3_gamma_exp (hreg.hNpos n) (hreg.hBpos n)]))
  · intro hW
    have hν : 0 < cutNu α := by unfold cutNu; split_ifs <;> norm_num
    have hnum := pg6p3_smallW hν hL (pg6p3_T_top hreg.hα hα hx (fun n => (hxp n).1)) hWp hW hT
    refine ⟨hnum.1, ?_⟩
    exact (hnum.2.const_mul_right (pg6p3_d_pos hα).ne').trans_isBigO
      (lem_app_pl_cutoff_pre hreg hα hc1 i hi hx).isBigO_symm

/-! ### P-G.6.P4 helpers: the continuum change of variables -/

private lemma pg6p4_wseq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => ?_, ?_, ⟨0, ?_⟩⟩
  · unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · have hg : Summable (fun j : ℕ => β ^ j) := summable_geometric_of_lt_one hβ0 hβ1
    have := hg.mul_left (1 - β)
    refine this.congr (fun j => ?_)
    simp [emaW]
  · unfold emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0 : ℝ) < 1 - β).ne'

private lemma pg6p4_rW_continuousOn {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (rW (emaW β)) (Ici 0) := by
  have hFc := (lem_app_de_scalar_ii (pg6p4_wseq hβ0 hβ1)).2.2.1
  exact continuousOn_id.mul hFc

private lemma pg6p4_rW_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (rW (emaW β)) atTop atTop := by
  have hT := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    unfold emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  rw [hset, Set.Infinite.encard_eq Set.infinite_univ, ENat.toENNReal_top] at hT
  refine tendsto_atTop.2 (fun K => ?_)
  filter_upwards [hT.eventually_const_lt ENNReal.ofReal_lt_top] with q hq
  exact ((ENNReal.ofReal_lt_ofReal_iff').1 hq).1.le

private lemma pg6p4_rW_surj {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ q ∈ Ioi (0 : ℝ), rW (emaW β) q = m := by
  have hcont := pg6p4_rW_continuousOn hβ0.le hβ1
  have htop := pg6p4_rW_atTop hβ0 hβ1
  have hr0 : rW (emaW β) 0 = 0 :=
    (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.1
  obtain ⟨b, hmb, hb0⟩ := ((htop.eventually_gt_atTop m).and (eventually_gt_atTop (0 : ℝ))).exists
  obtain ⟨q, hq, hqm⟩ := intermediate_value_Icc hb0.le
    (hcont.mono Icc_subset_Ici_self) (show m ∈ Icc (rW (emaW β) 0) (rW (emaW β) b) by
      rw [hr0]
      exact ⟨hm.le, hmb.le⟩)
  have hq0 : 0 < q := by
    rcases hq.1.eq_or_lt with heq | hlt
    · rw [← heq, hr0] at hqm
      linarith
    · exact hlt
  exact ⟨q, hq0, hqm⟩

private lemma pg6p4_Qm_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex := pg6p4_rW_surj hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg6p4_rW_image {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    rW (emaW β) '' Ioi (0 : ℝ) = Ioi 0 := by
  ext m
  constructor
  · rintro ⟨q, hq, rfl⟩
    have hmono := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1
    have hr0 := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.1
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq
    rwa [hr0] at this
  · intro hm
    exact pg6p4_rW_surj hβ0 hβ1 hm

private lemma pg6p4_E_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨hQ, -⟩ := pg6p4_Qm_spec hβ0 hβ1 hm
  obtain ⟨-, -, -, hd, hdp, -⟩ := lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)
  unfold Efun
  rw [(hd _ hQ).deriv]
  exact mul_pos hQ (hdp _ hQ)

private lemma pg6p4_Lw_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 < Lw (emaW β) q := by
  have hw := pg6p4_wseq hβ0.le hβ1
  have hwn : ∀ j, 0 ≤ emaW β j := hw.1
  have hwp : ∀ j, 0 < emaW β j := fun j => by
    unfold emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  obtain ⟨-, -, hJ, -⟩ := lem_app_de_scalar_i
  have hJq : ∀ j, 0 < emaW β j * J (emaW β j ^ 2 * q) := fun j =>
    mul_pos (hwp j) (hJ _ (mul_nonneg (sq_nonneg _) hq)).1
  have hsum : Summable (fun j => emaW β j * J (emaW β j ^ 2 * q)) := by
    refine Summable.of_nonneg_of_le (fun j => (hJq j).le) (fun j => ?_) hw.2.1
    calc
      emaW β j * J (emaW β j ^ 2 * q) ≤ emaW β j * 1 :=
        mul_le_mul_of_nonneg_left (hJ _ (mul_nonneg (sq_nonneg _) hq)).2 (hwn j)
      _ = emaW β j := mul_one _
  exact hsum.tsum_pos (fun j => (hJq j).le) 0 (hJq 0)

private lemma pg6p4_integrand_pos {α β y q : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hy : 0 < y) (hq : 0 < q) :
    0 < Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
      (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
      (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q := by
  have hmono := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1
  have hr0 := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.1
  have hr : 0 < rW (emaW β) q := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq
    rwa [hr0] at this
  have hd0 := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1 q hq
  have hd := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.1 q hq
  have hdr : 0 < deriv (rW (emaW β)) q := by simpa [hd.deriv] using hd0
  have hL := pg6p4_Lw_pos hβ0 hβ1 hq.le
  have hra : 0 < rW (emaW β) q ^ α := Real.rpow_pos_of_pos hr α
  have hrn : 0 < rW (emaW β) q ^ (-(α + 1) / 2) := Real.rpow_pos_of_pos hr _
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  positivity

private lemma pg6p4_Qm_rW {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 < q) :
    Qm β (rW (emaW β) q) = q := by
  have hmono := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1
  have hr0 := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.1
  have hrq : 0 < rW (emaW β) q := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq
    rwa [hr0] at this
  obtain ⟨hQ, hQr⟩ := pg6p4_Qm_spec hβ0 hβ1 hrq
  exact hmono.injOn hQ.le hq.le hQr

private lemma pg6p4_change_point {α β y q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hq : 0 < q) :
    |deriv (rW (emaW β)) q| •
        (Real.sqrt (Qm β (rW (emaW β) q)) * Lw (emaW β) (Qm β (rW (emaW β) q)) /
          Efun β (rW (emaW β) q) *
          rW (emaW β) q ^ (-(α + 1) / 2) *
          (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
          (1 + (α - 1) * Efun β (rW (emaW β) q) / rW (emaW β) q)) =
      Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
          (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
          (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q := by
  have hd := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.1 q hq
  have hdp := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1 q hq
  have hq0 := hq.ne'
  have hd0 : deriv (rW (emaW β)) q ≠ 0 := by
    rw [hd.deriv]
    exact hdp.ne'
  have hrq : 0 < rW (emaW β) q := by
    have hmono := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1
    have hr0 := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.1
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq.le) hq
    rwa [hr0] at this
  rw [pg6p4_Qm_rW hβ0 hβ1 hq, abs_of_pos (by simpa [hd.deriv] using hdp)]
  unfold Efun
  rw [pg6p4_Qm_rW hβ0 hβ1 hq]
  simp only [smul_eq_mul]
  field_simp [hd0]

private lemma pg6p4_change_integral {α β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hint : IntegrableOn (fun m : ℝ =>
      Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m *
        m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
        (1 + (α - 1) * Efun β m / m)) (Ioi 0)) :
    IntegrableOn (fun q : ℝ =>
      Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
        (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
        (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) (Ioi 0) ∧
      profPhi α β y = 1 / Real.pi * ∫ m in Ioi (0 : ℝ),
        Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m *
          m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
          (1 + (α - 1) * Efun β m / m) := by
  let H : ℝ → ℝ := fun m =>
    Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m *
      m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
      (1 + (α - 1) * Efun β m / m)
  have hderiv : ∀ q ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (rW (emaW β)) (deriv (rW (emaW β)) q) (Ioi 0) q := by
    intro q hq
    have hd := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.1 q hq
    exact hd.hasDerivWithinAt.congr_deriv hd.deriv.symm
  have hinj : Set.InjOn (rW (emaW β)) (Ioi (0 : ℝ)) :=
    (((lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1).injOn).mono Ioi_subset_Ici_self
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hderiv hinj H
  rw [pg6p4_rW_image hβ0 hβ1] at hiff
  have htrans : IntegrableOn (fun q : ℝ => |deriv (rW (emaW β)) q| • H (rW (emaW β) q))
      (Ioi 0) := hiff.1 hint
  have hpoint : ∀ q ∈ Ioi (0 : ℝ), |deriv (rW (emaW β)) q| • H (rW (emaW β) q) =
      Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
        (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
        (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q := by
    intro q hq
    exact pg6p4_change_point hβ0 hβ1 hq
  have hqint := htrans.congr_fun hpoint measurableSet_Ioi
  refine ⟨hqint, ?_⟩
  have hval := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj H
  rw [pg6p4_rW_image hβ0 hβ1] at hval
  unfold profPhi
  congr 1
  calc
    ∫ q in Ioi (0 : ℝ),
        Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
          (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
          (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q =
      ∫ q in Ioi (0 : ℝ), |deriv (rW (emaW β)) q| • H (rW (emaW β) q) :=
        setIntegral_congr_fun measurableSet_Ioi (fun q hq => (hpoint q hq).symm)
    _ = ∫ m in Ioi (0 : ℝ), H m := hval.symm

private lemma pg6p4_profPhi_pos_of_integrable {α β y : ℝ} (hα : 1 < α)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y)
    (hint : IntegrableOn (fun q : ℝ =>
      Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
        (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
        (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) (Ioi 0)) :
    0 < profPhi α β y := by
  unfold profPhi
  refine mul_pos (by positivity) ?_
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun q : ℝ =>
      Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
        (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
        (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) :=
    ae_restrict_of_forall_mem measurableSet_Ioi (fun q hq =>
      (pg6p4_integrand_pos hα hβ0 hβ1 hy hq).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hnn hint]
  have hpos : (0 : ENNReal) < volume (Ioi (0 : ℝ)) := by
    rw [Real.volume_Ioi]
    exact ENNReal.zero_lt_top
  exact lt_of_lt_of_le hpos (measure_mono (fun q hq =>
    ⟨Function.mem_support.2 (pg6p4_integrand_pos hα hβ0 hβ1 hy hq).ne', hq⟩))

private lemma pg6p4_theta_bounds {α β m : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hm : 0 < m) :
    1 ≤ 1 + (α - 1) * Efun β m / m ∧ 1 + (α - 1) * Efun β m / m ≤ α := by
  have hE0 := (pg6p4_E_pos hβ0 hβ1 hm).le
  have hE1 := lem_app_pl_weights_ii_E hβ0 hβ1 m hm
  have hdiv0 : 0 ≤ Efun β m / m := div_nonneg hE0 hm.le
  have hdiv1 : Efun β m / m ≤ 1 := (div_le_one hm).2 hE1
  have hp0 : 0 ≤ (α - 1) * (Efun β m / m) :=
    mul_nonneg (by linarith) hdiv0
  have hp1 : (α - 1) * (Efun β m / m) ≤ α - 1 := by
    simpa using mul_le_mul_of_nonneg_left hdiv1 (by linarith : 0 ≤ α - 1)
  rw [mul_div_assoc]
  exact ⟨by linarith, by linarith⟩

private lemma pg6p4_frac_bounds {α y m : ℝ} (hα : 0 < α) (hy : 0 < y) (hm : 0 < m) :
    0 < y * m ^ α / (1 + y * m ^ α) ∧
      y * m ^ α / (1 + y * m ^ α) ≤ 1 ∧
      y * m ^ α / (1 + y * m ^ α) ≤ y * m ^ α := by
  have hma : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hprod : 0 < y * m ^ α := mul_pos hy hma
  constructor
  · positivity
  constructor
  · rw [div_le_one (by linarith)]
    linarith
  · rw [div_le_iff₀ (by linarith)]
    nlinarith

private lemma pg6p4_Qm_continuousAt {β m : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hm : 0 < m) : ContinuousAt (Qm β) m := by
  obtain ⟨hQ, hQr⟩ := pg6p4_Qm_spec hβ0 hβ1 hm
  have hFd := (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1
  have hf : ContDiffAt ℝ (⊤ : ℕ∞) (rW (emaW β)) (Qm β m) :=
    ((contDiffOn_id.mul hFd).mono Ioi_subset_Ici_self).contDiffAt (Ioi_mem_nhds hQ)
  have hder := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.1 (Qm β m) hQ
  have hdpos := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1 (Qm β m) hQ
  have hf' := hder.hasFDerivAt_equiv hdpos.ne'
  have hn : ((↑(⊤ : ℕ∞)) : WithTop ℕ∞) ≠ 0 := by simp
  have hgC := hf.to_localInverse hf' hn
  have hga := hf.localInverse_apply_image hf' hn
  have hR := (hf.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  rw [hQr] at hgC hga hR
  have hgpos : ∀ᶠ y in 𝓝 m, 0 < hf.localInverse hf' hn y := by
    have hcont := hgC.continuousAt
    have h0 : ContinuousAt (fun _ : ℝ => (0 : ℝ)) m := continuousAt_const
    refine h0.eventually_lt hcont ?_
    rw [hga]
    exact hQ
  have hmem : Ioi (0 : ℝ) ∈ 𝓝 m := Ioi_mem_nhds hm
  have heq : Qm β =ᶠ[𝓝 m] hf.localInverse hf' hn := by
    filter_upwards [hmem, hR, hgpos] with y hy hRy hgy
    obtain ⟨h1, h2⟩ := pg6p4_Qm_spec hβ0 hβ1 hy
    exact ((lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1.injOn h1.le hgy.le
      (h2.trans hRy.symm))
  exact hgC.continuousAt.congr_of_eventuallyEq heq

private lemma pg6p4_Aav_continuousOn {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (Aav β) (Ioi 0) := by
  intro m hm
  have hQ := pg6p4_Qm_continuousAt hβ0 hβ1 hm
  have hQpos := (pg6p4_Qm_spec hβ0 hβ1 hm).1
  have hLd := (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.2.1
  have hrD : ContDiffOn ℝ (⊤ : ℕ∞) (rW (emaW β)) (Ioi 0) :=
    ((contDiffOn_id.mul
      (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1).mono Ioi_subset_Ici_self)
  have hdr : ContinuousOn (deriv (rW (emaW β))) (Ioi 0) :=
    hrD.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
  have hE : ContinuousAt (Efun β) m := by
    unfold Efun
    have hdA := (hdr (Qm β m) hQpos).continuousAt (Ioi_mem_nhds hQpos)
    have hcomp : ContinuousAt (fun x => deriv (rW (emaW β)) (Qm β x)) m :=
      hdA.tendsto.comp hQ
    exact hQ.mul hcomp
  have hEpos := pg6p4_E_pos hβ0 hβ1 hm
  unfold Aav
  have hsQ : ContinuousAt (fun x => Real.sqrt (Qm β x)) m :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hQ
  have hLA := (hLd.continuousOn (Qm β m) hQpos.le).continuousAt (Ici_mem_nhds hQpos)
  have hLc : ContinuousAt (fun x => Lw (emaW β) (Qm β x)) m := hLA.tendsto.comp hQ
  exact ((hsQ.mul hLc).div hE hEpos.ne').continuousWithinAt

private lemma pg6p4_Lw_le_one {β q : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hq : 0 ≤ q) :
    Lw (emaW β) q ≤ 1 := by
  have hw := pg6p4_wseq hβ0.le hβ1
  have hJ := lem_app_de_scalar_i.2.2.1
  have hnn : ∀ j, 0 ≤ emaW β j * J (emaW β j ^ 2 * q) := fun j =>
    mul_nonneg (hw.1 j) (hJ _ (mul_nonneg (sq_nonneg _) hq)).1.le
  have hle : ∀ j, emaW β j * J (emaW β j ^ 2 * q) ≤ emaW β j := fun j => by
    simpa using mul_le_mul_of_nonneg_left (hJ _ (mul_nonneg (sq_nonneg _) hq)).2 (hw.1 j)
  have hs := Summable.of_nonneg_of_le hnn hle hw.2.1
  unfold Lw
  calc
    ∑' j, emaW β j * J (emaW β j ^ 2 * q) ≤ ∑' j, emaW β j := hs.tsum_le_tsum hle hw.2.1
    _ = 1 := tsum_emaW hβ0.le hβ1

private lemma pg6p4_Qm_mono {β m n : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hm : 0 < m) (hmn : m ≤ n) : Qm β m ≤ Qm β n := by
  have hn : 0 < n := hm.trans_le hmn
  obtain ⟨hQm, hrm⟩ := pg6p4_Qm_spec hβ0 hβ1 hm
  obtain ⟨hQn, hrn⟩ := pg6p4_Qm_spec hβ0 hβ1 hn
  have hmono := (lem_app_de_scalar_iii (pg6p4_wseq hβ0.le hβ1)).2.1
  rw [← hrm, ← hrn] at hmn
  exact (hmono.le_iff_le hQm.le hQn.le).1 hmn

private lemma pg6p4_Aav_upper {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧
      (∀ m : ℝ, 0 < m → m ≤ 1 → 0 ≤ Aav β m ∧ Aav β m ≤ K / m) ∧
      (∀ m : ℝ, 1 ≤ m → 0 ≤ Aav β m ∧ Aav β m ≤ C) := by
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  obtain ⟨cA, CA, hcA, hA⟩ := lem_app_pl_average_i hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)
  have hQ1 := (pg6p4_Qm_spec hβ0 hβ1 (zero_lt_one : (0 : ℝ) < 1)).1
  refine ⟨Real.sqrt (Qm β 1) / cE, max CA cA, div_pos (Real.sqrt_pos.2 hQ1) hcE,
    lt_of_lt_of_le hcA (le_max_right _ _), ?_, ?_⟩
  · intro m hm hm1
    have hQ := (pg6p4_Qm_spec hβ0 hβ1 hm).1
    have hQle := pg6p4_Qm_mono hβ0 hβ1 hm hm1
    have hLpos := pg6p4_Lw_pos hβ0 hβ1 hQ.le
    have hLle := pg6p4_Lw_le_one hβ0 hβ1 hQ.le
    have hElo : cE * m ≤ Efun β m := by simpa [min_eq_left hm1] using (hE m hm).1
    have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hm) hElo
    have hsle : Real.sqrt (Qm β m) ≤ Real.sqrt (Qm β 1) := Real.sqrt_le_sqrt hQle
    have hnum : 0 ≤ Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) :=
      mul_nonneg (Real.sqrt_nonneg _) hLpos.le
    have hnumle : Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) ≤ Real.sqrt (Qm β 1) :=
      (mul_le_mul_of_nonneg_left hLle (Real.sqrt_nonneg _)).trans (by simpa using hsle)
    unfold Aav
    refine ⟨div_nonneg hnum hEpos.le, ?_⟩
    rw [div_div]
    rw [div_le_div_iff₀ hEpos (mul_pos hcE hm)]
    exact mul_le_mul hnumle hElo (mul_pos hcE hm).le (Real.sqrt_nonneg _)
  · intro m hm
    obtain ⟨hlo, hhi⟩ := hA m hm
    exact ⟨hcA.le.trans hlo, hhi.trans (le_max_left _ _)⟩

private lemma pg6p4_m_integrable {α β y : ℝ} (hα : 1 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hy : 0 < y) :
    IntegrableOn (fun m : ℝ =>
      Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
        (1 + (α - 1) * Efun β m / m)) (Ioi 0) := by
  let H : ℝ → ℝ := fun m =>
    Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
      (1 + (α - 1) * Efun β m / m)
  obtain ⟨K, C, hK, hC, hsmall, hlarge⟩ := pg6p4_Aav_upper hβ0 hβ1
  have hHcont : ContinuousOn H (Ioi 0) := by
    intro m hm
    have hA := pg6p4_Aav_continuousOn hβ0 hβ1 m hm
    have hm0 : m ≠ 0 := hm.ne'
    have hmα : ContinuousAt (fun x : ℝ => x ^ α) m :=
      Real.continuousAt_rpow_const m α (Or.inl hm0)
    have hmneg : ContinuousAt (fun x : ℝ => x ^ (-(α + 1) / 2)) m :=
      Real.continuousAt_rpow_const m (-(α + 1) / 2) (Or.inl hm0)
    have hE : ContinuousAt (Efun β) m := by
      unfold Efun
      have hQ := pg6p4_Qm_continuousAt hβ0 hβ1 hm
      have hQpos := (pg6p4_Qm_spec hβ0 hβ1 hm).1
      have hrD : ContDiffOn ℝ (⊤ : ℕ∞) (rW (emaW β)) (Ioi 0) :=
        ((contDiffOn_id.mul
          (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1).mono Ioi_subset_Ici_self)
      have hdr := hrD.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
      have hdA := (hdr (Qm β m) hQpos).continuousAt (Ioi_mem_nhds hQpos)
      have hcomp : ContinuousAt (fun x => deriv (rW (emaW β)) (Qm β x)) m :=
        hdA.tendsto.comp hQ
      exact hQ.mul hcomp
    dsimp [H]
    have hpα : 0 < m ^ α := Real.rpow_pos_of_pos hm α
    have hpαw : ContinuousWithinAt (fun x : ℝ => x ^ α) (Ioi 0) m := hmα.continuousWithinAt
    have hnumw : ContinuousWithinAt (fun x : ℝ => y * x ^ α) (Ioi 0) m :=
      continuousWithinAt_const.mul hpαw
    have hfrac : ContinuousWithinAt (fun x : ℝ => y * x ^ α / (1 + y * x ^ α))
        (Ioi 0) m := hnumw.div (continuousWithinAt_const.add hnumw)
          (by positivity : 1 + y * m ^ α ≠ 0)
    have hEw : ContinuousWithinAt (Efun β) (Ioi 0) m := hE.continuousWithinAt
    have htheta : ContinuousWithinAt (fun x : ℝ => 1 + (α - 1) * Efun β x / x)
        (Ioi 0) m := continuousWithinAt_const.add
          ((continuousWithinAt_const.mul hEw).div continuousWithinAt_id hm.ne')
    convert ((hA.mul hmneg.continuousWithinAt).mul hfrac).mul htheta using 1 <;> ring
  have hmeas : AEStronglyMeasurable H (volume.restrict (Ioi (0 : ℝ))) :=
    hHcont.aestronglyMeasurable measurableSet_Ioi
  have hs : IntegrableOn H (Ioo (0 : ℝ) 1) := by
    have hp : -1 < (α - 3) / 2 := by linarith
    have hg : IntegrableOn (fun m : ℝ => K * y * α * m ^ ((α - 3) / 2)) (Ioo 0 1) :=
      ((intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 hp).const_mul (K * y * α)
    refine Integrable.mono' hg
      ((hHcont.mono Ioo_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioo) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with m hm
    have hm0 := hm.1
    obtain ⟨hA0, hAle⟩ := hsmall m hm0 hm.2.le
    obtain ⟨hf0, -, hfle⟩ := pg6p4_frac_bounds (α := α) (by linarith) hy hm0
    obtain ⟨ht0, htle⟩ := pg6p4_theta_bounds hα hβ0 hβ1 hm0
    have hpow : 0 ≤ m ^ (-(α + 1) / 2) := (Real.rpow_pos_of_pos hm0 _).le
    have hα0 : 0 < α := by linarith
    have hH0 : 0 ≤ H m := by
      dsimp [H]
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hH0]
    calc
      H m ≤ (K / m) * m ^ (-(α + 1) / 2) * (y * m ^ α) * α := by
        dsimp [H]
        gcongr
      _ = K * y * α * m ^ ((α - 3) / 2) := by
        rw [div_eq_mul_inv]
        calc
          K * m⁻¹ * m ^ (-(α + 1) / 2) * (y * m ^ α) * α =
              K * y * α * (m⁻¹ * m ^ (-(α + 1) / 2) * m ^ α) := by ring
          _ = K * y * α * (m ^ (-1 : ℝ) * m ^ (-(α + 1) / 2) * m ^ α) := by
            rw [Real.rpow_neg_one]
          _ = _ := by
            rw [← Real.rpow_add hm0, ← Real.rpow_add hm0]
            congr 1
            ring
  have hli : IntegrableOn H (Ioi (1 : ℝ)) := by
    have hp : -(α + 1) / 2 < -1 := by linarith
    have hg : IntegrableOn (fun m : ℝ => C * α * m ^ (-(α + 1) / 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt hp zero_lt_one).const_mul (C * α)
    refine Integrable.mono' hg
      ((hHcont.mono (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))).aestronglyMeasurable
        measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with m hm
    have hm0 : 0 < m := zero_lt_one.trans hm
    obtain ⟨hA0, hAle⟩ := hlarge m hm.le
    obtain ⟨hf0, hfle, -⟩ := pg6p4_frac_bounds (α := α) (by linarith) hy hm0
    obtain ⟨ht0, htle⟩ := pg6p4_theta_bounds hα hβ0 hβ1 hm0
    have hpow : 0 < m ^ (-(α + 1) / 2) := Real.rpow_pos_of_pos hm0 _
    have hα0 : 0 < α := by linarith
    have hH0 : 0 ≤ H m := by dsimp [H]; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hH0]
    calc
      H m ≤ C * m ^ (-(α + 1) / 2) *
          (y * m ^ α / (1 + y * m ^ α)) *
          (1 + (α - 1) * Efun β m / m) := by dsimp [H]; gcongr
      _ ≤ C * m ^ (-(α + 1) / 2) * 1 *
          (1 + (α - 1) * Efun β m / m) := by gcongr
      _ ≤ C * m ^ (-(α + 1) / 2) * 1 * α := by gcongr
      _ = C * α * m ^ (-(α + 1) / 2) := by ring
  have hl : IntegrableOn H (Ici (1 : ℝ)) :=
    (integrableOn_Ici_iff_integrableOn_Ioi' (μ := volume) (by simp)).2 hli
  rw [← Ioo_union_Ici_eq_Ioi (show (0 : ℝ) < 1 by norm_num)]
  simpa only [H] using hs.union hl

private lemma pg6p4_m_continuousOn {α β y : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hy : 0 < y) :
    ContinuousOn (fun m : ℝ =>
      Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
        (1 + (α - 1) * Efun β m / m)) (Ioi 0) := by
  intro m hm
  have hA := pg6p4_Aav_continuousOn hβ0 hβ1 m hm
  have hm0 : m ≠ 0 := hm.ne'
  have hmα : ContinuousAt (fun x : ℝ => x ^ α) m :=
    Real.continuousAt_rpow_const m α (Or.inl hm0)
  have hmneg : ContinuousAt (fun x : ℝ => x ^ (-(α + 1) / 2)) m :=
    Real.continuousAt_rpow_const m (-(α + 1) / 2) (Or.inl hm0)
  have hE : ContinuousAt (Efun β) m := by
    unfold Efun
    have hQ := pg6p4_Qm_continuousAt hβ0 hβ1 hm
    have hQpos := (pg6p4_Qm_spec hβ0 hβ1 hm).1
    have hrD : ContDiffOn ℝ (⊤ : ℕ∞) (rW (emaW β)) (Ioi 0) :=
      ((contDiffOn_id.mul
        (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1).mono Ioi_subset_Ici_self)
    have hdr := hrD.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
    have hdA := (hdr (Qm β m) hQpos).continuousAt (Ioi_mem_nhds hQpos)
    have hcomp : ContinuousAt (fun x => deriv (rW (emaW β)) (Qm β x)) m :=
      hdA.tendsto.comp hQ
    exact hQ.mul hcomp
  have hpα : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hpαw : ContinuousWithinAt (fun x : ℝ => x ^ α) (Ioi 0) m := hmα.continuousWithinAt
  have hnumw : ContinuousWithinAt (fun x : ℝ => y * x ^ α) (Ioi 0) m :=
    continuousWithinAt_const.mul hpαw
  have hfrac : ContinuousWithinAt (fun x : ℝ => y * x ^ α / (1 + y * x ^ α))
      (Ioi 0) m := hnumw.div (continuousWithinAt_const.add hnumw)
        (by positivity : 1 + y * m ^ α ≠ 0)
  have hEw : ContinuousWithinAt (Efun β) (Ioi 0) m := hE.continuousWithinAt
  have htheta : ContinuousWithinAt (fun x : ℝ => 1 + (α - 1) * Efun β x / x)
      (Ioi 0) m := continuousWithinAt_const.add
        ((continuousWithinAt_const.mul hEw).div continuousWithinAt_id hm.ne')
  convert ((hA.mul hmneg.continuousWithinAt).mul hfrac).mul htheta using 1 <;> ring

private lemma pg6p4_frac_mono {α y Y m : ℝ} (hm : 0 < m) (hy : 0 < y) (hyY : y ≤ Y) :
    y * m ^ α / (1 + y * m ^ α) ≤ Y * m ^ α / (1 + Y * m ^ α) := by
  have hp := Real.rpow_pos_of_pos hm α
  have hy0 := mul_pos hy hp
  have hY0 : 0 < Y * m ^ α := mul_pos (hy.trans_le hyY) hp
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- `lem:app-pl-super`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[The supercritical drift profile]\label{lem:app-pl-super}
Let $\alpha>1$ and $p_\alpha\defeq(\alpha-1)/(2\alpha)$. The function $\Phi_{\alpha,\bmom}$ of
\cref{eqn:app-pl-Phi} is finite, positive and continuous on $(0,\infty)$, and
\[
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\quad(y\to\infty),\qquad \Phi_{\alpha,\bmom}(y)\sim d_\alpha y^{p_\alpha}\quad(y\downarrow0).
\]
Under \cref{assum:app-pl-regime}, for every row sequence $i\to\infty$ with $i/N\to0$,
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{b_N}\sim\Phi_{\alpha,\bmom}\big((i_{\mathrm c}/i)^\alpha\big).
\]
\end{lemma}
-/
theorem lem_app_pl_super_i {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (profPhi α β) (Ioi 0) ∧
      ∀ y ∈ Ioi (0 : ℝ), IntegrableOn (fun q : ℝ =>
        Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
          (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
          (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) (Ioi 0) ∧
        0 < profPhi α β y := by
  let F : ℝ → ℝ → ℝ := fun y m =>
    Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
      (1 + (α - 1) * Efun β m / m)
  have hmint : ∀ y ∈ Ioi (0 : ℝ), IntegrableOn (F y) (Ioi 0) := by
    intro y hy
    exact pg6p4_m_integrable hα hβ0 hβ1 hy
  have hchange : ∀ y ∈ Ioi (0 : ℝ),
      IntegrableOn (fun q : ℝ =>
        Real.sqrt q * Lw (emaW β) q * rW (emaW β) q ^ (-(α + 1) / 2) *
          (y * rW (emaW β) q ^ α / (1 + y * rW (emaW β) q ^ α)) *
          (1 + (α - 1) * q * deriv (rW (emaW β)) q / rW (emaW β) q) / q) (Ioi 0) ∧
        profPhi α β y = 1 / Real.pi * ∫ m in Ioi (0 : ℝ), F y m := by
    intro y hy
    simpa only [F, Aav] using pg6p4_change_integral (α := α) (β := β) (y := y)
      hβ0 hβ1 (by simpa only [F, Aav] using hmint y hy)
  have hcont : ContinuousOn (profPhi α β) (Ioi 0) := by
    intro y hy
    let Y := y + 1
    have hY : 0 < Y := by dsimp [Y]; exact add_pos hy one_pos
    have hdom : Integrable (F Y) (volume.restrict (Ioi (0 : ℝ))) :=
      pg6p4_m_integrable hα hβ0 hβ1 hY
    have hI : ContinuousAt (fun z : ℝ => ∫ m, F z m ∂(volume.restrict (Ioi (0 : ℝ)))) y := by
      apply continuousAt_of_dominated (bound := F Y)
      · filter_upwards [Ioo_mem_nhds hy (show y < Y by simp [Y])] with z hz
        exact (pg6p4_m_continuousOn hβ0 hβ1 hz.1).aestronglyMeasurable measurableSet_Ioi
      · filter_upwards [Ioo_mem_nhds hy (show y < Y by simp [Y])] with z hz
        apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro m hm
        obtain ⟨K, C, hK, hC, hsmall, hlarge⟩ := pg6p4_Aav_upper hβ0 hβ1
        have hAm : 0 ≤ Aav β m := by
          rcases le_total m 1 with hm1 | hm1
          · exact (hsmall m hm hm1).1
          · exact (hlarge m hm1).1
        have hp : 0 < m ^ (-(α + 1) / 2) := Real.rpow_pos_of_pos hm _
        have hfz := pg6p4_frac_bounds (by linarith : 0 < α) hz.1 hm
        have hfY := pg6p4_frac_bounds (by linarith : 0 < α) hY hm
        have hmono := pg6p4_frac_mono (α := α) hm hz.1 hz.2.le
        have ht := pg6p4_theta_bounds hα hβ0 hβ1 hm
        have hFz : 0 ≤ F z m := by
          dsimp [F]
          exact mul_nonneg (mul_nonneg (mul_nonneg hAm hp.le) hfz.1.le) (zero_le_one.trans ht.1)
        have hFY : 0 ≤ F Y m := by
          dsimp [F]
          exact mul_nonneg (mul_nonneg (mul_nonneg hAm hp.le) hfY.1.le) (zero_le_one.trans ht.1)
        rw [Real.norm_eq_abs, abs_of_nonneg hFz]
        dsimp [F]
        have hpre : 0 ≤ Aav β m * m ^ (-(α + 1) / 2) := mul_nonneg hAm hp.le
        have htheta0 : 0 ≤ 1 + (α - 1) * Efun β m / m := zero_le_one.trans ht.1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hpre) htheta0
      · exact hdom
      · apply ae_restrict_of_forall_mem measurableSet_Ioi
        intro m hm
        dsimp [F]
        have hp := Real.rpow_pos_of_pos hm α
        have hden : 1 + y * m ^ α ≠ 0 := by nlinarith [mul_pos hy hp]
        fun_prop
    have hG : ContinuousAt (fun z : ℝ => 1 / Real.pi * ∫ m in Ioi (0 : ℝ), F z m) y :=
      continuousAt_const.mul hI
    have heq : profPhi α β =ᶠ[𝓝 y]
        (fun z : ℝ => 1 / Real.pi * ∫ m in Ioi (0 : ℝ), F z m) := by
      filter_upwards [Ioi_mem_nhds hy] with z hz
      exact (hchange z hz).2
    exact hG.congr_of_eventuallyEq heq |>.continuousWithinAt
  refine ⟨hcont, fun y hy => ?_⟩
  have hc := hchange y hy
  exact ⟨hc.1, pg6p4_profPhi_pos_of_integrable hα hβ0 hβ1 hy hc.1⟩

/-! ### P-G.6.P4 helpers (continued): Beta integrals -/

private lemma pg6p5_beta {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hsα : s < α) :
    IntegrableOn (fun w : ℝ => w ^ (s - 1) / (1 + w ^ α)) (Ioi 0) ∧
    ∫ w in Ioi (0:ℝ), w ^ (s - 1) / (1 + w ^ α) = Real.pi / (α * Real.sin (Real.pi * s / α)) := by
  have hne : α ≠ 0 := hα.ne'
  have ha : 0 < s / α := by positivity
  have hb : 0 < 1 - s / α := by
    have : s / α < 1 := by rw [div_lt_one hα]; exact hsα
    linarith
  have hb' := Muon.Foundations.betaHalfLine ha hb
  rw [show (s / α + (1 - s / α)) = (1:ℝ) by ring] at hb'
  simp only [Real.rpow_neg_one] at hb'
  rw [Real.Gamma_one, div_one, Real.Gamma_mul_Gamma_one_sub] at hb'
  have hcv : ∫ x in Ioi (0:ℝ), (α * x ^ (α - 1)) • (((x ^ α) ^ (s / α - 1)) * (1 + x ^ α)⁻¹)
      = ∫ y in Ioi (0:ℝ), y ^ (s / α - 1) * (1 + y)⁻¹ :=
    integral_comp_rpow_Ioi_of_pos
      (g := fun y : ℝ => y ^ (s / α - 1) * (1 + y)⁻¹) hα
  have hpt : ∀ x ∈ Ioi (0:ℝ), (α * x ^ (α - 1)) • (((x ^ α) ^ (s / α - 1)) * (1 + x ^ α)⁻¹)
      = α * (x ^ (s - 1) / (1 + x ^ α)) := by
    intro x hx
    have hx' : (0:ℝ) < x := hx
    have e1 : (x ^ α) ^ (s / α - 1) = x ^ (s - α) := by
      rw [← Real.rpow_mul hx'.le]
      congr 1
      field_simp
    have e2 : x ^ (α - 1) * x ^ (s - α) = x ^ (s - 1) := by
      rw [← Real.rpow_add hx']
      congr 1
      ring
    rw [smul_eq_mul, e1]
    rw [show α * x ^ (α - 1) * (x ^ (s - α) * (1 + x ^ α)⁻¹)
      = α * (x ^ (α - 1) * x ^ (s - α)) * (1 + x ^ α)⁻¹ by ring, e2]
    ring
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Ioi hpt
  rw [hcv, integral_const_mul] at hcongr
  rw [hb'] at hcongr
  have hsin : 0 < Real.sin (Real.pi * s / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ hα]; nlinarith [Real.pi_pos]
  have hsin' : Real.sin (Real.pi * (s / α)) = Real.sin (Real.pi * s / α) := by
    rw [mul_div_assoc]
  rw [hsin'] at hcongr
  have hJ : ∫ w in Ioi (0:ℝ), w ^ (s - 1) / (1 + w ^ α) = Real.pi / (α * Real.sin (Real.pi * s / α)) := by
    field_simp at hcongr ⊢
    linarith
  refine ⟨?_, hJ⟩
  by_contra hn
  rw [integral_undef hn] at hJ
  have : 0 < Real.pi / (α * Real.sin (Real.pi * s / α)) := by positivity
  linarith

/-- the scaled profile `g(w) = w^{(α-1)/2}/(1+w^α)` -/
private def pg6p5_g (α w : ℝ) : ℝ := w ^ ((α - 1) / 2) / (1 + w ^ α)

private lemma pg6p5_g_hasDeriv {α w : ℝ} (hw : 0 < w) :
    HasDerivAt (pg6p5_g α)
      (((α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) - w ^ ((α - 1) / 2) * (α * w ^ (α - 1))) /
        (1 + w ^ α) ^ 2) w := by
  have h1 := Real.hasDerivAt_rpow_const (x := w) (p := (α - 1) / 2) (Or.inl hw.ne')
  have h2 := Real.hasDerivAt_rpow_const (x := w) (p := α) (Or.inl hw.ne')
  have h3 := h2.const_add (1:ℝ)
  have hne : (1 + w ^ α) ≠ 0 := by have := Real.rpow_pos_of_pos hw α; linarith
  exact h1.div h3 hne

private lemma pg6p5_g_deriv_bound {α w : ℝ} (hα : 1 < α) (hw : 0 < w) :
    |deriv (pg6p5_g α) w| ≤ (3 * α - 1) / 2 * (w ^ ((α - 1) / 2 - 1) / (1 + w ^ α)) := by
  rw [(pg6p5_g_hasDeriv hw).deriv]
  have hp : 0 < w ^ α := Real.rpow_pos_of_pos hw α
  have hq : 0 < w ^ ((α - 1) / 2 - 1) := Real.rpow_pos_of_pos hw _
  have hr : 0 < w ^ ((α - 1) / 2) := Real.rpow_pos_of_pos hw _
  have hs : 0 < w ^ (α - 1) := Real.rpow_pos_of_pos hw _
  -- w^{(α-1)/2} * w^{α-1} = w^{(α-1)/2-1} * w^α
  have hrel : w ^ ((α - 1) / 2) * w ^ (α - 1) = w ^ ((α - 1) / 2 - 1) * w ^ α := by
    rw [← Real.rpow_add hw, ← Real.rpow_add hw]; congr 1; ring
  have hD : 0 < 1 + w ^ α := by linarith
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < (1 + w ^ α) ^ 2)]
  rw [div_le_iff₀ (by positivity)]
  have key : |(α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) - w ^ ((α - 1) / 2) * (α * w ^ (α - 1))|
      ≤ (α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) + α * (w ^ ((α - 1) / 2 - 1) * w ^ α) := by
    have e : w ^ ((α - 1) / 2) * (α * w ^ (α - 1)) = α * (w ^ ((α - 1) / 2 - 1) * w ^ α) := by
      rw [← hrel]; ring
    rw [e]
    have h0 : 0 ≤ (α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) := by
      have : 0 ≤ (α - 1) / 2 := by linarith
      positivity
    have h1 : 0 ≤ α * (w ^ ((α - 1) / 2 - 1) * w ^ α) := by positivity
    rw [abs_le]; constructor <;> linarith
  refine key.trans ?_
  have : w ^ α ≤ 1 + w ^ α := by linarith
  have h2 : α * (w ^ ((α - 1) / 2 - 1) * w ^ α) ≤ α * (w ^ ((α - 1) / 2 - 1) * (1 + w ^ α)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this hq.le) (by linarith)
  have h3 : (3 * α - 1) / 2 * (w ^ ((α - 1) / 2 - 1) / (1 + w ^ α)) * (1 + w ^ α) ^ 2
      = (3 * α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) := by
    field_simp
  rw [h3]
  nlinarith

private lemma pg6p5_h_int {α : ℝ} (hα : 1 < α) :
    IntegrableOn (fun w : ℝ => w ^ ((α - 1) / 2 - 1) / (1 + w ^ α)) (Ioi 0) := by
  have := (pg6p5_beta (α := α) (s := (α - 1) / 2) (by linarith) (by linarith) (by linarith)).1
  exact this

private lemma pg6p5_g_cont {α : ℝ} : ContinuousOn (pg6p5_g α) (Ioi 0) := fun w hw =>
  (pg6p5_g_hasDeriv hw).continuousAt.continuousWithinAt

private lemma pg6p5_dg_int {α : ℝ} (hα : 1 < α) :
    IntegrableOn (fun w : ℝ => |deriv (pg6p5_g α) w|) (Ioi 0) := by
  refine Integrable.mono' ((pg6p5_h_int hα).const_mul ((3 * α - 1) / 2)) ?_ ?_
  · have hd : ContinuousOn (deriv (pg6p5_g α)) (Ioi 0) := by
      have hc : ContinuousOn (fun w : ℝ => ((α - 1) / 2 * w ^ ((α - 1) / 2 - 1) * (1 + w ^ α) - w ^ ((α - 1) / 2) * (α * w ^ (α - 1))) / (1 + w ^ α) ^ 2) (Ioi 0) := by
        apply ContinuousOn.div
        · apply ContinuousOn.sub
          · exact (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw)))).mul (continuousOn_const.add (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw))))
          · exact (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw))).mul (continuousOn_const.mul (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw))))
        · exact (continuousOn_const.add (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw)))).pow 2
        · intro w hw
          have := Real.rpow_pos_of_pos (show (0:ℝ) < w from hw) α
          positivity
      exact hc.congr (fun w hw => (pg6p5_g_hasDeriv hw).deriv)
    exact (hd.abs).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    rw [Real.norm_eq_abs, abs_abs]
    exact pg6p5_g_deriv_bound hα hw

/-- the weight `W_y(m) = m^{-(α+1)/2} y m^α/(1+y m^α)` -/
private def pg6p5_W (α y m : ℝ) : ℝ := m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α))

private lemma pg6p5_W_scale {α y m : ℝ} (hα : 0 < α) (hy : 0 < y) (hm : 0 < m) :
    pg6p5_W α y m = y ^ ((α + 1) / (2 * α)) * pg6p5_g α (y ^ (1 / α) * m) := by
  unfold pg6p5_W pg6p5_g
  have ht : 0 < y ^ (1 / α) := Real.rpow_pos_of_pos hy _
  have htα : (y ^ (1 / α)) ^ α = y := by
    rw [← Real.rpow_mul hy.le, one_div_mul_cancel hα.ne', Real.rpow_one]
  simp only [Real.mul_rpow ht.le hm.le, htα]
  have e1 : y ^ ((α + 1) / (2 * α)) * (y ^ (1 / α)) ^ ((α - 1) / 2) = y := by
    rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy]
    conv_rhs => rw [← Real.rpow_one y]
    congr 1
    field_simp
    ring
  have e2 : m ^ ((α - 1) / 2) = m ^ (-(α + 1) / 2) * m ^ α := by
    rw [← Real.rpow_add hm]; congr 1; ring
  have hD : 0 < 1 + y * m ^ α := by have := Real.rpow_pos_of_pos hm α; positivity
  calc m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α))
      = y * (m ^ (-(α + 1) / 2) * m ^ α) / (1 + y * m ^ α) := by ring
    _ = (y ^ ((α + 1) / (2 * α)) * (y ^ (1 / α)) ^ ((α - 1) / 2)) * m ^ ((α - 1) / 2) / (1 + y * m ^ α) := by
        rw [e1, e2]
    _ = _ := by ring

private lemma pg6p5_W_int {α y : ℝ} (hα : 1 < α) (hy : 0 < y) :
    IntegrableOn (pg6p5_W α y) (Ioi 0) ∧
      ∫ m in Ioi (0:ℝ), pg6p5_W α y m =
        y ^ ((α - 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), pg6p5_g α w := by
  have hα0 : 0 < α := by linarith
  have ht : 0 < y ^ (1 / α) := Real.rpow_pos_of_pos hy _
  have hgint : IntegrableOn (pg6p5_g α) (Ioi 0) := by
    have := (pg6p5_beta (α := α) (s := (α + 1) / 2) hα0 (by linarith) (by linarith)).1
    refine this.congr_fun (fun w _ => ?_) measurableSet_Ioi
    unfold pg6p5_g; congr 2; ring
  have hcongr : ∀ m ∈ Ioi (0:ℝ), pg6p5_W α y m =
      y ^ ((α + 1) / (2 * α)) * pg6p5_g α (y ^ (1 / α) * m) := fun m hm =>
    pg6p5_W_scale hα0 hy hm
  have hint1 : IntegrableOn (fun m => pg6p5_g α (y ^ (1 / α) * m)) (Ioi 0) := by
    rw [integrableOn_Ioi_comp_mul_left_iff (pg6p5_g α) 0 ht]
    simpa using hgint
  have hint2 : IntegrableOn (fun m => y ^ ((α + 1) / (2 * α)) * pg6p5_g α (y ^ (1 / α) * m)) (Ioi 0) :=
    hint1.const_mul _
  refine ⟨hint2.congr_fun (fun m hm => (hcongr m hm).symm) measurableSet_Ioi, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul,
    integral_comp_mul_left_Ioi (pg6p5_g α) 0 ht]
  simp only [mul_zero, smul_eq_mul]
  rw [← mul_assoc]
  congr 1
  rw [← Real.rpow_neg hy.le, ← Real.rpow_add hy]
  congr 1
  field_simp
  ring

private lemma pg6p5_W_contDiffOn {α y : ℝ} (hy : 0 < y) :
    ContDiffOn ℝ 1 (pg6p5_W α y) (Ioi 0) := by
  unfold pg6p5_W
  have hm : ContDiffOn ℝ 1 (fun m : ℝ => m ^ (-(α + 1) / 2)) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun m hm => ne_of_gt hm)
  have hp : ContDiffOn ℝ 1 (fun m : ℝ => m ^ α) (Ioi 0) :=
    contDiffOn_id.rpow_const_of_ne (fun m hm => ne_of_gt hm)
  refine hm.mul ?_
  refine (contDiffOn_const.mul hp).div (contDiffOn_const.add (contDiffOn_const.mul hp)) ?_
  intro m hm'
  have := Real.rpow_pos_of_pos (show (0:ℝ) < m from hm') α
  positivity

private lemma pg6p5_W_hasDeriv {α y m : ℝ} (hα : 0 < α) (hy : 0 < y) (hm : 0 < m) :
    HasDerivAt (pg6p5_W α y)
      (y ^ ((α + 1) / (2 * α)) * (deriv (pg6p5_g α) (y ^ (1 / α) * m) * y ^ (1 / α))) m := by
  have ht : 0 < y ^ (1 / α) := Real.rpow_pos_of_pos hy _
  have hg := (pg6p5_g_hasDeriv (α := α) (mul_pos ht hm)).deriv ▸ pg6p5_g_hasDeriv (α := α) (mul_pos ht hm)
  have h1 : HasDerivAt (fun x : ℝ => y ^ (1 / α) * x) (y ^ (1 / α)) m := by
    simpa using (hasDerivAt_id m).const_mul (y ^ (1 / α))
  have h2 := (hg.comp m h1).const_mul (y ^ ((α + 1) / (2 * α)))
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hm] with x hx
  exact pg6p5_W_scale hα hy hx

private lemma pg6p5_W_var {α y a c : ℝ} (hα : 1 < α) (hy : 0 < y) (ha : 0 < a) (hac : a ≤ c) :
    ∫ m in a..c, |deriv (pg6p5_W α y) m| ≤
      y ^ ((α + 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), |deriv (pg6p5_g α) w| := by
  have hα0 : 0 < α := by linarith
  have ht : 0 < y ^ (1 / α) := Real.rpow_pos_of_pos hy _
  have hpq : 0 < y ^ ((α + 1) / (2 * α)) := Real.rpow_pos_of_pos hy _
  have hcongr : ∀ m ∈ Set.uIcc a c, |deriv (pg6p5_W α y) m| =
      y ^ ((α + 1) / (2 * α)) * (y ^ (1 / α) * |deriv (pg6p5_g α) (y ^ (1 / α) * m)|) := by
    intro m hm
    rw [Set.uIcc_of_le hac] at hm
    have hm0 : 0 < m := ha.trans_le hm.1
    rw [(pg6p5_W_hasDeriv hα0 hy hm0).deriv, abs_mul, abs_mul, abs_of_pos hpq, abs_of_pos ht]
    ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  refine mul_le_mul_of_nonneg_left ?_ hpq.le
  have := intervalIntegral.integral_comp_mul_left (a := a) (b := c)
    (fun w => |deriv (pg6p5_g α) w|) ht.ne'
  have h2 : ∫ m in a..c, y ^ (1 / α) * |deriv (pg6p5_g α) (y ^ (1 / α) * m)| =
      ∫ w in (y ^ (1 / α) * a)..(y ^ (1 / α) * c), |deriv (pg6p5_g α) w| := by
    rw [intervalIntegral.integral_const_mul, this, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul]
  rw [h2, intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hac ht.le)]
  refine setIntegral_mono_set (pg6p5_dg_int hα) ?_ ?_
  · exact Filter.Eventually.of_forall (fun w => abs_nonneg _)
  · refine Filter.Eventually.of_forall ?_
    intro w hw
    exact lt_of_lt_of_le (mul_pos ht ha) hw.1.le

private lemma pg6p5_frac_sqrt {x : ℝ} (hx : 0 ≤ x) : x / (1 + x) ≤ Real.sqrt x := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx
  rw [div_le_iff₀ (by linarith)]
  set r := Real.sqrt x
  rw [← hsq]
  nlinarith [mul_nonneg hs (sq_nonneg (r - 1 / 2))]

private lemma pg6p5_W_bounds {α y m : ℝ} (hy : 0 < y) (hm : 0 < m) :
    0 ≤ pg6p5_W α y m ∧ pg6p5_W α y m ≤ y * m ^ ((α - 1) / 2) ∧
      pg6p5_W α y m ≤ m ^ (-(α + 1) / 2) ∧
      pg6p5_W α y m ≤ y ^ (1 / 2 : ℝ) * m ^ (-(1 : ℝ) / 2) := by
  unfold pg6p5_W
  have hp : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hq : 0 < m ^ (-(α + 1) / 2) := Real.rpow_pos_of_pos hm _
  have hD : 0 < 1 + y * m ^ α := by positivity
  have hfr0 : 0 ≤ y * m ^ α / (1 + y * m ^ α) := by positivity
  have hfr1 : y * m ^ α / (1 + y * m ^ α) ≤ 1 := by
    rw [div_le_one hD]; linarith
  have hfr2 : y * m ^ α / (1 + y * m ^ α) ≤ y * m ^ α := by
    rw [div_le_iff₀ hD]; nlinarith [mul_pos hy hp]
  have hfr3 : y * m ^ α / (1 + y * m ^ α) ≤ y ^ (1 / 2 : ℝ) * m ^ (α / 2) := by
    refine (pg6p5_frac_sqrt (by positivity)).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, Real.mul_rpow hy.le hp.le, ← Real.rpow_mul hm.le]
    congr 2; ring
  refine ⟨by positivity, ?_, ?_, ?_⟩
  · calc m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) ≤ m ^ (-(α + 1) / 2) * (y * m ^ α) :=
          mul_le_mul_of_nonneg_left hfr2 hq.le
      _ = y * m ^ ((α - 1) / 2) := by
          have : m ^ ((α - 1) / 2) = m ^ (-(α + 1) / 2) * m ^ α := by
            rw [← Real.rpow_add hm]; congr 1; ring
          rw [this]; ring
  · simpa using mul_le_mul_of_nonneg_left hfr1 hq.le
  · calc m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α))
        ≤ m ^ (-(α + 1) / 2) * (y ^ (1 / 2 : ℝ) * m ^ (α / 2)) := mul_le_mul_of_nonneg_left hfr3 hq.le
      _ = y ^ (1 / 2 : ℝ) * m ^ (-(1 : ℝ) / 2) := by
          have : m ^ (-(1 : ℝ) / 2) = m ^ (-(α + 1) / 2) * m ^ (α / 2) := by
            rw [← Real.rpow_add hm]; congr 1; ring
          rw [this]; ring

section pg6p5_abstract
variable {α : ℝ} {A e : ℝ → ℝ} {s K C CE C0 : ℝ}

private lemma pg6p5_AW_small {y : ℝ} (hy : 0 < y) (hK : 0 < K) (hs : 0 ≤ s)
    (hAs : ∀ m, 0 < m → m ≤ 1 → 0 ≤ A m ∧ A m ≤ K / m) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1) :
    |(A m - s) * pg6p5_W α y m| ≤ (K + s) * y * m ^ ((α - 3) / 2) ∧
    A m * pg6p5_W α y m ≤ K * y * m ^ ((α - 3) / 2) := by
  obtain ⟨hA0, hA1⟩ := hAs m hm hm1
  obtain ⟨hW0, hW1, -, -⟩ := pg6p5_W_bounds (α := α) hy hm
  have hpow : m ^ ((α - 1) / 2) = m * m ^ ((α - 3) / 2) := by
    rw [show (α - 1) / 2 = 1 + (α - 3) / 2 by ring, Real.rpow_add hm, Real.rpow_one]
  have hq : 0 < m ^ ((α - 3) / 2) := Real.rpow_pos_of_pos hm _
  have hWle : pg6p5_W α y m ≤ y * (m * m ^ ((α - 3) / 2)) := by rw [← hpow]; exact hW1
  have hsm : s ≤ s / m := by
    rw [le_div_iff₀ hm]; nlinarith
  have hAs' : A m + s ≤ (K + s) / m := by
    have : K / m + s / m = (K + s) / m := by ring
    linarith
  have hKm : K / m * (y * (m * m ^ ((α - 3) / 2))) = K * y * m ^ ((α - 3) / 2) := by
    field_simp
  have hKsm : (K + s) / m * (y * (m * m ^ ((α - 3) / 2))) = (K + s) * y * m ^ ((α - 3) / 2) := by
    field_simp
  constructor
  · rw [abs_mul, abs_of_nonneg hW0]
    have habs : |A m - s| ≤ A m + s := by
      rw [abs_le]; constructor <;> linarith
    calc |A m - s| * pg6p5_W α y m ≤ ((K + s) / m) * (y * (m * m ^ ((α - 3) / 2))) :=
          mul_le_mul (habs.trans hAs') hWle hW0 (by positivity)
      _ = _ := hKsm
  · calc A m * pg6p5_W α y m ≤ (K / m) * (y * (m * m ^ ((α - 3) / 2))) :=
          mul_le_mul hA1 hWle hW0 (by positivity)
      _ = _ := hKm

private lemma pg6p5_AWe_large {y : ℝ} (hy : 0 < y) (hC : 0 < C) (hCE : 0 < CE)
    (hAl : ∀ m, 1 ≤ m → 0 ≤ A m ∧ A m ≤ C)
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m) {m : ℝ} (hm : 1 ≤ m) :
    A m * pg6p5_W α y m * e m ≤ C * CE * y ^ (1 / 2 : ℝ) * m ^ (-(3 : ℝ) / 2) := by
  have hm0 : 0 < m := lt_of_lt_of_le one_pos hm
  obtain ⟨hA0, hA1⟩ := hAl m hm
  obtain ⟨hW0, -, -, hW3⟩ := pg6p5_W_bounds (α := α) hy hm0
  obtain ⟨he0, -, he2⟩ := he m hm0
  have hpow : m ^ (-(3 : ℝ) / 2) = m ^ (-(1 : ℝ) / 2) / m := by
    rw [← Real.rpow_sub_one hm0.ne']; congr 1; ring
  rw [hpow]
  have h1 : A m * pg6p5_W α y m ≤ C * (y ^ (1 / 2 : ℝ) * m ^ (-(1 : ℝ) / 2)) :=
    mul_le_mul hA1 hW3 hW0 hC.le
  have h2 : 0 ≤ A m * pg6p5_W α y m := mul_nonneg hA0 hW0
  calc A m * pg6p5_W α y m * e m ≤ (C * (y ^ (1 / 2 : ℝ) * m ^ (-(1 : ℝ) / 2))) * (CE / m) :=
        mul_le_mul h1 he2 he0 (by positivity)
    _ = C * CE * y ^ (1 / 2 : ℝ) * (m ^ (-(1 : ℝ) / 2) / m) := by ring


private lemma pg6p5_W_cont {α y : ℝ} (hy : 0 < y) : ContinuousOn (pg6p5_W α y) (Ioi 0) :=
  (pg6p5_W_contDiffOn hy).continuousOn

private lemma pg6p5_int_large {y : ℝ} (hα : 1 < α) (hy : 0 < y) (hC : 0 < C) (hCE : 0 < CE)
    (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Ioi 0))
    (hAl : ∀ m, 1 ≤ m → 0 ≤ A m ∧ A m ≤ C)
    (hec : ContinuousOn e (Ioi 0))
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m) :
    IntegrableOn (fun m => (A m - s) * pg6p5_W α y m) (Ioi 1) ∧
    IntegrableOn (fun m => A m * pg6p5_W α y m) (Ioi 1) ∧
    IntegrableOn (fun m => A m * pg6p5_W α y m * e m) (Ioi 1) := by
  have hWint := ((pg6p5_W_int hα hy).1).mono_set (Ioi_subset_Ioi (zero_le_one : (0:ℝ) ≤ 1))
  have hsub : Ioi (1:ℝ) ⊆ Ioi 0 := Ioi_subset_Ioi zero_le_one
  have hWc := (pg6p5_W_cont (α := α) hy).mono hsub
  have hAc' := hAc.mono hsub
  have hec' := hec.mono hsub
  refine ⟨?_, ?_, ?_⟩
  · refine Integrable.mono' (hWint.const_mul (C + s)) ?_ ?_
    · exact ((hAc'.sub continuousOn_const).mul hWc).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
      have hm1 : (1:ℝ) ≤ m := le_of_lt hm
      obtain ⟨hA0, hA1⟩ := hAl m hm1
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy (lt_of_lt_of_le one_pos hm1)
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW0]
      have habs : |A m - s| ≤ C + s := by rw [abs_le]; constructor <;> linarith
      nlinarith
  · refine Integrable.mono' (hWint.const_mul C) ?_ ?_
    · exact (hAc'.mul hWc).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
      have hm1 : (1:ℝ) ≤ m := le_of_lt hm
      obtain ⟨hA0, hA1⟩ := hAl m hm1
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy (lt_of_lt_of_le one_pos hm1)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 hW0)]
      nlinarith
  · have hmaj : IntegrableOn (fun m : ℝ => C * CE * y ^ (1 / 2 : ℝ) * m ^ (-(3 : ℝ) / 2)) (Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
    refine Integrable.mono' hmaj ?_ ?_
    · exact ((hAc'.mul hWc).mul hec').aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with m hm
      have hm1 : (1:ℝ) ≤ m := le_of_lt hm
      obtain ⟨hA0, hA1⟩ := hAl m hm1
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy (lt_of_lt_of_le one_pos hm1)
      obtain ⟨he0, -, -⟩ := he m (lt_of_lt_of_le one_pos hm1)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hA0 hW0) he0)]
      exact pg6p5_AWe_large hy hC hCE hAl he hm1

private lemma pg6p5_int_small {y : ℝ} (hα : 1 < α) (hy : 0 < y) (hK : 0 < K) (hs : 0 ≤ s)
    (hAc : ContinuousOn A (Ioi 0))
    (hAs : ∀ m, 0 < m → m ≤ 1 → 0 ≤ A m ∧ A m ≤ K / m)
    (hec : ContinuousOn e (Ioi 0))
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m) :
    IntegrableOn (fun m => (A m - s) * pg6p5_W α y m) (Ioc 0 1) ∧
    IntegrableOn (fun m => A m * pg6p5_W α y m) (Ioc 0 1) ∧
    IntegrableOn (fun m => A m * pg6p5_W α y m * e m) (Ioc 0 1) := by
  have hsub : Ioc (0:ℝ) 1 ⊆ Ioi 0 := Ioc_subset_Ioi_self
  have hWc := (pg6p5_W_cont (α := α) hy).mono hsub
  have hAc' := hAc.mono hsub
  have hec' := hec.mono hsub
  have hr : IntegrableOn (fun m : ℝ => m ^ ((α - 3) / 2)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < (α - 3) / 2)
      (a := 0) (b := 1) |> (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1)
  refine ⟨?_, ?_, ?_⟩
  · refine Integrable.mono' (hr.const_mul ((K + s) * y)) ?_ ?_
    · exact ((hAc'.sub continuousOn_const).mul hWc).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
      rw [Real.norm_eq_abs]
      have := (pg6p5_AW_small (α := α) hy hK hs hAs hm.1 hm.2).1
      linarith
  · refine Integrable.mono' (hr.const_mul (K * y)) ?_ ?_
    · exact (hAc'.mul hWc).aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
      have h := (pg6p5_AW_small (α := α) hy hK hs hAs hm.1 hm.2).2
      obtain ⟨hA0, -⟩ := hAs m hm.1 hm.2
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy hm.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hA0 hW0)]
      linarith
  · refine Integrable.mono' (hr.const_mul (K * y)) ?_ ?_
    · exact ((hAc'.mul hWc).mul hec').aestronglyMeasurable measurableSet_Ioc
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
      have h := (pg6p5_AW_small (α := α) hy hK hs hAs hm.1 hm.2).2
      obtain ⟨hA0, -⟩ := hAs m hm.1 hm.2
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy hm.1
      obtain ⟨he0, he1, -⟩ := he m hm.1
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hA0 hW0) he0)]
      have : A m * pg6p5_W α y m * e m ≤ A m * pg6p5_W α y m := by
        simpa using mul_le_mul_of_nonneg_left he1 (mul_nonneg hA0 hW0)
      linarith

end pg6p5_abstract

section pg6p5_abstract2
variable {α : ℝ} {A e : ℝ → ℝ} {s K C CE C0 : ℝ}

private lemma pg6p5_Z_bound {y : ℝ} (hα : 1 < α) (hy : 0 < y) (hC : 0 < C) (hCE : 0 < CE)
    (hs : 0 ≤ s) (hC0 : 0 ≤ C0)
    (hAc : ContinuousOn A (Ioi 0))
    (hAl : ∀ m, 1 ≤ m → 0 ≤ A m ∧ A m ≤ C)
    (hec : ContinuousOn e (Ioi 0))
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m)
    (hIBP : ∀ a c, 1 ≤ a → a ≤ c → ∀ W : ℝ → ℝ, ContDiffOn ℝ 1 W (Icc a c) →
        |∫ m in a..c, (A m - s) * W m| ≤ C0 * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|)) :
    |∫ m in Ioi (1:ℝ), (A m - s) * pg6p5_W α y m| ≤
      C0 * (y + y ^ ((α + 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), |deriv (pg6p5_g α) w|) := by
  have hα0 : 0 < α := by linarith
  have hint := (pg6p5_int_large hα hy hC hCE hs hAc hAl hec he).1
  have htend := intervalIntegral_tendsto_integral_Ioi (1:ℝ) hint tendsto_id
  have hW1 : pg6p5_W α y 1 ≤ y := by
    have := (pg6p5_W_bounds (α := α) hy one_pos).2.1
    simpa using this
  have hW10 : 0 ≤ pg6p5_W α y 1 := (pg6p5_W_bounds (α := α) hy one_pos).1
  have hWt : Tendsto (fun c : ℝ => pg6p5_W α y c) atTop (𝓝 0) := by
    have h0 : Tendsto (fun c : ℝ => c ^ (-(α + 1) / 2)) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by linarith : 0 < (α + 1) / 2) |>.congr (fun c => by congr 1; ring)
    refine squeeze_zero' ?_ ?_ h0
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
      exact (pg6p5_W_bounds (α := α) hy hc).1
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with c hc
      exact (pg6p5_W_bounds (α := α) hy hc).2.2.1
  set G1 := ∫ w in Ioi (0:ℝ), |deriv (pg6p5_g α) w| with hG1
  have hrhs : Tendsto (fun c : ℝ => C0 * (|pg6p5_W α y 1| + |pg6p5_W α y c| +
      y ^ ((α + 1) / (2 * α)) * G1)) atTop (𝓝 (C0 * (|pg6p5_W α y 1| + |0| + y ^ ((α + 1) / (2 * α)) * G1))) := by
    exact (((tendsto_const_nhds.add hWt.abs).add tendsto_const_nhds).const_mul C0)
  have hle : ∀ᶠ c : ℝ in atTop, |∫ m in (1:ℝ)..c, (A m - s) * pg6p5_W α y m| ≤
      C0 * (|pg6p5_W α y 1| + |pg6p5_W α y c| + y ^ ((α + 1) / (2 * α)) * G1) := by
    filter_upwards [eventually_gt_atTop (1:ℝ)] with c hc
    refine (hIBP 1 c le_rfl hc.le (pg6p5_W α y) ?_).trans ?_
    · exact (pg6p5_W_contDiffOn hy).mono (fun m hm => lt_of_lt_of_le one_pos hm.1)
    · refine mul_le_mul_of_nonneg_left ?_ hC0
      have hvar := pg6p5_W_var hα hy one_pos hc.le
      have hcongr : ∀ m ∈ Set.uIcc (1:ℝ) c, |derivWithin (pg6p5_W α y) (Icc 1 c) m| =
          |deriv (pg6p5_W α y) m| := by
        intro m hm
        rw [Set.uIcc_of_le hc.le] at hm
        have hm0 : 0 < m := lt_of_lt_of_le one_pos hm.1
        have hd := (pg6p5_W_hasDeriv hα0 hy hm0).differentiableAt
        rw [hd.derivWithin ((uniqueDiffOn_Icc hc) m hm)]
      rw [intervalIntegral.integral_congr hcongr]
      linarith
  have := le_of_tendsto_of_tendsto htend.abs hrhs hle
  rw [abs_of_nonneg hW10, abs_zero, add_zero] at this
  refine this.trans ?_
  have := mul_le_mul_of_nonneg_left hW1 hC0
  nlinarith


private lemma pg6p5_diff_bound {y : ℝ} (hα : 1 < α) (hy : 0 < y) (hK : 0 < K) (hC : 0 < C) (hCE : 0 < CE)
    (hs : 0 ≤ s) (hC0 : 0 ≤ C0)
    (hAc : ContinuousOn A (Ioi 0))
    (hAs : ∀ m, 0 < m → m ≤ 1 → 0 ≤ A m ∧ A m ≤ K / m)
    (hAl : ∀ m, 1 ≤ m → 0 ≤ A m ∧ A m ≤ C)
    (hec : ContinuousOn e (Ioi 0))
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m)
    (hIBP : ∀ a c, 1 ≤ a → a ≤ c → ∀ W : ℝ → ℝ, ContDiffOn ℝ 1 W (Icc a c) →
        |∫ m in a..c, (A m - s) * W m| ≤ C0 * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|)) :
    |(∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m)) -
        s * (y ^ ((α - 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), pg6p5_g α w)| ≤
      (K + s) * (∫ m in Ioc (0:ℝ) 1, m ^ ((α - 3) / 2)) * y +
        C0 * (y + y ^ ((α + 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), |deriv (pg6p5_g α) w|) +
        (α - 1) * (K * (∫ m in Ioc (0:ℝ) 1, m ^ ((α - 3) / 2)) * y +
          C * CE * (∫ m in Ioi (1:ℝ), m ^ (-(3:ℝ) / 2)) * y ^ (1 / 2 : ℝ)) := by
  obtain ⟨hS1, hS2, hS3⟩ := pg6p5_int_small (α := α) (A := A) (e := e) (s := s) (K := K) (CE := CE) hα hy hK hs hAc hAs hec he
  obtain ⟨hL1, hL2, hL3⟩ := pg6p5_int_large (α := α) (A := A) (e := e) (s := s) (C := C) (CE := CE) hα hy hC hCE hs hAc hAl hec he
  have hunion : Ioc (0:ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi zero_le_one
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi 1) := by
    rw [Set.disjoint_left]; intro m hm hm'; exact absurd hm.2 (not_le.2 hm')
  have hX1 : IntegrableOn (fun m => (A m - s) * pg6p5_W α y m) (Ioi 0) := by
    rw [← hunion]; exact hS1.union hL1
  have hY1 : IntegrableOn (fun m => A m * pg6p5_W α y m * e m) (Ioi 0) := by
    rw [← hunion]; exact hS3.union hL3
  have hW1 := (pg6p5_W_int hα hy).1
  have hpt : ∀ m, A m * pg6p5_W α y m * (1 + (α - 1) * e m) =
      (A m - s) * pg6p5_W α y m + (α - 1) * (A m * pg6p5_W α y m * e m) + s * pg6p5_W α y m := by
    intro m; ring
  have h1 : IntegrableOn (fun m => (A m - s) * pg6p5_W α y m + (α - 1) * (A m * pg6p5_W α y m * e m)) (Ioi 0) :=
    hX1.add (hY1.const_mul _)
  have h2 : IntegrableOn (fun m => s * pg6p5_W α y m) (Ioi 0) := hW1.const_mul s
  have hsum : ∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m) =
      (∫ m in Ioi (0:ℝ), (A m - s) * pg6p5_W α y m) + (α - 1) * (∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * e m) +
        s * ∫ m in Ioi (0:ℝ), pg6p5_W α y m := by
    simp_rw [hpt]
    rw [integral_add h1 h2, integral_add hX1 (hY1.const_mul _),
      integral_const_mul, integral_const_mul]
  rw [hsum, (pg6p5_W_int hα hy).2]
  have hXsplit : ∫ m in Ioi (0:ℝ), (A m - s) * pg6p5_W α y m =
      (∫ m in Ioc (0:ℝ) 1, (A m - s) * pg6p5_W α y m) + ∫ m in Ioi (1:ℝ), (A m - s) * pg6p5_W α y m := by
    have := setIntegral_union hdisj measurableSet_Ioi hS1 hL1
    rwa [hunion] at this
  have hYsplit : ∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * e m =
      (∫ m in Ioc (0:ℝ) 1, A m * pg6p5_W α y m * e m) + ∫ m in Ioi (1:ℝ), A m * pg6p5_W α y m * e m := by
    have := setIntegral_union hdisj measurableSet_Ioi hS3 hL3
    rwa [hunion] at this
  set cint := ∫ m in Ioc (0:ℝ) 1, m ^ ((α - 3) / 2) with hcint
  set ctail := ∫ m in Ioi (1:ℝ), m ^ (-(3:ℝ) / 2) with hctail
  have hr : IntegrableOn (fun m : ℝ => m ^ ((α - 3) / 2)) (Ioc 0 1) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < (α - 3) / 2)
      (a := 0) (b := 1) |> (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1)
  have hrt : IntegrableOn (fun m : ℝ => m ^ (-(3:ℝ) / 2)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos
  -- small-range bounds
  have hXs : |∫ m in Ioc (0:ℝ) 1, (A m - s) * pg6p5_W α y m| ≤ (K + s) * cint * y := by
    have hb : ‖∫ m in Ioc (0:ℝ) 1, (A m - s) * pg6p5_W α y m‖ ≤
        ∫ m in Ioc (0:ℝ) 1, (K + s) * y * m ^ ((α - 3) / 2) := by
      refine norm_integral_le_of_norm_le (hr.const_mul ((K + s) * y)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
      rw [Real.norm_eq_abs]
      exact (pg6p5_AW_small (α := α) hy hK hs hAs hm.1 hm.2).1
    rw [Real.norm_eq_abs, integral_const_mul] at hb
    nlinarith
  have hYs : 0 ≤ ∫ m in Ioc (0:ℝ) 1, A m * pg6p5_W α y m * e m ∧
      ∫ m in Ioc (0:ℝ) 1, A m * pg6p5_W α y m * e m ≤ K * cint * y := by
    constructor
    · refine setIntegral_nonneg measurableSet_Ioc (fun m hm => ?_)
      obtain ⟨hA0, -⟩ := hAs m hm.1 hm.2
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy hm.1
      exact mul_nonneg (mul_nonneg hA0 hW0) (he m hm.1).1
    · have hb : ∫ m in Ioc (0:ℝ) 1, A m * pg6p5_W α y m * e m ≤
          ∫ m in Ioc (0:ℝ) 1, K * y * m ^ ((α - 3) / 2) := by
        refine setIntegral_mono_on hS3 (hr.const_mul (K * y)) measurableSet_Ioc (fun m hm => ?_)
        have h := (pg6p5_AW_small (α := α) hy hK hs hAs hm.1 hm.2).2
        obtain ⟨hA0, -⟩ := hAs m hm.1 hm.2
        obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy hm.1
        obtain ⟨he0, he1, -⟩ := he m hm.1
        have : A m * pg6p5_W α y m * e m ≤ A m * pg6p5_W α y m := by
          simpa using mul_le_mul_of_nonneg_left he1 (mul_nonneg hA0 hW0)
        linarith
      rw [integral_const_mul] at hb
      nlinarith
  have hYl : 0 ≤ ∫ m in Ioi (1:ℝ), A m * pg6p5_W α y m * e m ∧
      ∫ m in Ioi (1:ℝ), A m * pg6p5_W α y m * e m ≤ C * CE * ctail * y ^ (1 / 2 : ℝ) := by
    constructor
    · refine setIntegral_nonneg measurableSet_Ioi (fun m hm => ?_)
      have hm1 : (1:ℝ) ≤ m := le_of_lt hm
      obtain ⟨hA0, -⟩ := hAl m hm1
      obtain ⟨hW0, -, -, -⟩ := pg6p5_W_bounds (α := α) hy (lt_of_lt_of_le one_pos hm1)
      exact mul_nonneg (mul_nonneg hA0 hW0) (he m (lt_of_lt_of_le one_pos hm1)).1
    · have hb : ∫ m in Ioi (1:ℝ), A m * pg6p5_W α y m * e m ≤
          ∫ m in Ioi (1:ℝ), C * CE * y ^ (1 / 2 : ℝ) * m ^ (-(3:ℝ) / 2) := by
        refine setIntegral_mono_on hL3 (hrt.const_mul _) measurableSet_Ioi (fun m hm => ?_)
        exact pg6p5_AWe_large hy hC hCE hAl he (le_of_lt hm)
      rw [integral_const_mul, ← hctail] at hb
      have : C * CE * y ^ (1 / 2 : ℝ) * ctail = C * CE * ctail * y ^ (1 / 2 : ℝ) := by ring
      linarith
  have hZ := pg6p5_Z_bound hα hy hC hCE hs hC0 hAc hAl hec he hIBP
  rw [hXsplit, hYsplit]
  have hα1 : 0 ≤ α - 1 := by linarith
  set Xs := ∫ m in Ioc (0:ℝ) 1, (A m - s) * pg6p5_W α y m
  set Xl := ∫ m in Ioi (1:ℝ), (A m - s) * pg6p5_W α y m
  set Ys := ∫ m in Ioc (0:ℝ) 1, A m * pg6p5_W α y m * e m
  set Yl := ∫ m in Ioi (1:ℝ), A m * pg6p5_W α y m * e m
  have e1 : Xs + Xl + (α - 1) * (Ys + Yl) + s * (y ^ ((α - 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), pg6p5_g α w) -
      s * (y ^ ((α - 1) / (2 * α)) * ∫ w in Ioi (0:ℝ), pg6p5_g α w) = Xs + Xl + (α - 1) * (Ys + Yl) := by ring
  rw [e1]
  have habs : |Xs + Xl + (α - 1) * (Ys + Yl)| ≤ |Xs| + |Xl| + (α - 1) * (Ys + Yl) := by
    have h0 : 0 ≤ (α - 1) * (Ys + Yl) := mul_nonneg hα1 (add_nonneg hYs.1 hYl.1)
    calc |Xs + Xl + (α - 1) * (Ys + Yl)| ≤ |Xs + Xl| + |(α - 1) * (Ys + Yl)| := abs_add_le _ _
      _ ≤ |Xs| + |Xl| + (α - 1) * (Ys + Yl) := by
          rw [abs_of_nonneg h0]; linarith [abs_add_le Xs Xl]
  refine habs.trans ?_
  have := mul_le_mul_of_nonneg_left (add_le_add hYs.2 hYl.2) hα1
  linarith


private lemma pg6p5_rpow_tendsto {r : ℝ} (hr : 0 < r) :
    Tendsto (fun y : ℝ => y ^ r) (𝓝[>] 0) (𝓝 0) := by
  have := (Real.continuousAt_rpow_const (0:ℝ) r (Or.inr hr.le)).tendsto
  rw [Real.zero_rpow hr.ne'] at this
  exact this.mono_left nhdsWithin_le_nhds

private lemma pg6p5_small_tendsto (hα : 1 < α) (hK : 0 < K) (hC : 0 < C) (hCE : 0 < CE)
    (hs : 0 ≤ s) (hC0 : 0 ≤ C0)
    (hAc : ContinuousOn A (Ioi 0))
    (hAs : ∀ m, 0 < m → m ≤ 1 → 0 ≤ A m ∧ A m ≤ K / m)
    (hAl : ∀ m, 1 ≤ m → 0 ≤ A m ∧ A m ≤ C)
    (hec : ContinuousOn e (Ioi 0))
    (he : ∀ m, 0 < m → 0 ≤ e m ∧ e m ≤ 1 ∧ e m ≤ CE / m)
    (hIBP : ∀ a c, 1 ≤ a → a ≤ c → ∀ W : ℝ → ℝ, ContDiffOn ℝ 1 W (Icc a c) →
        |∫ m in a..c, (A m - s) * W m| ≤ C0 * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|)) :
    Tendsto (fun y : ℝ => (∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m)) /
        y ^ ((α - 1) / (2 * α))) (𝓝[>] 0) (𝓝 (s * ∫ w in Ioi (0:ℝ), pg6p5_g α w)) := by
  have hα0 : 0 < α := by linarith
  set p : ℝ := (α - 1) / (2 * α) with hp
  set I0 := ∫ w in Ioi (0:ℝ), pg6p5_g α w
  set G1 := ∫ w in Ioi (0:ℝ), |deriv (pg6p5_g α) w|
  set cint := ∫ m in Ioc (0:ℝ) 1, m ^ ((α - 3) / 2)
  set ctail := ∫ m in Ioi (1:ℝ), m ^ (-(3:ℝ) / 2)
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hp1 : p < 1 / 2 := by
    rw [hp, div_lt_iff₀ (by linarith)]; linarith
  have e1 : 0 < 1 - p := by linarith
  have e2 : 0 < 1 / 2 - p := by linarith
  have e3 : 0 < 1 / α := by positivity
  set c1 : ℝ := (K + s) * cint + C0 + (α - 1) * (K * cint)
  set a : ℝ → ℝ := fun y => c1 * y ^ (1 - p) + C0 * G1 * y ^ (1 / α) +
    (α - 1) * (C * CE * ctail) * y ^ (1 / 2 - p)
  have ha : Tendsto a (𝓝[>] 0) (𝓝 0) := by
    have h1 := (pg6p5_rpow_tendsto e1).const_mul c1
    have h2 := (pg6p5_rpow_tendsto e3).const_mul (C0 * G1)
    have h3 := (pg6p5_rpow_tendsto e2).const_mul ((α - 1) * (C * CE * ctail))
    have := (h1.add h2).add h3
    simpa [a] using this
  have hmain : Tendsto (fun y : ℝ => (∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m)) /
        y ^ p - s * I0) (𝓝[>] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ ha
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : (0:ℝ) < y := hy
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy' _
    have hbd := pg6p5_diff_bound hα hy' hK hC hCE hs hC0 hAc hAs hAl hec he hIBP
    rw [Real.norm_eq_abs]
    have e : (∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m)) / y ^ p - s * I0 =
        ((∫ m in Ioi (0:ℝ), A m * pg6p5_W α y m * (1 + (α - 1) * e m)) - s * (y ^ p * I0)) / y ^ p := by
      field_simp
    rw [e, abs_div, abs_of_pos hyp, div_le_iff₀ hyp]
    refine hbd.trans (le_of_eq ?_)
    have r1 : y = y ^ (1 - p) * y ^ p := by
      rw [← Real.rpow_add hy']; simp
    have r2 : y ^ ((α + 1) / (2 * α)) = y ^ (1 / α) * y ^ p := by
      rw [← Real.rpow_add hy']; congr 1; rw [hp]; field_simp; ring
    have r3 : y ^ (1 / 2 : ℝ) = y ^ (1 / 2 - p) * y ^ p := by
      rw [← Real.rpow_add hy']; congr 1; ring
    simp only [a, c1]
    linear_combination ((K + s) * cint + C0 + (α - 1) * (K * cint)) * r1 + (C0 * G1) * r2 +
      ((α - 1) * (C * CE * ctail)) * r3
  have := hmain.add_const (s * I0)
  simpa using this

end pg6p5_abstract2

private lemma pg6p5_Efun_continuousOn {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (Efun β) (Ioi 0) := by
  intro m hm
  have hQ := pg6p4_Qm_continuousAt hβ0 hβ1 hm
  have hQpos := (pg6p4_Qm_spec hβ0 hβ1 hm).1
  have hrD : ContDiffOn ℝ (⊤ : ℕ∞) (rW (emaW β)) (Ioi 0) :=
    ((contDiffOn_id.mul
      (lem_app_de_scalar_ii (pg6p4_wseq hβ0.le hβ1)).2.2.2.2.1).mono Ioi_subset_Ici_self)
  have hdr : ContinuousOn (deriv (rW (emaW β))) (Ioi 0) :=
    hrD.continuousOn_deriv_of_isOpen isOpen_Ioi (by simp)
  have hE : ContinuousAt (Efun β) m := by
    unfold Efun
    have hdA := (hdr (Qm β m) hQpos).continuousAt (Ioi_mem_nhds hQpos)
    have hcomp : ContinuousAt (fun x => deriv (rW (emaW β)) (Qm β x)) m :=
      hdA.tendsto.comp hQ
    exact hQ.mul hcomp
  exact hE.continuousWithinAt

private lemma pg6p5_I0 {α : ℝ} (hα : 1 < α) :
    ∫ w in Ioi (0:ℝ), pg6p5_g α w = Real.pi / (α * Real.cos (Real.pi / (2 * α))) := by
  have hα0 : 0 < α := by linarith
  have h := (pg6p5_beta (α := α) (s := (α + 1) / 2) hα0 (by linarith) (by linarith)).2
  have hcongr : ∀ w ∈ Ioi (0:ℝ), pg6p5_g α w = w ^ ((α + 1) / 2 - 1) / (1 + w ^ α) := by
    intro w _; unfold pg6p5_g; congr 2; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, h]
  congr 2
  rw [← Real.cos_pi_div_two_sub]
  have : Real.pi / 2 - Real.pi * ((α + 1) / 2) / α = -(Real.pi / (2 * α)) := by
    field_simp
    ring
  rw [this, Real.cos_neg]

private lemma pg6p5_const {α : ℝ} (hα : 1 < α) :
    Real.sqrt (2 * Real.pi) * (Real.pi / (α * Real.cos (Real.pi / (2 * α)))) /
      (Real.pi * dAl α) = 1 := by
  have hα0 : 0 < α := by linarith
  have hcos : 0 < Real.cos (Real.pi / (2 * α)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < Real.pi / (2 * α) := by positivity
      linarith [Real.pi_pos]
    · have : Real.pi / (2 * α) < Real.pi / 2 := by
        apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
      exact this
  unfold dAl c0
  have hpi := Real.pi_pos
  have h1 : Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 * Real.pi) := by
    have hh : Real.pi = Real.sqrt Real.pi * Real.sqrt Real.pi := (Real.mul_self_sqrt hpi.le).symm
    calc Real.sqrt (2 / Real.pi) * Real.pi = Real.sqrt (2 / Real.pi) * Real.sqrt Real.pi * Real.sqrt Real.pi := by
          rw [mul_assoc, ← hh]
      _ = Real.sqrt (2 / Real.pi * Real.pi) * Real.sqrt Real.pi := by
          rw [← Real.sqrt_mul (by positivity)]
      _ = Real.sqrt 2 * Real.sqrt Real.pi := by rw [div_mul_cancel₀ _ hpi.ne']
      _ = Real.sqrt (2 * Real.pi) := (Real.sqrt_mul (by norm_num) _).symm
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.2 (by positivity)
  have h2 : Real.pi * (Real.sqrt (2 / Real.pi) * Real.pi / (α * Real.cos (Real.pi / (2 * α)))) =
      Real.sqrt (2 * Real.pi) * Real.pi / (α * Real.cos (Real.pi / (2 * α))) := by
    rw [← h1]; ring
  rw [h2]
  field_simp

private lemma pg6p5_iii_proof {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsEquivalent (nhdsWithin (0 : ℝ) (Ioi 0)) (fun y : ℝ => profPhi α β y)
      (fun y : ℝ => dAl α * y ^ ((α - 1) / (2 * α))) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨K, C, hK, hC, hAs, hAl⟩ := pg6p4_Aav_upper hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcC, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  obtain ⟨C0', hIBP0⟩ := lem_app_pl_average_iii hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  have hCE : 0 < CE := lt_of_lt_of_le hcE hcC
  have he : ∀ m : ℝ, 0 < m → 0 ≤ (fun m => Efun β m / m) m ∧ (fun m => Efun β m / m) m ≤ 1 ∧
      (fun m => Efun β m / m) m ≤ CE / m := by
    intro m hm
    have hE0 := (pg6p4_E_pos hβ0 hβ1 hm).le
    have hE1 := lem_app_pl_weights_ii_E hβ0 hβ1 m hm
    have hE2 := (hE m hm).2
    refine ⟨div_nonneg hE0 hm.le, (div_le_one hm).2 hE1, ?_⟩
    show Efun β m / m ≤ CE / m
    exact div_le_div_of_nonneg_right (hE2.trans (by
      have : min m 1 ≤ 1 := min_le_right _ _
      nlinarith)) hm.le
  have hIBP : ∀ a c, 1 ≤ a → a ≤ c → ∀ W : ℝ → ℝ, ContDiffOn ℝ 1 W (Icc a c) →
      |∫ m in a..c, (Aav β m - Real.sqrt (2 * Real.pi)) * W m| ≤
        max C0' 0 * (|W a| + |W c| + ∫ m in a..c, |derivWithin W (Icc a c) m|) := by
    intro a c ha hac W hW
    refine (hIBP0 a c ha hac W hW).trans ?_
    refine mul_le_mul_of_nonneg_right (le_max_left _ _) ?_
    have : 0 ≤ ∫ m in a..c, |derivWithin W (Icc a c) m| :=
      intervalIntegral.integral_nonneg hac (fun _ _ => abs_nonneg _)
    positivity
  have hT := pg6p5_small_tendsto (α := α) (A := Aav β) (e := fun m => Efun β m / m)
    (s := Real.sqrt (2 * Real.pi)) (K := K) (C := C) (CE := CE) (C0 := max C0' 0) hα hK hC hCE
    (Real.sqrt_nonneg _) (le_max_right _ _) (pg6p4_Aav_continuousOn hβ0 hβ1) hAs hAl
    ((pg6p5_Efun_continuousOn hβ0 hβ1).div continuousOn_id (fun m hm => ne_of_gt hm)) he hIBP
  rw [pg6p5_I0 hα] at hT
  have hd : 0 < dAl α := by
    unfold dAl c0
    have hcos : 0 < Real.cos (Real.pi / (2 * α)) := by
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · have : 0 < Real.pi / (2 * α) := by positivity
        linarith [Real.pi_pos]
      · have : Real.pi / (2 * α) < Real.pi / 2 := by
          apply div_lt_div_of_pos_left Real.pi_pos (by norm_num) (by linarith)
        exact this
    have := Real.pi_pos
    positivity
  have hT2 := hT.div_const (Real.pi * dAl α)
  rw [pg6p5_const hα] at hT2
  refine isEquivalent_of_tendsto_one (hT2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy' : (0:ℝ) < y := hy
  have hyp : 0 < y ^ ((α - 1) / (2 * α)) := Real.rpow_pos_of_pos hy' _
  have hΦ := (pg6p4_change_integral (α := α) (β := β) (y := y) hβ0 hβ1
    (by simpa only [Aav] using (pg6p4_m_integrable hα hβ0 hβ1 hy'))).2
  show (∫ m in Ioi (0:ℝ), Aav β m * pg6p5_W α y m * (1 + (α - 1) * (Efun β m / m))) /
      y ^ ((α - 1) / (2 * α)) / (Real.pi * dAl α) =
      profPhi α β y / (dAl α * y ^ ((α - 1) / (2 * α)))
  rw [hΦ]
  have hpt : ∀ m : ℝ, Aav β m * pg6p5_W α y m * (1 + (α - 1) * (Efun β m / m)) =
      Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m) := by
    intro m; unfold Aav pg6p5_W; ring
  simp_rw [hpt]
  have hpi := Real.pi_pos
  have alg : ∀ I : ℝ, I / y ^ ((α - 1) / (2 * α)) / (Real.pi * dAl α) =
      1 / Real.pi * I / (dAl α * y ^ ((α - 1) / (2 * α))) := by
    intro I; field_simp
  exact alg _

/-- `lem:app-pl-super`, part (iii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[The supercritical drift profile]\label{lem:app-pl-super}
Let $\alpha>1$ and $p_\alpha\defeq(\alpha-1)/(2\alpha)$. The function $\Phi_{\alpha,\bmom}$ of
\cref{eqn:app-pl-Phi} is finite, positive and continuous on $(0,\infty)$, and
\[
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\quad(y\to\infty),\qquad \Phi_{\alpha,\bmom}(y)\sim d_\alpha y^{p_\alpha}\quad(y\downarrow0).
\]
Under \cref{assum:app-pl-regime}, for every row sequence $i\to\infty$ with $i/N\to0$,
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{b_N}\sim\Phi_{\alpha,\bmom}\big((i_{\mathrm c}/i)^\alpha\big).
\]
\end{lemma}
-/
theorem lem_app_pl_super_iii {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsEquivalent (nhdsWithin (0 : ℝ) (Ioi 0)) (fun y : ℝ => profPhi α β y)
      (fun y : ℝ => dAl α * y ^ ((α - 1) / (2 * α))) := by
  exact pg6p5_iii_proof hα hβ0 hβ1

/-! ### P-G.6.P1 helpers (begin) -/
private lemma pg6_Kc_pos {α : ℝ} (hα : 1 < α) : 0 < Kc α := by
  unfold Kc
  have h0 : 0 < α := by linarith
  have hs : 0 < Real.sin (Real.pi / α) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · rw [div_lt_iff₀ h0]; nlinarith [Real.pi_pos]
  positivity

private lemma pg6_ii_rowN_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n)) {l : ℝ}
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 l)) :
    Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) := by
  have hK := pg6_Kc_pos hα
  have h1 : Tendsto (fun n => (Kc α * ((N n : ℝ) / (B n : ℝ)))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Tendsto.const_mul_atTop hK hreg.hγ)
  have h2 := h.mul h1
  rw [mul_zero] at h2
  refine h2.congr (fun n => ?_)
  have hB : (B n : ℝ) ≠ 0 := by exact_mod_cast (hreg.hBpos n).ne'
  have hN : (N n : ℝ) ≠ 0 := by exact_mod_cast (hreg.hNpos n).ne'
  unfold icCross
  field_simp

private lemma pg6_rowNum_pos {N : ℕ} (i : Fin N) : 0 < rowNum i := by
  unfold rowNum; positivity

private lemma pg6_plSpec_eq {α c : ℝ} {N : ℕ} (i : Fin N) :
    plSpec α c N i = c * rowNum i ^ (-α) := rfl

private lemma pg6_icCross_pos {α : ℝ} (hα : 1 < α) {B : ℕ} (hB : 0 < B) : 0 < icCross α B := by
  unfold icCross
  have := pg6_Kc_pos hα
  have : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

private lemma pg6_bN_sq {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) :
    0 ≤ bN α c N B ∧ bN α c N B ^ 2 = c / ((N : ℝ) / (B : ℝ) * icCross α B ^ α) := by
  have hic := pg6_icCross_pos hα hB
  have hz : 0 < (N : ℝ) / (B : ℝ) * icCross α B ^ α := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < B := by exact_mod_cast hB
    positivity
  unfold bN
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hz.le _), ?_⟩
  rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast, ← Real.rpow_mul hz.le]
  norm_num [Real.rpow_neg_one, div_eq_mul_inv]

private lemma pg6_bN_main {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (i : Fin N) (s2 : ℝ) (hs2 : 0 < s2) :
    bN α c N B * Real.sqrt ((icCross α B / rowNum i) ^ α / s2) =
      Real.sqrt (plSpec α c N i / (gammaOf N B * s2)) := by
  obtain ⟨h0, h1⟩ := pg6_bN_sq hα hc hN hB
  have hic := pg6_icCross_pos hα hB
  have hr := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  conv_lhs => rw [← Real.sqrt_sq h0]
  rw [← Real.sqrt_mul (sq_nonneg _), h1]
  congr 1
  rw [pg6_plSpec_eq, Real.div_rpow hic.le hr.le, Real.rpow_neg hr.le]
  unfold gammaOf
  have : 0 < icCross α B ^ α := Real.rpow_pos_of_pos hic _
  have : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hr _
  field_simp

private lemma pg6_sPow_two_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) : 0 < sPow β 2 := by
  rw [sPow_two h0.le h1]
  apply div_pos <;> linarith

/-! #### Positivity of the integrand of `dZero` (private copies of the Participation helpers) -/

private lemma pg6_wseq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : WeightSeq (emaW β) := by
  refine ⟨fun j => ?_, ?_, ⟨0, ?_⟩⟩
  · unfold emaW
    exact mul_nonneg (by linarith) (pow_nonneg hβ0 j)
  · have hg : Summable (fun j : ℕ => β ^ j) := summable_geometric_of_lt_one hβ0 hβ1
    have := hg.mul_left (1 - β)
    refine this.congr (fun j => ?_)
    simp [emaW]
  · unfold emaW
    rw [pow_zero, mul_one]
    exact (by linarith : (0:ℝ) < 1 - β).ne'

private lemma pg6_rW_facts {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContinuousOn (rW (emaW β)) (Ici 0) := by
  have hFc := (lem_app_de_scalar_ii (pg6_wseq hβ0 hβ1)).2.2.1
  exact continuousOn_id.mul hFc

private lemma pg6_rW_atTop {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (rW (emaW β)) atTop atTop := by
  have hT := (lem_app_de_scalar_iii (pg6_wseq hβ0.le hβ1)).2.2.2.2.2.2
  have hset : {j : ℕ | 0 < emaW β j} = Set.univ := by
    ext j
    simp only [Set.mem_univ, iff_true]
    unfold emaW
    have h1 : (0:ℝ) < 1 - β := by linarith
    exact mul_pos h1 (pow_pos hβ0 j)
  rw [hset, Set.Infinite.encard_eq Set.infinite_univ, ENat.toENNReal_top] at hT
  refine tendsto_atTop.2 (fun K => ?_)
  have hlt : ENNReal.ofReal K < ⊤ := ENNReal.ofReal_lt_top
  filter_upwards [hT.eventually_const_lt hlt] with q hq
  exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 hq).1.le

private lemma pg6_rW_surj {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := by
  have hcont := pg6_rW_facts hβ0.le hβ1
  have hT := pg6_rW_atTop hβ0 hβ1
  have hr0 : rW (emaW β) 0 = 0 := (lem_app_de_scalar_iii (pg6_wseq hβ0.le hβ1)).2.2.1
  obtain ⟨b, hb⟩ := ((hT.eventually_gt_atTop m).and (eventually_gt_atTop (0:ℝ))).exists
  have hmem : m ∈ Icc (rW (emaW β) 0) (rW (emaW β) b) :=
    ⟨by rw [hr0]; exact hm.le, hb.1.le⟩
  obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc hb.2.le (hcont.mono Icc_subset_Ici_self) hmem
  have hxpos : 0 < x := by
    rcases hx.1.eq_or_lt with h | h
    · exfalso
      rw [← h, hr0] at hfx
      linarith
    · exact h
  exact ⟨x, Set.mem_Ioi.2 hxpos, hfx⟩

private lemma pg6_Qm_spec {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Qm β m ∧ rW (emaW β) (Qm β m) = m := by
  have hex : ∃ a ∈ Ioi (0:ℝ), rW (emaW β) a = m := pg6_rW_surj hβ0 hβ1 hm
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg6_Lw_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    0 < Lw (emaW β) q := by
  have hw := pg6_wseq hβ0.le hβ1
  have hwn : ∀ j, 0 ≤ emaW β j := hw.1
  have hwp : ∀ j, 0 < emaW β j := fun j => by
    unfold emaW
    exact mul_pos (by linarith) (pow_pos hβ0 j)
  obtain ⟨-, -, hJ, -⟩ := lem_app_de_scalar_i
  have hJq : ∀ j, 0 < emaW β j * J (emaW β j ^ 2 * q) := fun j =>
    mul_pos (hwp j) (hJ _ (mul_nonneg (sq_nonneg _) hq)).1
  have hsum : Summable (fun j => emaW β j * J (emaW β j ^ 2 * q)) := by
    refine Summable.of_nonneg_of_le (fun j => (hJq j).le) (fun j => ?_) hw.2.1
    calc emaW β j * J (emaW β j ^ 2 * q) ≤ emaW β j * 1 :=
          mul_le_mul_of_nonneg_left (hJ _ (mul_nonneg (sq_nonneg _) hq)).2 (hwn j)
      _ = emaW β j := mul_one _
  exact hsum.tsum_pos (fun j => (hJq j).le) 0 (hJq 0)


private lemma pg6_plSpec_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (i : Fin N) : 0 < plSpec α c N i := by
  rw [pg6_plSpec_eq]; exact mul_pos hc (Real.rpow_pos_of_pos (pg6_rowNum_pos i) _)

private lemma pg6_plSpec_anti {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N : ℕ} :
    Antitone (plSpec α c N) := by
  intro i j hij
  rw [pg6_plSpec_eq, pg6_plSpec_eq]
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  have hi := pg6_rowNum_pos i
  have hle : rowNum i ≤ rowNum j := by
    unfold rowNum
    have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  rw [Real.rpow_neg hi.le, Real.rpow_neg (pg6_rowNum_pos j).le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hi _) (Real.rpow_le_rpow hi.le hle hα.le)

private lemma pg6_mOf_mem {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) := by
  have hbij := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  have hex : ∃ a, a ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ a = s := hbij.surjOn (show s ∈ Ioi 0 from hs)
  unfold mOf
  exact (Function.invFunOn_pos hex).1

private lemma pg6_G_pos {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {s : ℝ} (hs : 0 < s) : 0 < Gfun β B μ i s := by
  have hm := pg6_mOf_mem μ hβ0 hβ1 hB hN hanti hpos hs
  obtain ⟨hQ, hr⟩ := pg6_Qm_spec hβ0 hβ1 hm.1
  have hFw : 0 < Fw (emaW β) (Qm β (mOf β B μ s)) := by
    have : Qm β (mOf β B μ s) * Fw (emaW β) (Qm β (mOf β B μ s)) = mOf β B μ s := hr
    by_contra hneg
    push Not at hneg
    nlinarith [hm.1, mul_nonpos_of_nonneg_of_nonpos hQ.le hneg]
  have hL := pg6_Lw_pos hβ0 hβ1 hQ.le
  have hΛ : 0 < partLam B μ (mOf β B μ s) :=
    (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm
  unfold Gfun partF
  have := hpos i
  positivity

private lemma pg6_dZero_pos {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    0 < dZero β B μ i := by
  have hint := prop_app_pl_drift_zero_ii_fin μ hβ0 hβ1 hB hN hanti hpos i
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf
    have : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < B := by exact_mod_cast hB
    positivity
  unfold dZero
  refine mul_pos (by positivity) ?_
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun u : ℝ => Gfun β B μ i (u ^ 2)) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall (fun u hu =>
      (pg6_G_pos μ hβ0 hβ1 hB hN hanti hpos i (pow_pos hu 2)).le))
  rw [integral_pos_iff_support_of_nonneg_ae hnn hint]
  have hsub : Ioi (0 : ℝ) ⊆ Function.support (fun u : ℝ => Gfun β B μ i (u ^ 2)) := fun u hu =>
    (pg6_G_pos μ hβ0 hβ1 hB hN hanti hpos i (pow_pos hu 2)).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Measure.restrict_apply_self, Real.volume_Ioi]
  exact ENNReal.zero_lt_top


private lemma pg6_gamma_pos {N B : ℕ} (hB : 0 < B) (hN : 0 < N) : 0 < gammaOf N B := by
  unfold gammaOf
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast hB
  positivity

private lemma pg6_split {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {M : ℝ} (hM0 : 0 < M) (hMγ : M < gammaOf N B) :
    Real.sqrt 2 * dZero β B μ i =
      sqrt2DPiece β B μ i 0 M + sqrt2DPiece β B μ i M (gammaOf N B) := by
  have hγ := pg6_gamma_pos hB hN
  have h := lem_app_pl_drift_participation_i μ hβ0 hβ1 hB hN hpos i
  have hD := pg6_dZero_pos μ hβ0 hβ1 hB hN hanti hpos i
  set f : ℝ → ℝ := fun m => Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m with hf
  have hint : IntegrableOn f (Ioo 0 (gammaOf N B)) := by
    by_contra hni
    have h0 : ∫ m in Ioo 0 (gammaOf N B), f m = 0 := integral_undef hni
    rw [h0, mul_zero] at h
    have : 0 < Real.sqrt 2 * dZero β B μ i := mul_pos (by positivity) hD
    linarith
  have hunion : Ioo 0 (gammaOf N B) = Ioc 0 M ∪ Ioo M (gammaOf N B) := by
    ext x
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hx : x ≤ M
      · exact Or.inl ⟨h1, hx⟩
      · exact Or.inr ⟨not_le.1 hx, h2⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, lt_of_le_of_lt h2 hMγ⟩
      · exact ⟨lt_trans hM0 h1, h2⟩
  have hdisj : Disjoint (Ioc 0 M) (Ioo M (gammaOf N B)) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx.2 (not_le.2 hx'.1)
  have hsplit : ∫ m in Ioo 0 (gammaOf N B), f m =
      (∫ m in Ioo 0 M, f m) + ∫ m in Ioo M (gammaOf N B), f m := by
    rw [hunion, setIntegral_union hdisj measurableSet_Ioo
      (hint.mono_set (by rw [hunion]; exact subset_union_left))
      (hint.mono_set (by rw [hunion]; exact subset_union_right)), integral_Ioc_eq_integral_Ioo]
  rw [h]
  unfold sqrt2DPiece
  rw [hsplit]
  ring


private lemma pg6_Efun_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m : ℝ} (hm : 0 < m) :
    0 < Efun β m := by
  obtain ⟨hQ, -⟩ := pg6_Qm_spec hβ0 hβ1 hm
  obtain ⟨-, -, -, hd, hdp, -⟩ := lem_app_de_scalar_iii (pg6_wseq hβ0.le hβ1)
  unfold Efun
  rw [(hd _ hQ).deriv]
  exact mul_pos hQ (hdp _ hQ)

private lemma pg6_f_nonneg {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 ≤ Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m := by
  obtain ⟨hQ, -⟩ := pg6_Qm_spec hβ0 hβ1 hm.1
  have hE := pg6_Efun_pos hβ0 hβ1 hm.1
  have hL := pg6_Lw_pos hβ0 hβ1 hQ.le
  have hθ := ((prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.2 m hm).2
  have hΛ : 0 < partLam B μ m := (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm
  have hF : 0 ≤ partF B μ i m := by
    unfold partF
    have := hpos i
    positivity
  have hP : 0 ≤ partBfun B μ i m := mul_nonneg (Real.sqrt_nonneg _) hF
  unfold Aav
  have : Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) / Efun β m * partBfun B μ i m * Efun β m *
      thetaN β B μ m =
      Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) * partBfun B μ i m * thetaN β B μ m := by
    field_simp
  rw [this]
  positivity

private lemma pg6_piece_nonneg {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {lo hi : ℝ} (hlo : 0 ≤ lo) (hhi : hi ≤ gammaOf N B) : 0 ≤ sqrt2DPiece β B μ i lo hi := by
  have hγ := pg6_gamma_pos hB hN
  unfold sqrt2DPiece
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioo (fun m hm => ?_))
  exact pg6_f_nonneg μ hβ0 hβ1 hB hN hanti hpos i ⟨lt_of_le_of_lt hlo hm.1, lt_of_lt_of_le hm.2 hhi⟩


/-! #### P-G.6.P2: the head piece in the `u` variable -/

private lemma pg6p2_piece_u {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {δ : ℝ} (hδ0 : 0 < δ) (hδγ : δ < gammaOf N B) :
    sqrt2DPiece β B μ i 0 δ =
      2 / (Real.pi * gammaOf N B) *
        ∫ u in Ioi (Real.sqrt (sN β B μ δ)), Gfun β B μ i (u ^ 2) := by
  have hγ := pg6_gamma_pos hB hN
  obtain ⟨hcd, hanti_s, hbij, hθ⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hinj := hanti_s.injOn
  have hspos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < sN β B μ m := fun m hm => hbij.mapsTo hm
  have hδm : δ ∈ Ioo 0 (gammaOf N B) := ⟨hδ0, hδγ⟩
  have hsδ := hspos δ hδm
  set g : ℝ → ℝ := fun y => Gfun β B μ i y / (2 * Real.sqrt y) with hg
  set a : ℝ := Real.sqrt (sN β B μ δ) with ha
  have ha0 : 0 < a := Real.sqrt_pos.2 hsδ
  have ha2 : a ^ 2 = sN β B μ δ := Real.sq_sqrt hsδ.le
  -- Step A
  have hA : ∫ u in Ioi a, Gfun β B μ i (u ^ 2) = ∫ y in Ioi (sN β B μ δ), g y := by
    have himg : (fun u : ℝ => u ^ 2) '' Ioi a = Ioi (sN β B μ δ) := by
      ext y
      constructor
      · rintro ⟨u, hu, rfl⟩
        have hu' : a < u := hu
        show sN β B μ δ < u ^ 2
        rw [← ha2]
        nlinarith
      · intro hy
        have hy' : sN β B μ δ < y := hy
        have hy0 : 0 < y := lt_trans hsδ hy'
        refine ⟨Real.sqrt y, ?_, Real.sq_sqrt hy0.le⟩
        show a < Real.sqrt y
        exact Real.sqrt_lt_sqrt hsδ.le hy'
    have hderiv : ∀ u ∈ Ioi a, HasDerivWithinAt (fun u : ℝ => u ^ 2) (2 * u) (Ioi a) u := by
      intro u _
      exact ((hasDerivAt_pow 2 u).congr_deriv (by ring)).hasDerivWithinAt
    have hinj2 : Set.InjOn (fun u : ℝ => u ^ 2) (Ioi a) := by
      intro x hx y hy hxy
      have hx' : a < x := hx
      have hy' : a < y := hy
      exact (pow_left_inj₀ (by linarith) (by linarith) two_ne_zero).1 hxy
    have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi
      hderiv hinj2 g
    rw [himg] at key
    rw [key]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    have hu' : 0 < u := lt_trans ha0 hu
    simp only [hg, smul_eq_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * u), Real.sqrt_sq hu'.le]
    field_simp
  -- Step B
  have hB2 : ∫ y in Ioi (sN β B μ δ), g y =
      ∫ m in Ioo 0 δ, |deriv (sN β B μ) m| • g (sN β B μ m) := by
    have hsub : Ioo 0 δ ⊆ Ioo 0 (gammaOf N B) := Ioo_subset_Ioo_right hδγ.le
    have hdiff : ∀ m ∈ Ioo 0 δ,
        HasDerivWithinAt (sN β B μ) (deriv (sN β B μ) m) (Ioo 0 δ) m := by
      intro m hm
      have hm' := hsub hm
      have hca := hcd.contDiffAt (Ioo_mem_nhds hm'.1 hm'.2)
      exact (hca.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      hdiff (hinj.mono hsub) g
    have himg : sN β B μ '' Ioo 0 δ = Ioi (sN β B μ δ) := by
      ext y
      constructor
      · rintro ⟨m, hm, rfl⟩
        exact hanti_s (hsub hm) hδm hm.2
      · intro hy
        have hy' : sN β B μ δ < y := hy
        obtain ⟨m, hm, hmy⟩ := hbij.surjOn (show y ∈ Ioi (0:ℝ) from lt_trans hsδ hy')
        refine ⟨m, ⟨hm.1, ?_⟩, hmy⟩
        by_contra hnot
        push_neg at hnot
        have := hanti_s.antitoneOn hδm hm hnot
        linarith
    rw [himg] at key
    exact key
  -- Step C
  have hC : ∀ m ∈ Ioo 0 (gammaOf N B), |deriv (sN β B μ) m| • g (sN β B μ m) =
      1 / 2 * (Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m) := by
    intro m hm
    obtain ⟨hm0, hmg⟩ := hm
    have hm' : m ∈ Ioo 0 (gammaOf N B) := ⟨hm0, hmg⟩
    have hs : 0 < sN β B μ m := hspos m hm'
    have hθ' : 0 < thetaN β B μ m := (hθ m hm').2
    have hd : deriv (sN β B μ) m = -(thetaN β B μ m * sN β B μ m) := by
      have := (hθ m hm').1
      field_simp at this
      linarith
    have hmOf : mOf β B μ (sN β B μ m) = m :=
      hinj (Function.invFunOn_mem ⟨m, hm', rfl⟩) hm' (Function.invFunOn_eq ⟨m, hm', rfl⟩)
    obtain ⟨hQ, hr⟩ := pg6_Qm_spec hβ0 hβ1 hm0
    have hE := pg6_Efun_pos hβ0 hβ1 hm0
    have hΛ : 0 < partLam B μ m := (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm'
    have hX : 0 < (gammaOf N B - m) / (m * partLam B μ m) :=
      div_pos (sub_pos.2 hmg) (mul_pos hm0 hΛ)
    have hr' : Qm β m * Fw (emaW β) (Qm β m) = m := hr
    have hFw : Fw (emaW β) (Qm β m) = m / Qm β m :=
      eq_div_of_mul_eq hQ.ne' (by rw [mul_comm]; exact hr')
    have hsq1 := Real.mul_self_sqrt hs.le
    have hsq2 := Real.mul_self_sqrt hQ.le
    have hSpos := Real.sqrt_pos.2 hs
    have key : Real.sqrt (sN β B μ m) * Real.sqrt (Qm β m) =
        m * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) := by
      rw [← Real.sqrt_mul hs.le, show m * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) =
        Real.sqrt (m ^ 2 * ((gammaOf N B - m) / (m * partLam B μ m))) by
          rw [Real.sqrt_mul (sq_nonneg m), Real.sqrt_sq hm0.le]]
      congr 1
      have hQ0 : Qm β m ≠ 0 := hQ.ne'
      have hΛ0 : partLam B μ m ≠ 0 := hΛ.ne'
      have hm0' : m ≠ 0 := hm0.ne'
      unfold sN
      field_simp
    have hE0 : Efun β m ≠ 0 := hE.ne'
    rw [hd, abs_neg, abs_of_pos (mul_pos hθ' hs)]
    simp only [hg, smul_eq_mul]
    unfold Gfun
    rw [hmOf, hFw]
    unfold Aav partBfun
    generalize hS : Real.sqrt (sN β B μ m) = S at hsq1 key hSpos ⊢
    rw [← hsq1]
    have hST : S * Qm β m = m * Real.sqrt (Qm β m) * Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)) := by
      linear_combination (-S) * hsq2 + Real.sqrt (Qm β m) * key
    have hQ0 : Qm β m ≠ 0 := hQ.ne'
    have hm0' : m ≠ 0 := hm0.ne'
    field_simp
    linear_combination (Lw (emaW β) (Qm β m) * partF B μ i m) * hST
  have hI : ∫ u in Ioi a, Gfun β B μ i (u ^ 2) =
      1 / 2 * ∫ m in Ioo 0 δ,
        Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m := by
    rw [hA, hB2, ← MeasureTheory.integral_const_mul (1 / 2 : ℝ)]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
    intro m hm
    exact hC m ⟨hm.1, lt_trans hm.2 hδγ⟩
  unfold sqrt2DPiece
  rw [hI]
  have hpi : Real.pi * gammaOf N B ≠ 0 := mul_ne_zero Real.pi_ne_zero hγ.ne'
  field_simp

private lemma pg6p2_Gform {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {y : ℝ} (hy : 0 < y) :
    mOf β B μ y ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ y) = y ∧
    Gfun β B μ i y = Lw (emaW β) (Qm β (mOf β B μ y)) / Fw (emaW β) (Qm β (mOf β B μ y)) *
      (((gammaOf N B - mOf β B μ y) * Fw (emaW β) (Qm β (mOf β B μ y))) * μ i /
       (y + ((gammaOf N B - mOf β B μ y) * Fw (emaW β) (Qm β (mOf β B μ y))) * μ i)) := by
  obtain ⟨-, -, hbij, -⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hex : ∃ a, a ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ a = y := hbij.surjOn (show y ∈ Ioi (0:ℝ) from hy)
  have hmem : mOf β B μ y ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ y) = y := by
    unfold mOf
    exact ⟨(Function.invFunOn_pos hex).1, (Function.invFunOn_pos hex).2⟩
  refine ⟨hmem.1, hmem.2, ?_⟩
  set m := mOf β B μ y with hm
  obtain ⟨hm0, hmg⟩ := hmem.1
  obtain ⟨hQ, hr⟩ := pg6_Qm_spec hβ0 hβ1 hm0
  have hr' : Qm β m * Fw (emaW β) (Qm β m) = m := hr
  have hΛ : 0 < partLam B μ m := (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hmem.1
  set Q := Qm β m with hQdef
  set F := Fw (emaW β) Q with hF
  have hFpos : 0 < F := by
    by_contra hneg
    push_neg at hneg
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hQ.le hneg]
  have hsy := hmem.2
  unfold sN at hsy
  rw [← hQdef] at hsy
  have hΛy : partLam B μ m = (gammaOf N B - m) * F / y := by
    have h1 : y * (Q * partLam B μ m) = (gammaOf N B - m) * m := by
      rw [← hsy]; field_simp
    rw [eq_div_iff hy.ne']
    have : Q * (partLam B μ m * y) = Q * ((gammaOf N B - m) * F) := by
      calc Q * (partLam B μ m * y) = y * (Q * partLam B μ m) := by ring
        _ = (gammaOf N B - m) * m := h1
        _ = Q * ((gammaOf N B - m) * F) := by rw [← hr']; ring
    exact mul_left_cancel₀ hQ.ne' this
  unfold Gfun
  show Lw (emaW β) Q / F * partF B μ i m = _
  unfold partF
  rw [hΛy]
  have hmuy := hpos i
  have hden : 0 < y + (gammaOf N B - m) * F * μ i := by
    have : 0 < (gammaOf N B - m) * F * μ i := mul_pos (mul_pos (sub_pos.2 hmg) hFpos) hmuy
    linarith
  field_simp

private lemma pg6p2_arctan_int {k a : ℝ} (hk : 0 < k) :
    IntegrableOn (fun u : ℝ => k / (u ^ 2 + k)) (Ioi a) ∧
      ∫ u in Ioi a, k / (u ^ 2 + k) = Real.sqrt k * (Real.pi / 2 - Real.arctan (a / Real.sqrt k)) := by
  have hsk : 0 < Real.sqrt k := Real.sqrt_pos.2 hk
  set Fa : ℝ → ℝ := fun u => Real.sqrt k * Real.arctan (u / Real.sqrt k) with hFa
  have hderiv : ∀ u ∈ Ici a, HasDerivAt Fa (k / (u ^ 2 + k)) u := by
    intro u _
    have h1 : HasDerivAt (fun u : ℝ => u / Real.sqrt k) (1 / Real.sqrt k) u := by
      simpa using (hasDerivAt_id u).div_const (Real.sqrt k)
    have h2 := (h1.arctan).const_mul (Real.sqrt k)
    refine h2.congr_deriv ?_
    have hsq : Real.sqrt k ^ 2 = k := Real.sq_sqrt hk.le
    field_simp
    rw [hsq]
    ring
  have hlim : Tendsto Fa atTop (𝓝 (Real.sqrt k * (Real.pi / 2))) := by
    have h1 : Tendsto (fun u : ℝ => u / Real.sqrt k) atTop atTop :=
      tendsto_id.atTop_div_const hsk
    exact (((Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1).const_mul (Real.sqrt k))
  have hint : IntegrableOn (fun u : ℝ => k / (u ^ 2 + k)) (Ioi a) := by
    refine integrableOn_Ioi_deriv_of_nonneg (g := Fa) (g' := fun u => k / (u ^ 2 + k))
      (l := Real.sqrt k * (Real.pi / 2)) ?_ (fun u hu => hderiv u (Set.mem_Ici.2 (le_of_lt hu))) ?_ hlim
    · exact (hderiv a (Set.mem_Ici.2 le_rfl)).continuousAt.continuousWithinAt
    · intro u _
      positivity
  refine ⟨hint, ?_⟩
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint hlim]
  simp only [hFa]
  ring

private lemma pg6p2_min_pos {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Icc a b))
    (hpos : ∀ y ∈ Icc a b, 0 < f y) : ∃ m : ℝ, 0 < m ∧ ∀ y ∈ Icc a b, m ≤ f y := by
  by_cases hne : (Icc a b).Nonempty
  · obtain ⟨y0, hy0, hmin⟩ := isCompact_Icc.exists_isMinOn hne hf
    exact ⟨f y0, hpos y0 hy0, fun y hy => hmin hy⟩
  · refine ⟨1, one_pos, fun y hy => ?_⟩
    exact absurd ⟨y, hy⟩ hne

private lemma pg6p2_Fw_facts {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (∀ q, 0 ≤ q → 0 < Fw (emaW β) q ∧ Fw (emaW β) q ≤ sPow β 2) ∧
      ContinuousOn (Fw (emaW β)) (Ici 0) := by
  have hF := Fw_admissible (pg6_wseq hβ0.le hβ1)
  have h0 : Fw (emaW β) 0 = sPow β 2 := (lem_app_de_scalar_ii (pg6_wseq hβ0.le hβ1)).2.2.2.2.2.2.1
  refine ⟨fun q hq => ⟨hF.pos q hq, ?_⟩, hF.contOn⟩
  rw [← h0]
  exact hF.le_zero q hq

private lemma pg6p2_Lw_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {q : ℝ} (hq : 0 ≤ q) :
    Lw (emaW β) q ≤ 1 := by
  have hw := pg6_wseq hβ0.le hβ1
  have hwn : ∀ j, 0 ≤ emaW β j := hw.1
  obtain ⟨-, -, hJ, -⟩ := lem_app_de_scalar_i
  have hJq : ∀ j, 0 ≤ emaW β j * J (emaW β j ^ 2 * q) := fun j =>
    mul_nonneg (hwn j) (hJ _ (mul_nonneg (sq_nonneg _) hq)).1.le
  have hle : ∀ j, emaW β j * J (emaW β j ^ 2 * q) ≤ emaW β j := fun j => by
    calc emaW β j * J (emaW β j ^ 2 * q) ≤ emaW β j * 1 :=
          mul_le_mul_of_nonneg_left (hJ _ (mul_nonneg (sq_nonneg _) hq)).2 (hwn j)
      _ = emaW β j := mul_one _
  have hsum : Summable (fun j => emaW β j * J (emaW β j ^ 2 * q)) :=
    Summable.of_nonneg_of_le hJq hle hw.2.1
  unfold Lw
  calc ∑' j, emaW β j * J (emaW β j ^ 2 * q) ≤ ∑' j, emaW β j :=
        hsum.tsum_le_tsum hle hw.2.1
    _ = 1 := tsum_emaW hβ0.le hβ1

private lemma pg6p2_Q_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {m q : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (h : m ≤ rW (emaW β) q) : Qm β m ≤ q := by
  obtain ⟨hQ, hr⟩ := pg6_Qm_spec hβ0 hβ1 hm
  have hmono := (lem_app_de_scalar_iii (pg6_wseq hβ0.le hβ1)).2.1
  rw [← hr] at h
  exact (hmono.le_iff_le (Set.mem_Ici.2 hQ.le) (Set.mem_Ici.2 hq)).1 h

private lemma pg6p2_F_lower {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {M : ℝ} (hM : 0 < M) :
    ∃ c : ℝ, 0 < c ∧ ∀ m ∈ Ioc (0:ℝ) M, c ≤ Fw (emaW β) (Qm β m) := by
  obtain ⟨hFp, hFc⟩ := pg6p2_Fw_facts hβ0 hβ1
  obtain ⟨hQM, hrM⟩ := pg6_Qm_spec hβ0 hβ1 hM
  obtain ⟨c, hc, hcle⟩ := pg6p2_min_pos (f := Fw (emaW β)) (a := 0) (b := Qm β M)
    (hFc.mono Icc_subset_Ici_self) (fun q hq => (hFp q hq.1).1)
  refine ⟨c, hc, fun m hm => hcle _ ⟨(pg6_Qm_spec hβ0 hβ1 hm.1).1.le, ?_⟩⟩
  refine pg6p2_Q_le hβ0 hβ1 hm.1 hQM.le ?_
  rw [hrM]; exact hm.2

private lemma pg6p2_sqrt_alg {γ s μ : ℝ} (hγ : 0 < γ) (hs : 0 < s) (hμ : 0 < μ) :
    Real.sqrt (γ * s * μ) / γ = Real.sqrt s * Real.sqrt (μ / γ) := by
  obtain ⟨g, hg, rfl⟩ : ∃ g : ℝ, 0 < g ∧ γ = g * g := ⟨Real.sqrt γ, Real.sqrt_pos.2 hγ,
    (Real.mul_self_sqrt hγ.le).symm⟩
  have e1 : Real.sqrt (g * g * s * μ) = g * Real.sqrt s * Real.sqrt μ := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_mul_self hg.le]
  have e2 : Real.sqrt (μ / (g * g)) = Real.sqrt μ / g := by
    rw [Real.sqrt_div hμ.le, Real.sqrt_mul_self hg.le]
  rw [e1, e2]
  field_simp

/-- Pointwise bound of the integrand of the head in the `u` variable. -/
private lemma pg6p2_G_le {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {M : ℝ} (hM0 : 0 < M) (hMγ : M < gammaOf N B) {c : ℝ} (hc : 0 < c)
    (hcF : ∀ m ∈ Ioc (0:ℝ) M, c ≤ Fw (emaW β) (Qm β m))
    {u : ℝ} (hu : Real.sqrt (sN β B μ M) < u) :
    0 ≤ Gfun β B μ i (u ^ 2) ∧ Gfun β B μ i (u ^ 2) ≤
      1 / c * (gammaOf N B * sPow β 2 * μ i / (u ^ 2 + gammaOf N B * sPow β 2 * μ i)) := by
  have hγ := pg6_gamma_pos hB hN
  obtain ⟨-, hanti_s, hbij, -⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hMm : M ∈ Ioo 0 (gammaOf N B) := ⟨hM0, hMγ⟩
  have hsM : 0 < sN β B μ M := hbij.mapsTo hMm
  have hu0 : 0 < u := lt_trans (Real.sqrt_pos.2 hsM) hu
  have hy : 0 < u ^ 2 := by positivity
  obtain ⟨hmem, hsm, hG⟩ := pg6p2_Gform μ hβ0 hβ1 hB hN hanti hpos i hy
  set m := mOf β B μ (u ^ 2) with hm
  have hmM : m < M := by
    by_contra hnot
    push_neg at hnot
    have := hanti_s.antitoneOn hMm hmem hnot
    have h2 : sN β B μ M < u ^ 2 := by
      have := Real.sqrt_lt' hu0 |>.1 hu
      exact this
    linarith
  obtain ⟨hFpos, hFle⟩ := (pg6p2_Fw_facts hβ0 hβ1).1 (Qm β m) (pg6_Qm_spec hβ0 hβ1 hmem.1).1.le
  have hcm := hcF m ⟨hmem.1, hmM.le⟩
  have hLpos := pg6_Lw_pos hβ0 hβ1 (pg6_Qm_spec hβ0 hβ1 hmem.1).1.le
  have hLle := pg6p2_Lw_le hβ0 hβ1 (pg6_Qm_spec hβ0 hβ1 hmem.1).1.le
  have hmu := hpos i
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  set F := Fw (emaW β) (Qm β m) with hFdef
  set t := (gammaOf N B - m) * F with ht
  have ht0 : 0 < t := mul_pos (sub_pos.2 hmem.2) hFpos
  have htle : t ≤ gammaOf N B * sPow β 2 := by
    rw [ht]
    exact mul_le_mul (by linarith [hmem.1]) hFle hFpos.le hγ.le
  rw [hG]
  have h1 : 0 ≤ t * μ i / (u ^ 2 + t * μ i) := by positivity
  refine ⟨by positivity, ?_⟩
  have h2 : t * μ i / (u ^ 2 + t * μ i) ≤
      gammaOf N B * sPow β 2 * μ i / (u ^ 2 + gammaOf N B * sPow β 2 * μ i) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hy hmu, mul_le_mul_of_nonneg_right htle hmu.le, mul_nonneg hy.le
      (mul_nonneg (sub_nonneg.2 htle) hmu.le)]
  have h3 : Lw (emaW β) (Qm β m) / F ≤ 1 / c := by
    rw [div_le_div_iff₀ hFpos hc]
    nlinarith
  calc Lw (emaW β) (Qm β m) / F * (t * μ i / (u ^ 2 + t * μ i))
      ≤ 1 / c * (t * μ i / (u ^ 2 + t * μ i)) :=
        mul_le_mul_of_nonneg_right h3 h1
    _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)

private lemma pg6p2_head_bound {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {M : ℝ} (hM0 : 0 < M) (hMγ : M < gammaOf N B) {c : ℝ} (hc : 0 < c)
    (hcF : ∀ m ∈ Ioc (0:ℝ) M, c ≤ Fw (emaW β) (Qm β m)) :
    sqrt2DPiece β B μ i 0 M ≤ Real.sqrt (sPow β 2) / c * Real.sqrt (μ i / gammaOf N B) := by
  have hγ := pg6_gamma_pos hB hN
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hmu := hpos i
  obtain ⟨-, -, hbij, -⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hsM : 0 < sN β B μ M := hbij.mapsTo ⟨hM0, hMγ⟩
  set a := Real.sqrt (sN β B μ M) with ha
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  rw [pg6p2_piece_u μ hβ0 hβ1 hB hN hanti hpos i hM0 hMγ]
  set k := gammaOf N B * sPow β 2 * μ i with hk
  have hk0 : 0 < k := by positivity
  obtain ⟨hint, hval⟩ := pg6p2_arctan_int (k := k) (a := a) hk0
  have hGint : IntegrableOn (fun u : ℝ => Gfun β B μ i (u ^ 2)) (Ioi a) :=
    (prop_app_pl_drift_zero_ii_fin μ hβ0 hβ1 hB hN hanti hpos i).mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi ha0) le_rfl)
  have hle : ∫ u in Ioi a, Gfun β B μ i (u ^ 2) ≤ ∫ u in Ioi a, 1 / c * (k / (u ^ 2 + k)) :=
    setIntegral_mono_on hGint (hint.const_mul (1 / c)) measurableSet_Ioi (fun u hu =>
      (pg6p2_G_le μ hβ0 hβ1 hB hN hanti hpos i hM0 hMγ hc hcF hu).2)
  rw [integral_const_mul, hval] at hle
  have hatan : 0 ≤ Real.arctan (a / Real.sqrt k) :=
    Real.arctan_nonneg.2 (div_nonneg ha0 (Real.sqrt_nonneg _))
  have hsk : 0 ≤ Real.sqrt k := Real.sqrt_nonneg _
  have h2 : ∫ u in Ioi a, Gfun β B μ i (u ^ 2) ≤ 1 / c * (Real.sqrt k * (Real.pi / 2)) := by
    refine hle.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    nlinarith
  have hsq := pg6p2_sqrt_alg hγ hs2 hmu
  calc 2 / (Real.pi * gammaOf N B) * ∫ u in Ioi a, Gfun β B μ i (u ^ 2)
      ≤ 2 / (Real.pi * gammaOf N B) * (1 / c * (Real.sqrt k * (Real.pi / 2))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 1 / c * (Real.sqrt k / gammaOf N B) := by
        field_simp
    _ = _ := by
        rw [hk, hsq]; ring

/-- `lem:app-pl-head`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Head]\label{lem:app-pl-head}
For every fixed $M>0$ and all large $N$, $\sqrt2\,\mathfrak d_i^{\le M}\le C_M\sqrt{\mu_i/\gamma}$ for
every $i$. If a row sequence satisfies $m_N(1/\mu_i)\to0$, then
$\sqrt2\,\mathfrak d_i^{\le M}\sim\sqrt{\mu_i/(\gamma\sw2)}$.
\end{lemma}
-/
theorem lem_app_pl_head_i {α β : ℝ} :
    ∀ M : ℝ, 0 < M → ∃ C : ℝ, ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n),
        sqrt2DPiece β (B n) (plSpec α (c n) (N n)) i 0 M ≤
          C * Real.sqrt (plSpec α (c n) (N n) i / gammaOf (N n) (B n)) := by
  intro M hM
  by_cases hβ : 0 < β ∧ β < 1
  · obtain ⟨c, hc, hcF⟩ := pg6p2_F_lower hβ.1 hβ.2 hM
    refine ⟨Real.sqrt (sPow β 2) / c, fun N B c' hreg => ?_⟩
    filter_upwards [hreg.hγ.eventually_gt_atTop M] with n hn i
    have hn' : M < gammaOf (N n) (B n) := hn
    have := pg6p2_head_bound (plSpec α (c' n) (N n)) hβ.1 hβ.2 (hreg.hBpos n) (hreg.hNpos n)
      (pg6_plSpec_anti hreg.hα (hreg.hcpos n)) (fun j => pg6_plSpec_pos (hreg.hcpos n) j) i hM hn' hc hcF
    exact this
  · refine ⟨0, fun N B c' hreg => absurd ⟨hreg.hβ0, hreg.hβ1⟩ hβ⟩

/-! #### P-G.6.P2: the participation inverse and the divergence `Λ_N(δ) μ_i → ∞` -/

private lemma pg6p2_Lam_spec {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partLam B μ m ∧ partMN B μ (partLam B μ m) = m := by
  obtain ⟨hb1, hb2, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  have hex : ∃ a ∈ Ioi (0:ℝ), partMN B μ a = m := hb1.surjOn hm
  unfold partLam
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma pg6p2_partMN_mono {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {x y : ℝ}
    (hx : 0 ≤ x) (hxy : x ≤ y) : partMN B μ x ≤ partMN B μ y := by
  unfold partMN
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ => ?_)) (by positivity)
  have hj := hpos j
  have h1 : 0 < 1 + x * μ j := by nlinarith [mul_nonneg hx hj.le]
  have h2 : 0 < 1 + y * μ j := by nlinarith [mul_nonneg (hx.trans hxy) hj.le]
  rw [div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) hj.le, mul_pos hj hj,
    mul_nonneg (mul_nonneg (sub_nonneg.2 hxy) hj.le) hj.le]

private lemma pg6p2_partMN_scale {N B : ℕ} (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {x t : ℝ}
    (hx : 0 ≤ x) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t * partMN B μ x ≤ partMN B μ (t * x) := by
  unfold partMN
  rw [mul_left_comm]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have hj := hpos j
  have h1 : 0 < 1 + x * μ j := by nlinarith [mul_nonneg hx hj.le]
  have h2 : 0 < 1 + t * x * μ j := by nlinarith [mul_nonneg (mul_nonneg ht0 hx) hj.le]
  rw [mul_div_assoc', div_le_div_iff₀ h1 h2]
  nlinarith [mul_nonneg (mul_nonneg ht0 hx) hj.le, mul_nonneg (sub_nonneg.2 ht1)
    (mul_nonneg (mul_nonneg ht0 hx) hj.le), mul_nonneg (mul_nonneg ht0 (mul_nonneg hx hj.le))
    (mul_nonneg (sub_nonneg.2 ht1) (mul_nonneg hx hj.le))]

/-- If `m_N(1/μ_i) < δ/L` then `Λ_N(δ) μ_i > L`. -/
private lemma pg6p2_z_gt {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (i : Fin N) {δ L : ℝ} (hδ : δ ∈ Ioo 0 (gammaOf N B)) (hL : 1 ≤ L)
    (h : partMN B μ (1 / μ i) < δ / L) : L < partLam B μ δ * μ i := by
  obtain ⟨hΛ, hΛm⟩ := pg6p2_Lam_spec μ hB hN hpos hδ
  by_contra hnot
  push_neg at hnot
  have hmu := hpos i
  have hL0 : 0 < L := by linarith
  have h1 : partLam B μ δ / L ≤ 1 / μ i := by
    rw [div_le_div_iff₀ hL0 hmu]; linarith
  have h2 := pg6p2_partMN_mono (B := B) μ hpos (by positivity : 0 ≤ partLam B μ δ / L) h1
  have h3 := pg6p2_partMN_scale (B := B) μ hpos hΛ.le (by positivity : 0 ≤ 1 / L)
    (by rw [div_le_one hL0]; exact hL)
  rw [hΛm] at h3
  have e : 1 / L * partLam B μ δ = partLam B μ δ / L := by ring
  rw [e] at h3
  have e2 : 1 / L * δ = δ / L := by ring
  rw [e2] at h3
  linarith

private lemma pg6p2_FL_eps {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ m ∈ Ioc (0:ℝ) δ,
      (1 - ε) * sPow β 2 ≤ Fw (emaW β) (Qm β m) ∧ 1 - ε ≤ Lw (emaW β) (Qm β m) := by
  have hw := pg6_wseq hβ0.le hβ1
  obtain ⟨-, -, hFc, hLc, -, -, hF0, -, hL0, -⟩ := lem_app_de_scalar_ii hw
  have hF0' : Fw (emaW β) 0 = sPow β 2 := hF0
  have hL0' : Lw (emaW β) 0 = 1 := by rw [hL0]; exact tsum_emaW hβ0.le hβ1
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hFc0 := (Metric.continuousWithinAt_iff.1 (hFc 0 (Set.mem_Ici.2 le_rfl))) (ε * sPow β 2)
    (by positivity)
  have hLc0 := (Metric.continuousWithinAt_iff.1 (hLc 0 (Set.mem_Ici.2 le_rfl))) ε hε
  obtain ⟨d1, hd1, h1⟩ := hFc0
  obtain ⟨d2, hd2, h2⟩ := hLc0
  set q0 : ℝ := min d1 d2 / 2 with hq0
  have hq0pos : 0 < q0 := by positivity
  have hmono := (lem_app_de_scalar_iii hw).2.1
  have hr0 : rW (emaW β) 0 = 0 := (lem_app_de_scalar_iii hw).2.2.1
  have hrq : 0 < rW (emaW β) q0 := by
    have := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hq0pos.le) hq0pos
    rwa [hr0] at this
  refine ⟨rW (emaW β) q0, hrq, fun m hm => ?_⟩
  have hQ := (pg6_Qm_spec hβ0 hβ1 hm.1).1
  have hQle : Qm β m ≤ q0 := pg6p2_Q_le hβ0 hβ1 hm.1 hq0pos.le hm.2
  have hdist1 : dist (Qm β m) 0 < d1 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hQ]
    have : min d1 d2 ≤ d1 := min_le_left _ _
    linarith [lt_min hd1 hd2]
  have hdist2 : dist (Qm β m) 0 < d2 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hQ]
    have : min d1 d2 ≤ d2 := min_le_right _ _
    linarith [lt_min hd1 hd2]
  have e1 := h1 (Set.mem_Ici.2 hQ.le) hdist1
  have e2 := h2 (Set.mem_Ici.2 hQ.le) hdist2
  rw [Real.dist_eq, hF0'] at e1
  rw [Real.dist_eq, hL0'] at e2
  constructor
  · have := (abs_lt.1 e1).1
    nlinarith
  · have := (abs_lt.1 e2).1
    linarith

private lemma pg6p2_frac_mono {y a b : ℝ} (hy : 0 < y) (ha : 0 < a) (hab : a ≤ b) :
    a / (y + a) ≤ b / (y + b) := by
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

private lemma pg6p2_G_two {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {δ : ℝ} (hδ0 : 0 < δ) (hδγ : δ < gammaOf N B) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hFL : ∀ m ∈ Ioc (0:ℝ) δ, (1 - ε) * sPow β 2 ≤ Fw (emaW β) (Qm β m) ∧
      1 - ε ≤ Lw (emaW β) (Qm β m))
    {u : ℝ} (hu : Real.sqrt (sN β B μ δ) < u) :
    (1 - ε) / sPow β 2 * (((gammaOf N B - δ) * ((1 - ε) * sPow β 2) * μ i) /
        (u ^ 2 + (gammaOf N B - δ) * ((1 - ε) * sPow β 2) * μ i)) ≤ Gfun β B μ i (u ^ 2) ∧
    Gfun β B μ i (u ^ 2) ≤ 1 / ((1 - ε) * sPow β 2) *
      (gammaOf N B * sPow β 2 * μ i / (u ^ 2 + gammaOf N B * sPow β 2 * μ i)) := by
  have hγ := pg6_gamma_pos hB hN
  obtain ⟨-, hanti_s, hbij, -⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hδm : δ ∈ Ioo 0 (gammaOf N B) := ⟨hδ0, hδγ⟩
  have hsδ : 0 < sN β B μ δ := hbij.mapsTo hδm
  have hu0 : 0 < u := lt_trans (Real.sqrt_pos.2 hsδ) hu
  have hy : 0 < u ^ 2 := by positivity
  obtain ⟨hmem, hsm, hG⟩ := pg6p2_Gform μ hβ0 hβ1 hB hN hanti hpos i hy
  set m := mOf β B μ (u ^ 2) with hm
  have hmδ : m < δ := by
    by_contra hnot
    push_neg at hnot
    have := hanti_s.antitoneOn hδm hmem hnot
    have h2 : sN β B μ δ < u ^ 2 := (Real.sqrt_lt' hu0).1 hu
    linarith
  have hQ := (pg6_Qm_spec hβ0 hβ1 hmem.1).1
  obtain ⟨hFpos, hFle⟩ := (pg6p2_Fw_facts hβ0 hβ1).1 (Qm β m) hQ.le
  obtain ⟨hFlo, hLlo⟩ := hFL m ⟨hmem.1, hmδ.le⟩
  have hLle := pg6p2_Lw_le hβ0 hβ1 hQ.le
  have hmu := hpos i
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hε' : 0 < 1 - ε := by linarith
  set F := Fw (emaW β) (Qm β m) with hFdef
  set L := Lw (emaW β) (Qm β m) with hLdef
  set t := (gammaOf N B - m) * F with ht
  have ht0 : 0 < t := mul_pos (sub_pos.2 hmem.2) hFpos
  have htle : t ≤ gammaOf N B * sPow β 2 := by
    rw [ht]
    exact mul_le_mul (by linarith [hmem.1]) hFle hFpos.le hγ.le
  have htge : (gammaOf N B - δ) * ((1 - ε) * sPow β 2) ≤ t := by
    rw [ht]
    exact mul_le_mul (by linarith) hFlo (by positivity) (sub_pos.2 hmem.2).le
  have hkl : 0 < (gammaOf N B - δ) * ((1 - ε) * sPow β 2) := by
    have := sub_pos.2 hδγ
    positivity
  rw [hG]
  have hLpos : 0 < L := lt_of_lt_of_le hε' hLlo
  constructor
  · have h1 : ((gammaOf N B - δ) * ((1 - ε) * sPow β 2) * μ i) /
        (u ^ 2 + (gammaOf N B - δ) * ((1 - ε) * sPow β 2) * μ i) ≤
        t * μ i / (u ^ 2 + t * μ i) :=
      pg6p2_frac_mono hy (by positivity) (mul_le_mul_of_nonneg_right htge hmu.le)
    have h2 : (1 - ε) / sPow β 2 ≤ L / F := by
      rw [div_le_div_iff₀ hs2 hFpos]
      nlinarith
    calc (1 - ε) / sPow β 2 * _ ≤ (1 - ε) / sPow β 2 * (t * μ i / (u ^ 2 + t * μ i)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ L / F * (t * μ i / (u ^ 2 + t * μ i)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  · have h1 : t * μ i / (u ^ 2 + t * μ i) ≤
        gammaOf N B * sPow β 2 * μ i / (u ^ 2 + gammaOf N B * sPow β 2 * μ i) :=
      pg6p2_frac_mono hy (by positivity) (mul_le_mul_of_nonneg_right htle hmu.le)
    have h2 : L / F ≤ 1 / ((1 - ε) * sPow β 2) := by
      rw [div_le_div_iff₀ hFpos (by positivity)]
      nlinarith
    calc L / F * (t * μ i / (u ^ 2 + t * μ i)) ≤ 1 / ((1 - ε) * sPow β 2) *
          (t * μ i / (u ^ 2 + t * μ i)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

private lemma pg6p2_S1 {g s μ : ℝ} (hg : 0 < g) (hs : 0 < s) (hμ : 0 < μ) :
    Real.sqrt (g * s * μ) / (g * s) = Real.sqrt (μ / (g * s)) := by
  have hgs : 0 < g * s := by positivity
  generalize g * s = p at hgs ⊢
  obtain ⟨r, hr, rfl⟩ : ∃ r : ℝ, 0 < r ∧ p = r * r := ⟨Real.sqrt p, Real.sqrt_pos.2 hgs,
    (Real.mul_self_sqrt hgs.le).symm⟩
  rw [Real.sqrt_mul (mul_self_nonneg r), Real.sqrt_mul_self hr.le, Real.sqrt_div hμ.le,
    Real.sqrt_mul_self hr.le]
  field_simp

private lemma pg6p2_S2a {g s μ δ Q Λ S : ℝ} (hg : 0 < g) (hs : 0 < s) (hμ : 0 < μ) (hδ : 0 < δ)
    (hQ : 0 < Q) (hΛ : 0 < Λ) (hS0 : 0 ≤ S) (hS : S ≤ g * δ / (Q * Λ)) :
    Real.sqrt S / g ≤ Real.sqrt (μ / (g * s)) * Real.sqrt (s * δ / (Q * (Λ * μ))) := by
  rw [← Real.sqrt_mul (by positivity)]
  have e : Real.sqrt S / g = Real.sqrt (S / g ^ 2) := by
    rw [Real.sqrt_div hS0, Real.sqrt_sq hg.le]
  rw [e]
  apply Real.sqrt_le_sqrt
  have h1 : S / g ^ 2 ≤ g * δ / (Q * Λ) / g ^ 2 := div_le_div_of_nonneg_right hS (by positivity)
  refine h1.trans (le_of_eq ?_)
  field_simp

private lemma pg6p2_S2b {g s μ δ Q Λ S ε : ℝ} (hg : 0 < g) (hs : 0 < s) (hμ : 0 < μ) (hδ : 0 < δ)
    (hQ : 0 < Q) (hΛ : 0 < Λ) (hS0 : 0 ≤ S) (hS : S ≤ g * δ / (Q * Λ)) (h2δ : 2 * δ ≤ g)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Real.sqrt S / Real.sqrt ((g - δ) * ((1 - ε) * s) * μ) ≤
      Real.sqrt (2 * δ / (Q * ((1 - ε) * s) * (Λ * μ))) := by
  have hk : 0 < (g - δ) * ((1 - ε) * s) * μ := by
    have : 0 < g - δ := by linarith
    have : 0 < 1 - ε := by linarith
    positivity
  rw [← Real.sqrt_div hS0]
  apply Real.sqrt_le_sqrt
  have hε' : 0 < 1 - ε := by linarith
  have h1 : S / ((g - δ) * ((1 - ε) * s) * μ) ≤
      g * δ / (Q * Λ) / ((g - δ) * ((1 - ε) * s) * μ) := div_le_div_of_nonneg_right hS hk.le
  have h2 : g * δ / (Q * Λ) / ((g - δ) * ((1 - ε) * s) * μ) ≤
      g * δ / (Q * Λ) / ((g / 2) * ((1 - ε) * s) * μ) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    have : g / 2 ≤ g - δ := by linarith
    have := mul_le_mul_of_nonneg_right this (by positivity : 0 ≤ (1 - ε) * s)
    exact mul_le_mul_of_nonneg_right this hμ.le
  refine h1.trans (h2.trans (le_of_eq ?_))
  field_simp

private lemma pg6p2_head_two {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N)
    {M δ : ℝ} (hδ0 : 0 < δ) (hδM : δ ≤ M) (hMγ : M < gammaOf N B) (h2δ : 2 * δ ≤ gammaOf N B)
    {c : ℝ} (hc : 0 < c) (hcF : ∀ m ∈ Ioc (0:ℝ) M, c ≤ Fw (emaW β) (Qm β m))
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hFL : ∀ m ∈ Ioc (0:ℝ) δ, (1 - ε) * sPow β 2 ≤ Fw (emaW β) (Qm β m) ∧
      1 - ε ≤ Lw (emaW β) (Qm β m)) :
    sqrt2DPiece β B μ i 0 M ≤ Real.sqrt (μ i / (gammaOf N B * sPow β 2)) *
        (1 / (1 - ε) + 2 / (Real.pi * c) *
          Real.sqrt (sPow β 2 * δ / (Qm β δ * (partLam B μ δ * μ i)))) ∧
    Real.sqrt (μ i / (gammaOf N B * sPow β 2)) * ((1 - ε) *
        Real.sqrt ((1 - δ / gammaOf N B) * (1 - ε)) *
        (1 - Real.sqrt (2 * δ / (Qm β δ * ((1 - ε) * sPow β 2) * (partLam B μ δ * μ i))))) ≤
      sqrt2DPiece β B μ i 0 M := by
  have hγ := pg6_gamma_pos hB hN
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hmu := hpos i
  have hε' : 0 < 1 - ε := by linarith
  have hδγ : δ < gammaOf N B := by linarith
  have hM0 : 0 < M := lt_of_lt_of_le hδ0 hδM
  obtain ⟨-, hanti_s, hbij, -⟩ := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hMm : M ∈ Ioo 0 (gammaOf N B) := ⟨hM0, hMγ⟩
  have hδm : δ ∈ Ioo 0 (gammaOf N B) := ⟨hδ0, hδγ⟩
  have hsM : 0 < sN β B μ M := hbij.mapsTo hMm
  have hsδ : 0 < sN β B μ δ := hbij.mapsTo hδm
  have hsle : sN β B μ M ≤ sN β B μ δ := hanti_s.antitoneOn hδm hMm hδM
  set a' := Real.sqrt (sN β B μ M) with ha'
  set a := Real.sqrt (sN β B μ δ) with ha
  have ha'0 : 0 ≤ a' := Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha'a : a' ≤ a := Real.sqrt_le_sqrt hsle
  have hQ := (pg6_Qm_spec hβ0 hβ1 hδ0).1
  obtain ⟨hΛ, -⟩ := pg6p2_Lam_spec μ hB hN hpos hδm
  rw [pg6p2_piece_u μ hβ0 hβ1 hB hN hanti hpos i hM0 hMγ]
  -- integrability
  have hGint' : IntegrableOn (fun u : ℝ => Gfun β B μ i (u ^ 2)) (Ioi a') :=
    (prop_app_pl_drift_zero_ii_fin μ hβ0 hβ1 hB hN hanti hpos i).mono_measure
      (Measure.restrict_mono (Ioi_subset_Ioi ha'0) le_rfl)
  have hGint : IntegrableOn (fun u : ℝ => Gfun β B μ i (u ^ 2)) (Ioi a) :=
    hGint'.mono_set (Ioi_subset_Ioi ha'a)
  have hGintE : IntegrableOn (fun u : ℝ => Gfun β B μ i (u ^ 2)) (Ioc a' a) :=
    hGint'.mono_set (fun u hu => hu.1)
  have hsplit : ∫ u in Ioi a', Gfun β B μ i (u ^ 2) =
      (∫ u in Ioc a' a, Gfun β B μ i (u ^ 2)) + ∫ u in Ioi a, Gfun β B μ i (u ^ 2) := by
    rw [← setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi hGintE hGint,
      Set.Ioc_union_Ioi_eq_Ioi ha'a]
  rw [hsplit]
  set E := ∫ u in Ioc a' a, Gfun β B μ i (u ^ 2) with hE
  set J := ∫ u in Ioi a, Gfun β B μ i (u ^ 2) with hJ
  have hE0 : 0 ≤ E := setIntegral_nonneg measurableSet_Ioc (fun u hu =>
    (pg6p2_G_le μ hβ0 hβ1 hB hN hanti hpos i hM0 hMγ hc hcF hu.1).1)
  have hE1 : E ≤ a / c := by
    have h1 : E ≤ ∫ u in Ioc a' a, 1 / c :=
      setIntegral_mono_on hGintE (integrableOn_const (by simp)) measurableSet_Ioc (fun u hu => by
        have := (pg6p2_G_le μ hβ0 hβ1 hB hN hanti hpos i hM0 hMγ hc hcF hu.1).2
        refine this.trans ?_
        have hK : 0 < gammaOf N B * sPow β 2 * μ i := by positivity
        have : gammaOf N B * sPow β 2 * μ i / (u ^ 2 + gammaOf N B * sPow β 2 * μ i) ≤ 1 := by
          rw [div_le_one (by positivity)]; nlinarith [sq_nonneg u]
        calc 1 / c * _ ≤ 1 / c * 1 := mul_le_mul_of_nonneg_left this (by positivity)
          _ = 1 / c := mul_one _)
    refine h1.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le ha'a]
    rw [div_eq_mul_one_div a c]
    nlinarith [one_div_pos.2 hc]
  -- the bounds on J
  have hJbd : ∀ u ∈ Ioi a, _ := fun u hu =>
    pg6p2_G_two μ hβ0 hβ1 hB hN hanti hpos i hδ0 hδγ hε0 hε1 hFL hu
  set k := gammaOf N B * sPow β 2 * μ i with hk
  set k' := (gammaOf N B - δ) * ((1 - ε) * sPow β 2) * μ i with hk'
  have hk0 : 0 < k := by positivity
  have hk'0 : 0 < k' := by
    have : 0 < gammaOf N B - δ := by linarith
    positivity
  obtain ⟨hint1, hval1⟩ := pg6p2_arctan_int (k := k) (a := a) hk0
  obtain ⟨hint2, hval2⟩ := pg6p2_arctan_int (k := k') (a := a) hk'0
  have hJup : J ≤ 1 / ((1 - ε) * sPow β 2) * (Real.sqrt k * (Real.pi / 2)) := by
    have h1 : J ≤ ∫ u in Ioi a, 1 / ((1 - ε) * sPow β 2) * (k / (u ^ 2 + k)) :=
      setIntegral_mono_on hGint (hint1.const_mul _) measurableSet_Ioi (fun u hu => (hJbd u hu).2)
    rw [integral_const_mul, hval1] at h1
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    have : 0 ≤ Real.arctan (a / Real.sqrt k) :=
      Real.arctan_nonneg.2 (div_nonneg ha0 (Real.sqrt_nonneg _))
    nlinarith [Real.sqrt_nonneg k]
  have hJlo : (1 - ε) / sPow β 2 * (Real.sqrt k' * (Real.pi / 2 - Real.arctan (a / Real.sqrt k'))) ≤ J := by
    have h1 : ∫ u in Ioi a, (1 - ε) / sPow β 2 * (k' / (u ^ 2 + k')) ≤ J :=
      setIntegral_mono_on (hint2.const_mul _) hGint measurableSet_Ioi (fun u hu => (hJbd u hu).1)
    rw [integral_const_mul, hval2] at h1
    exact h1
  -- identities
  have hX : Real.sqrt k / (gammaOf N B * sPow β 2) = Real.sqrt (μ i / (gammaOf N B * sPow β 2)) :=
    pg6p2_S1 hγ hs2 hmu
  have hSle : sN β B μ δ ≤ gammaOf N B * δ / (Qm β δ * partLam B μ δ) := by
    unfold sN
    apply div_le_div_of_nonneg_right _ (by positivity)
    nlinarith
  have hA := pg6p2_S2a (g := gammaOf N B) (s := sPow β 2) (μ := μ i) (δ := δ) (Q := Qm β δ)
    (Λ := partLam B μ δ) hγ hs2 hmu hδ0 hQ hΛ hsδ.le hSle
  have hBb := pg6p2_S2b (g := gammaOf N B) (s := sPow β 2) (μ := μ i) (δ := δ) (Q := Qm β δ)
    (Λ := partLam B μ δ) (ε := ε) hγ hs2 hmu hδ0 hQ hΛ hsδ.le hSle h2δ hε0 hε1
  set X := Real.sqrt (μ i / (gammaOf N B * sPow β 2)) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  constructor
  · -- upper
    have hpg : 0 < Real.pi * gammaOf N B := by positivity
    have h1 : 2 / (Real.pi * gammaOf N B) * (E + J) ≤
        2 / (Real.pi * gammaOf N B) * (a / c + 1 / ((1 - ε) * sPow β 2) * (Real.sqrt k * (Real.pi / 2))) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine h1.trans ?_
    have e1 : 2 / (Real.pi * gammaOf N B) * (1 / ((1 - ε) * sPow β 2) * (Real.sqrt k * (Real.pi / 2))) =
        X * (1 / (1 - ε)) := by
      rw [← hX]
      field_simp
    have e2 : 2 / (Real.pi * gammaOf N B) * (a / c) = 2 / (Real.pi * c) * (a / gammaOf N B) := by
      field_simp
    have h3 : 2 / (Real.pi * c) * (a / gammaOf N B) ≤ 2 / (Real.pi * c) *
        (X * Real.sqrt (sPow β 2 * δ / (Qm β δ * (partLam B μ δ * μ i)))) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    rw [mul_add, e1, e2]
    calc _ ≤ X * (1 / (1 - ε)) + 2 / (Real.pi * c) *
          (X * Real.sqrt (sPow β 2 * δ / (Qm β δ * (partLam B μ δ * μ i)))) := by linarith
      _ = _ := by ring
  · -- lower
    have hpg : 0 < Real.pi * gammaOf N B := by positivity
    have h1 : 2 / (Real.pi * gammaOf N B) * J ≤ 2 / (Real.pi * gammaOf N B) * (E + J) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    refine le_trans ?_ h1
    have h2 : 2 / (Real.pi * gammaOf N B) * ((1 - ε) / sPow β 2 *
        (Real.sqrt k' * (Real.pi / 2 - Real.arctan (a / Real.sqrt k')))) ≤
        2 / (Real.pi * gammaOf N B) * J := mul_le_mul_of_nonneg_left hJlo (by positivity)
    refine le_trans ?_ h2
    -- k' = ρ k
    set ρ := (1 - δ / gammaOf N B) * (1 - ε) with hρ
    have hρ0 : 0 ≤ ρ := by
      have : δ / gammaOf N B ≤ 1 := by rw [div_le_one hγ]; linarith
      have : 0 ≤ 1 - δ / gammaOf N B := by linarith
      positivity
    have hk'ρ : k' = ρ * k := by
      rw [hk', hk, hρ]; field_simp
    have hsq : Real.sqrt k' = Real.sqrt ρ * Real.sqrt k := by
      rw [hk'ρ, Real.sqrt_mul hρ0]
    have hr : a / Real.sqrt k' ≤ Real.sqrt (2 * δ / (Qm β δ * ((1 - ε) * sPow β 2) *
        (partLam B μ δ * μ i))) := hBb
    have hr0 : 0 ≤ a / Real.sqrt k' := div_nonneg ha0 (Real.sqrt_nonneg _)
    set e2 := Real.sqrt (2 * δ / (Qm β δ * ((1 - ε) * sPow β 2) * (partLam B μ δ * μ i))) with he2
    have hat : Real.arctan (a / Real.sqrt k') ≤ e2 :=
      (Real.arctan_le_self hr0).trans hr
    have hpi : 2 / Real.pi * Real.arctan (a / Real.sqrt k') ≤ e2 := by
      have h2pi : 2 / Real.pi ≤ 1 := by
        rw [div_le_one Real.pi_pos]; linarith [Real.pi_gt_three]
      have hat0 : 0 ≤ Real.arctan (a / Real.sqrt k') := Real.arctan_nonneg.2 hr0
      calc 2 / Real.pi * Real.arctan (a / Real.sqrt k') ≤ 1 * Real.arctan (a / Real.sqrt k') :=
            mul_le_mul_of_nonneg_right h2pi hat0
        _ ≤ e2 := by linarith
    have e3 : 2 / (Real.pi * gammaOf N B) * ((1 - ε) / sPow β 2 *
        (Real.sqrt k' * (Real.pi / 2 - Real.arctan (a / Real.sqrt k')))) =
        (1 - ε) * Real.sqrt ρ * X * (1 - 2 / Real.pi * Real.arctan (a / Real.sqrt k')) := by
      rw [hsq, ← hX]
      field_simp
    rw [e3]
    have hsρ : 0 ≤ Real.sqrt ρ := Real.sqrt_nonneg _
    have : (1 - ε) * Real.sqrt ρ * X * (1 - e2) ≤
        (1 - ε) * Real.sqrt ρ * X * (1 - 2 / Real.pi * Real.arctan (a / Real.sqrt k')) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith [this]

private lemma pg6p2_sqrt_small {A Q z θ : ℝ} (hA : 0 ≤ A) (hQ : 0 < Q) (hθ : 0 < θ)
    (hz0 : 0 < z) (hz : A / (Q * θ ^ 2) ≤ z) : Real.sqrt (A / (Q * z)) ≤ θ := by
  refine Real.sqrt_le_iff.2 ⟨hθ.le, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  have := (div_le_iff₀ (by positivity : 0 < Q * θ ^ 2)).1 hz
  calc A ≤ z * (Q * θ ^ 2) := this
    _ = θ ^ 2 * (Q * z) := by ring

private lemma pg6p2_prod3 {a b c : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : a + b + c - 2 ≤ a * b * c := by
  nlinarith [mul_nonneg ha0 hb0, mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1),
    mul_nonneg (mul_nonneg (sub_nonneg.2 ha1) (sub_nonneg.2 hb1)) hc0,
    mul_nonneg (sub_nonneg.2 hc1) (sub_nonneg.2 (mul_le_one₀ ha1 hb0 hb1)),
    mul_nonneg ha0 hb0]

private lemma pg6p2_final {P X η e0 q e2 t : ℝ} (hX : 0 ≤ X) (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hηe : η ≤ e0) (hq0 : 0 ≤ q) (hq : q ≤ η / 8) (he20 : 0 ≤ e2) (he2 : e2 ≤ η / 8)
    (ht : t ≤ η / 8) (hup : P ≤ X * (1 / (1 - η / 8) + t))
    (hlo : X * ((1 - η / 8) * Real.sqrt ((1 - q) * (1 - η / 8)) * (1 - e2)) ≤ P) :
    |P - X| ≤ e0 * X := by
  have hε1 : 0 < 1 - η / 8 := by linarith
  have hε2 : 1 / (1 - η / 8) ≤ 1 + 2 * (η / 8) := by
    rw [div_le_iff₀ hε1]
    nlinarith [sq_nonneg η]
  have hρ0 : 0 ≤ (1 - q) * (1 - η / 8) := by
    have : 0 ≤ 1 - q := by linarith
    positivity
  have hρ1 : (1 - q) * (1 - η / 8) ≤ 1 := by
    have : 0 ≤ 1 - q := by linarith
    nlinarith
  have hsq : (1 - q) * (1 - η / 8) ≤ Real.sqrt ((1 - q) * (1 - η / 8)) :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 ≤ 1 - e2 := by linarith
  have hprod : (1 - η / 8) * ((1 - q) * (1 - η / 8)) * (1 - e2) ≤
      (1 - η / 8) * Real.sqrt ((1 - q) * (1 - η / 8)) * (1 - e2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hε1.le) hs0
  have h3 := pg6p2_prod3 (a := (1 - η / 8) * (1 - η / 8)) (b := 1 - q) (c := 1 - e2)
    (by positivity) (by nlinarith) (by linarith) (by linarith) hs0 (by linarith)
  have hfin : 1 - η ≤ (1 - η / 8) * Real.sqrt ((1 - q) * (1 - η / 8)) * (1 - e2) := by
    have e : (1 - η / 8) * ((1 - q) * (1 - η / 8)) * (1 - e2) =
        (1 - η / 8) * (1 - η / 8) * (1 - q) * (1 - e2) := by ring
    rw [e] at hprod
    nlinarith
  have hlo' : (1 - η) * X ≤ P := le_trans (mul_le_mul_of_nonneg_right hfin hX) (by linarith)
  have hup' : P ≤ X * (1 + 3 * η / 8) := by
    refine hup.trans (mul_le_mul_of_nonneg_left ?_ hX)
    linarith
  have hηX : η * X ≤ e0 * X := mul_le_mul_of_nonneg_right hηe hX
  rw [abs_le]
  constructor <;> nlinarith

/-- `lem:app-pl-head`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Head]\label{lem:app-pl-head}
For every fixed $M>0$ and all large $N$, $\sqrt2\,\mathfrak d_i^{\le M}\le C_M\sqrt{\mu_i/\gamma}$ for
every $i$. If a row sequence satisfies $m_N(1/\mu_i)\to0$, then
$\sqrt2\,\mathfrak d_i^{\le M}\sim\sqrt{\mu_i/(\gamma\sw2)}$.
\end{lemma}
-/
theorem lem_app_pl_head_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (M : ℝ) (hM : 0 < M) (i : (n : ℕ) → Fin (N n))
    (hrow : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M)
      (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) := by
  have hβ0 := hreg.hβ0
  have hβ1 := hreg.hβ1
  have hα := hreg.hα
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  obtain ⟨cM, hcM, hcF⟩ := pg6p2_F_lower hβ0 hβ1 hM
  rw [IsEquivalent, isLittleO_iff]
  intro e0 he0
  set η : ℝ := min e0 1 with hη
  have hη0 : 0 < η := lt_min he0 one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hηε : η ≤ e0 := min_le_left _ _
  set ε : ℝ := η / 8 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by rw [hε]; linarith
  obtain ⟨δ0, hδ0, hFL0⟩ := pg6p2_FL_eps hβ0 hβ1 hε0
  set δ : ℝ := min δ0 M with hδdef
  have hδpos : 0 < δ := lt_min hδ0 hM
  have hδM : δ ≤ M := min_le_right _ _
  have hFL : ∀ m ∈ Ioc (0:ℝ) δ, (1 - ε) * sPow β 2 ≤ Fw (emaW β) (Qm β m) ∧
      1 - ε ≤ Lw (emaW β) (Qm β m) := fun m hm =>
    hFL0 m ⟨hm.1, hm.2.trans (min_le_left _ _)⟩
  set Q : ℝ := Qm β δ with hQdef
  have hQ : 0 < Q := (pg6_Qm_spec hβ0 hβ1 hδpos).1
  have hε1m : 0 < 1 - ε := by linarith
  set θ1 : ℝ := η * Real.pi * cM / 16 with hθ1
  have hθ1pos : 0 < θ1 := by positivity
  set θ2 : ℝ := η / 8 with hθ2
  have hθ2pos : 0 < θ2 := by positivity
  set L : ℝ := max 1 (max (sPow β 2 * δ / (Q * θ1 ^ 2))
    (2 * δ / (Q * ((1 - ε) * sPow β 2) * θ2 ^ 2))) with hL
  have hL1 : 1 ≤ L := le_max_left _ _
  have hL0 : 0 < L := by linarith
  have h1 : ∀ᶠ n in atTop, M < gammaOf (N n) (B n) := hreg.hγ.eventually_gt_atTop M
  have h2 : ∀ᶠ n in atTop, 2 * δ ≤ gammaOf (N n) (B n) := hreg.hγ.eventually_ge_atTop (2 * δ)
  have h3 : ∀ᶠ n in atTop, 8 * δ / η ≤ gammaOf (N n) (B n) := hreg.hγ.eventually_ge_atTop _
  have h4 := hrow.eventually (Iio_mem_nhds (show (0:ℝ) < δ / L by positivity))
  filter_upwards [h1, h2, h3, h4] with n hn1 hn2 hn3 hn4
  have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
  have hanti := pg6_plSpec_anti (α := α) hα (hreg.hcpos n) (N := N n)
  have hpos := fun j => pg6_plSpec_pos (α := α) (hreg.hcpos n) (N := N n) j
  have hδγ : δ < gammaOf (N n) (B n) := by linarith
  have hz := pg6p2_z_gt (plSpec α (c n) (N n)) (hreg.hBpos n) (hreg.hNpos n) hpos (i n)
    (δ := δ) (L := L) ⟨hδpos, hδγ⟩ hL1 hn4
  obtain ⟨hup, hlo⟩ := pg6p2_head_two (plSpec α (c n) (N n)) hβ0 hβ1 (hreg.hBpos n) (hreg.hNpos n)
    hanti hpos (i n) hδpos hδM hn1 hn2 hcM hcF hε0 hε1 hFL
  set μ := plSpec α (c n) (N n) (i n) with hμ
  have hmu : 0 < μ := hpos (i n)
  set γ := gammaOf (N n) (B n) with hγdef
  set z := partLam (B n) (plSpec α (c n) (N n)) δ * μ with hzdef
  have hz0 : 0 < z := by linarith
  set X := Real.sqrt (μ / (γ * sPow β 2)) with hXdef
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have he1 : Real.sqrt (sPow β 2 * δ / (Q * z)) ≤ θ1 := by
    refine pg6p2_sqrt_small (by positivity) hQ hθ1pos hz0 ?_
    have : sPow β 2 * δ / (Q * θ1 ^ 2) ≤ L := (le_max_left _ _).trans (le_max_right _ _)
    linarith
  have he2 : Real.sqrt (2 * δ / (Q * ((1 - ε) * sPow β 2) * z)) ≤ θ2 := by
    refine pg6p2_sqrt_small (by positivity) (by positivity) hθ2pos hz0 ?_
    have : 2 * δ / (Q * ((1 - ε) * sPow β 2) * θ2 ^ 2) ≤ L :=
      (le_max_right _ _).trans (le_max_right _ _)
    linarith
  have hδγ' : δ / γ ≤ η / 8 := by
    rw [div_le_iff₀ hγ]
    rw [div_le_iff₀ hη0] at hn3
    nlinarith
  have hδγ0 : 0 ≤ δ / γ := by positivity
  have hc2 : 2 / (Real.pi * cM) * Real.sqrt (sPow β 2 * δ / (Q * z)) ≤ η / 8 := by
    have h5 : 2 / (Real.pi * cM) * Real.sqrt (sPow β 2 * δ / (Q * z)) ≤ 2 / (Real.pi * cM) * θ1 :=
      mul_le_mul_of_nonneg_left he1 (by positivity)
    have h6 : 2 / (Real.pi * cM) * θ1 = η / 8 := by
      rw [hθ1]; field_simp <;> ring
    linarith
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  rw [abs_of_nonneg hX0]
  exact pg6p2_final (P := sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M) (X := X) (η := η)
    (e0 := e0) hX0 hη0 hη1 hηε hδγ0 hδγ' (Real.sqrt_nonneg _) he2 hc2 hup hlo

/-! #### P-G.6.P2: the tail. Regularity of `𝓑_i` -/

private lemma pg6p2_Lam_hasDeriv {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partLam B μ m ∧ HasDerivAt (partLam B μ) (deriv (partLam B μ) m) m := by
  obtain ⟨-, hb2, -, hcd⟩ := def_app_pl_participation_bij μ hB hN hpos
  refine ⟨hb2.mapsTo hm, ?_⟩
  have hca := hcd.contDiffAt (Ioo_mem_nhds hm.1 hm.2)
  exact (hca.differentiableAt (by simp)).hasDerivAt

private lemma pg6p2_W_deriv {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    0 < partBfun B μ i m ∧
    HasDerivAt (partBfun B μ i)
      (partBfun B μ i m * (-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) +
        (1 / 2 - partF B μ i m) * (deriv (partLam B μ) m / partLam B μ m))) m := by
  obtain ⟨hL, hLd⟩ := pg6p2_Lam_hasDeriv μ hB hN hpos hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  have hmu := hpos i
  set L := partLam B μ m with hLdef
  set L' := deriv (partLam B μ) m with hL'def
  set γ := gammaOf N B with hγ
  have hden : 0 < m * L := mul_pos hm0 hL
  set u := (γ - m) / (m * L) with hu
  have hu0 : 0 < u := div_pos hgm hden
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu0
  have hsq : Real.sqrt u * Real.sqrt u = u := Real.mul_self_sqrt hu0.le
  have hfL : 0 < 1 + L * μ i := by have := mul_pos hL hmu; linarith
  -- derivatives
  have hd1 : HasDerivAt (fun y : ℝ => γ - y) (-1) m := by
    simpa using (hasDerivAt_id m).const_sub γ
  have hd2 : HasDerivAt (fun y : ℝ => y * partLam B μ y) (L + m * L') m := by
    exact ((hasDerivAt_id' m).mul hLd).congr_deriv (by ring)
  have hdu : HasDerivAt (fun y : ℝ => (γ - y) / (y * partLam B μ y))
      ((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) m := hd1.div hd2 hden.ne'
  have hds : HasDerivAt (fun y : ℝ => Real.sqrt ((γ - y) / (y * partLam B μ y)))
      (((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) / (2 * Real.sqrt u)) m :=
    hdu.sqrt hu0.ne'
  have hdf : HasDerivAt (fun y : ℝ => partLam B μ y * μ i / (1 + partLam B μ y * μ i))
      ((L' * μ i * (1 + L * μ i) - L * μ i * (L' * μ i)) / (1 + L * μ i) ^ 2) m := by
    have h1 : HasDerivAt (fun y : ℝ => partLam B μ y * μ i) (L' * μ i) m := hLd.mul_const _
    have h2 : HasDerivAt (fun y : ℝ => 1 + partLam B μ y * μ i) (L' * μ i) m := h1.const_add 1
    exact h1.div h2 hfL.ne'
  have hW : HasDerivAt (partBfun B μ i)
      ((((-1 * (m * L) - (γ - m) * (L + m * L')) / (m * L) ^ 2) / (2 * Real.sqrt u)) *
          (L * μ i / (1 + L * μ i)) +
        Real.sqrt u * ((L' * μ i * (1 + L * μ i) - L * μ i * (L' * μ i)) / (1 + L * μ i) ^ 2)) m :=
    hds.mul hdf
  have hWm : partBfun B μ i m = Real.sqrt u * (L * μ i / (1 + L * μ i)) := rfl
  have hfpos : 0 < L * μ i / (1 + L * μ i) := div_pos (mul_pos hL hmu) hfL
  refine ⟨by rw [hWm]; positivity, ?_⟩
  refine hW.congr_deriv ?_
  have hF : partF B μ i m = L * μ i / (1 + L * μ i) := rfl
  rw [hWm, hF]
  have hm0' : m ≠ 0 := hm0.ne'
  have hL0 : L ≠ 0 := hL.ne'
  have hg0 : γ - m ≠ 0 := hgm.ne'
  have hs0 : Real.sqrt u ≠ 0 := hsu.ne'
  have hfL0 : 1 + L * μ i ≠ 0 := hfL.ne'
  have hsq2 : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu0.le
  field_simp
  rw [hsq2, hu]
  field_simp
  ring

private lemma pg6p2_W_facts {α : ℝ} (hα : 0 < α) :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → ∀ i : Fin N,
      ∀ m ∈ Ioo 0 (gammaOf N B),
        0 < partBfun B (plSpec α c N) i m ∧
        HasDerivAt (partBfun B (plSpec α c N) i)
          (deriv (partBfun B (plSpec α c N) i) m) m ∧
        |deriv (partBfun B (plSpec α c N) i) m| ≤
          C4 * partBfun B (plSpec α c N) i m * (1 / m + 1 / (gammaOf N B - m)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  refine ⟨1 / 2 + 1 / (2 * cα), by positivity, fun N B c hN hB hc i m hm => ?_⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => pg6_plSpec_pos hc j
  obtain ⟨hW0, hWd⟩ := pg6p2_W_deriv (plSpec α c N) hB hN hpos i hm
  refine ⟨hW0, hWd.differentiableAt.hasDerivAt, ?_⟩
  rw [hWd.deriv]
  obtain ⟨-, hlam⟩ := (hel N B c hN hB hc)
  obtain ⟨hl1, hl2⟩ := hlam m hm
  obtain ⟨hL, -⟩ := pg6p2_Lam_hasDeriv (plSpec α c N) hB hN hpos hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  set W := partBfun B (plSpec α c N) i m with hWdef
  set r := deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m with hr
  set f := partF B (plSpec α c N) i m with hf
  have hf0 : 0 < f := by
    rw [hf]; unfold partF
    have := hpos i
    positivity
  have hf1 : f < 1 := by
    rw [hf]; unfold partF
    have := mul_pos hL (hpos i)
    rw [div_lt_one (by linarith)]
    linarith
  have hr0 : 0 ≤ r := by
    have : 0 < 1 / m := by positivity
    linarith
  have hrb : r ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) := hl2
  have e1 : 0 < 1 / (2 * (gammaOf N B - m)) := by positivity
  have e2 : 0 < 1 / (2 * m) := by positivity
  have h3 : |(1 / 2 - f) * r| ≤ r / 2 := by
    rw [abs_mul, abs_of_nonneg hr0]
    have : |1 / 2 - f| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
    nlinarith
  have habs : |-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) + (1 / 2 - f) * r| ≤
      1 / (2 * (gammaOf N B - m)) + 1 / (2 * m) + r / 2 := by
    have := abs_le.1 h3
    rw [abs_le]
    constructor <;> linarith
  rw [abs_mul, abs_of_pos hW0]
  have hb : 1 / (2 * (gammaOf N B - m)) + 1 / (2 * m) + r / 2 ≤
      (1 / 2 + 1 / (2 * cα)) * (1 / m + 1 / (gammaOf N B - m)) := by
    have h1 : 1 / (2 * (gammaOf N B - m)) = 1 / 2 * (1 / (gammaOf N B - m)) := by
      rw [one_div_mul_one_div]
    have h2 : 1 / (2 * m) = 1 / 2 * (1 / m) := by rw [one_div_mul_one_div]
    rw [h1, h2]
    have h4 : r / 2 ≤ 1 / (2 * cα) * (1 / m + 1 / (gammaOf N B - m)) := by
      have : r / 2 ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) / 2 := by linarith
      calc r / 2 ≤ _ := this
        _ = 1 / (2 * cα) * (1 / m + 1 / (gammaOf N B - m)) := by field_simp
    nlinarith
  calc W * |-(1 / (2 * (gammaOf N B - m))) - 1 / (2 * m) + (1 / 2 - f) * r| ≤
        W * ((1 / 2 + 1 / (2 * cα)) * (1 / m + 1 / (gammaOf N B - m))) :=
        mul_le_mul_of_nonneg_left (habs.trans hb) hW0.le
    _ = _ := by ring

private lemma pg6p2_Phi_bounds {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ C3 : ℝ, 0 < C3 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c →
      ∀ m ∈ Ioo 0 (gammaOf N B),
        1 ≤ Efun β m * thetaN β B (plSpec α c N) m ∧
        Efun β m * thetaN β B (plSpec α c N) m ≤
          1 + C3 * (1 / m + 1 / (gammaOf N B - m)) := by
  obtain ⟨cα, hcα, hel⟩ := lem_app_pl_elasticity_i hα
  obtain ⟨C2, hC2⟩ := lem_app_pl_elasticity_ii hα hβ0 hβ1
  obtain ⟨cE, CE, hcE, hcCE, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  have hCE : 0 < CE := lt_of_lt_of_le hcE hcCE
  refine ⟨CE * (1 / cα + 1), by positivity, fun N B c hN hB hc m hm => ?_⟩
  refine ⟨(hC2 N B c hN hB hc m hm).2, ?_⟩
  obtain ⟨-, hlam⟩ := (hel N B c hN hB hc)
  obtain ⟨hl1, hl2⟩ := hlam m hm
  obtain ⟨hm0, hmg⟩ := hm
  have hgm : 0 < gammaOf N B - m := sub_pos.2 hmg
  obtain ⟨-, hE2⟩ := hE m hm0
  have hEC : Efun β m ≤ CE := hE2.trans (mul_le_of_le_one_right hCE.le (min_le_right _ _))
  have hEpos : 0 < Efun β m := by
    have := hE m hm0
    have h1 : 0 < cE * min m 1 := mul_pos hcE (lt_min hm0 one_pos)
    linarith [this.1]
  set r := deriv (partLam B (plSpec α c N)) m / partLam B (plSpec α c N) m with hr
  have hrb : r ≤ (1 / cα) * (1 / m + 1 / (gammaOf N B - m)) := hl2
  have hkey : Efun β m * thetaN β B (plSpec α c N) m =
      1 + Efun β m * (r - 1 / m + 1 / (gammaOf N B - m)) := by
    unfold thetaN
    rw [← hr]
    field_simp
    ring
  rw [hkey]
  have hS : 0 < 1 / m + 1 / (gammaOf N B - m) := by positivity
  have h1 : r - 1 / m + 1 / (gammaOf N B - m) ≤ (1 / cα + 1) * (1 / m + 1 / (gammaOf N B - m)) := by
    have : 0 < 1 / m := by positivity
    have : 0 ≤ 1 / (gammaOf N B - m) := by positivity
    nlinarith
  have hnn : 0 ≤ (r - 1 / m + 1 / (gammaOf N B - m)) := by
    have : 1 / m ≤ r := hl1
    have : 0 ≤ 1 / (gammaOf N B - m) := by positivity
    linarith
  have h2 : Efun β m * (r - 1 / m + 1 / (gammaOf N B - m)) ≤
      CE * ((1 / cα + 1) * (1 / m + 1 / (gammaOf N B - m))) :=
    mul_le_mul hEC h1 hnn hCE.le
  linarith [h2]

private lemma pg6p2_exp_le {L : ℝ} (hL0 : 0 ≤ L) (hL1 : L ≤ 1) : Real.exp L ≤ (1 + L) ^ 2 := by
  rcases hL0.eq_or_lt with h | h
  · rw [← h]; simp
  have hx : L / 2 < 1 := by linarith
  have h1 := Real.exp_bound_div_one_sub_of_interval' (by linarith : 0 < L / 2) hx
  have h2 : 1 / (1 - L / 2) ≤ 1 + L := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : Real.exp L = Real.exp (L / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [h3]
  have := Real.exp_pos (L / 2)
  exact pow_le_pow_left₀ this.le (h1.le.trans h2) 2

private lemma pg6p2_sqrt_ratio {r L : ℝ} (hr : 0 < r) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (hlog : |Real.log r| ≤ L) : Real.sqrt r ≤ 1 + L ∧ 1 / Real.sqrt r ≤ 1 + L := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hsq : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hup : r ≤ Real.exp L := by
    have := (abs_le.1 hlog).2
    calc r = Real.exp (Real.log r) := (Real.exp_log hr).symm
      _ ≤ Real.exp L := Real.exp_le_exp.2 this
  have hlo : Real.exp (-L) ≤ r := by
    have := (abs_le.1 hlog).1
    calc Real.exp (-L) ≤ Real.exp (Real.log r) := Real.exp_le_exp.2 this
      _ = r := Real.exp_log hr
  have hE := pg6p2_exp_le hL0 hL1
  constructor
  · by_contra hnot
    push_neg at hnot
    have : (1 + L) ^ 2 < Real.sqrt r ^ 2 := by
      exact pow_lt_pow_left₀ hnot (by linarith) two_ne_zero
    rw [hsq] at this
    linarith
  · rw [div_le_iff₀ hs]
    by_contra hnot
    push_neg at hnot
    have h1 : 0 < 1 + L := by linarith
    -- 1 > (1+L) s  ⇒ r < 1/(1+L)^2 ≤ exp(-L)
    have h2 : (1 + L) ^ 2 * r < 1 := by
      have : ((1 + L) * Real.sqrt r) ^ 2 < 1 := by
        have h0 : 0 ≤ (1 + L) * Real.sqrt r := by positivity
        nlinarith
      nlinarith [hsq]
    have h3 : Real.exp L * Real.exp (-L) = 1 := by rw [← Real.exp_add]; simp
    have h4 : (1 + L) ^ 2 * Real.exp (-L) ≥ 1 := by
      have hpos : 0 < Real.exp (-L) := Real.exp_pos _
      nlinarith [mul_le_mul_of_nonneg_right hE hpos.le]
    nlinarith [mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ) ≤ (1 + L) ^ 2)]

private lemma pg6p2_g_ratio {V V' y q L : ℝ} (hV : 0 < V) (hV' : 0 < V') (hy : 0 ≤ y) (hq : 0 ≤ q)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hlog : |Real.log (V / V')| ≤ L) :
    |Real.sqrt (q / V) * (V / (V + y)) - Real.sqrt (q / V') * (V' / (V' + y))| ≤
      L * (Real.sqrt (q / V') * (V' / (V' + y))) := by
  set r := V / V' with hr
  have hr0 : 0 < r := div_pos hV hV'
  have hVr : V = r * V' := by rw [hr]; field_simp
  obtain ⟨hs1, hs2⟩ := pg6p2_sqrt_ratio hr0 hL0 hL1 hlog
  set s := Real.sqrt r with hs
  have hs0 : 0 < s := Real.sqrt_pos.2 hr0
  have hss : s ^ 2 = r := Real.sq_sqrt hr0.le
  set G := Real.sqrt (q / V') * (V' / (V' + y)) with hG
  have hG0 : 0 ≤ G := by positivity
  have hgV : Real.sqrt (q / V) * (V / (V + y)) = G * (s * (V' + y) / (s ^ 2 * V' + y)) := by
    have e1 : Real.sqrt (q / V) = Real.sqrt (q / V') / s := by
      rw [hVr, mul_comm, ← div_div, Real.sqrt_div (by positivity)]
    rw [e1, hG, hVr, ← hss]
    have : 0 < V' + y := by linarith
    have : 0 < s ^ 2 * V' + y := by positivity
    have : 0 < s := hs0
    field_simp
  set ρ := s * (V' + y) / (s ^ 2 * V' + y) with hρ
  have hden : 0 < s ^ 2 * V' + y := by positivity
  have hden2 : 0 < V' + y := by linarith
  have hρup : ρ ≤ 1 + L := by
    rcases le_total 1 s with h | h
    · have : ρ ≤ s := by
        rw [hρ, div_le_iff₀ hden]
        nlinarith [mul_nonneg hV'.le (sub_nonneg.2 (one_le_pow₀ h : (1:ℝ) ≤ s ^ 2)), hs0]
      linarith
    · have : ρ ≤ 1 / s := by
        rw [hρ, div_le_div_iff₀ hden hs0]
        nlinarith [mul_nonneg hy (sub_nonneg.2 (pow_le_one₀ hs0.le h : s ^ 2 ≤ 1)), hs0]
      linarith
  have hρlo : 1 - L ≤ ρ := by
    have h1 : 1 / (1 + L) ≤ s := by
      rw [div_le_iff₀ (by linarith)]
      rw [div_le_iff₀ hs0] at hs2
      linarith
    have h2 : 1 / (1 + L) ≤ 1 / s := by
      apply one_div_le_one_div_of_le hs0 hs1
    have h3 : 1 / (1 + L) ≤ ρ := by
      rcases le_total 1 s with h | h
      · have : 1 / s ≤ ρ := by
          rw [hρ, div_le_div_iff₀ hs0 hden]
          nlinarith [mul_nonneg hy (sub_nonneg.2 (one_le_pow₀ h : (1:ℝ) ≤ s ^ 2)), hs0]
        linarith
      · have : s ≤ ρ := by
          rw [hρ, le_div_iff₀ hden]
          nlinarith [mul_nonneg hV'.le (sub_nonneg.2 (pow_le_one₀ hs0.le h : s ^ 2 ≤ 1)), hs0]
        linarith
    have h4 : 1 - L ≤ 1 / (1 + L) := by
      rw [le_div_iff₀ (by linarith)]
      nlinarith
    linarith
  rw [hgV]
  have e : G * ρ - G = G * (ρ - 1) := by ring
  rw [e, abs_mul, abs_of_nonneg hG0]
  have : |ρ - 1| ≤ L := by rw [abs_le]; constructor <;> linarith
  nlinarith

private lemma pg6p2_finV_pos {α : ℝ} {N B : ℕ} (c : ℝ) (hN : 0 < N) (hB : 0 < B) (hc : 0 < c)
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : 0 < finV α N p := by
  have hNr : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hBr : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB
  have hγ : 0 < gammaOf N B := by unfold gammaOf; exact div_pos hNr hBr
  have hγp : 0 < gammaOf N B * p := mul_pos hγ hp0
  have hmI : gammaOf N B * p ∈ Ioo 0 (gammaOf N B) := ⟨hγp, by nlinarith⟩
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => pg6_plSpec_pos hc j
  have hLpos : 0 < partLam B (plSpec α c N) (gammaOf N B * p) :=
    (def_app_pl_participation_bij (plSpec α c N) hB hN hpos).2.1.mapsTo hmI
  have hLV := eqn_app_pl_Lambda_V (N := N) (B := B) α c hN hB hc hmI
  rw [mul_div_cancel_left₀ p hγ.ne'] at hLV
  have hNα : 0 < (N:ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have h1 : 0 < (N:ℝ) ^ α / c * finV α N p := hLV ▸ hLpos
  exact pos_of_mul_pos_right h1 (div_pos hNα hc).le

private lemma pg6p2_rowNum_le {N : ℕ} (i : Fin N) : rowNum i ≤ (N : ℝ) := by
  unfold rowNum
  have : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  exact this

private lemma pg6p2_aN_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) : 0 < aN α c N := by
  unfold aN
  have : (0:ℝ) < N := by exact_mod_cast hN
  positivity

private lemma pg6p2_contV_pos {α : ℝ} (hα : 0 < α) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p := by
  have hex : ∃ V, V ∈ Ioi (0:ℝ) ∧ contS α V = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact Function.invFunOn_mem hex

private lemma pg6p2_W_cont {α : ℝ} (hα : 0 < α) {N B : ℕ} {c : ℝ} (hN : 0 < N) (hB : 0 < B)
    (hc : 0 < c) (i : Fin N) :
    ContinuousOn (partBfun B (plSpec α c N) i) (Ioo 0 (gammaOf N B)) := by
  obtain ⟨C4, hC4, hW⟩ := pg6p2_W_facts hα
  intro m hm
  exact (hW N B c hN hB hc i m hm).2.1.continuousAt.continuousWithinAt

/-- Comparison of the finite-`N` and continuum participation profiles, as integrals. -/
private lemma pg6p2_S5 {α : ℝ} (hα : 0 < α) :
    ∃ C5 : ℝ, 0 < C5 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 2 ≤ B → 0 < c → 1 ≤ M →
      2 * M ≤ gammaOf N B → C5 ≤ (B : ℝ) * M →
      (1 - C5 / ((B : ℝ) * M)) *
          ∫ p in (M / gammaOf N B)..(1 - M / gammaOf N B),
            Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p ≤
        (1 / (gammaOf N B * aN α c N)) *
          ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m ∧
      (1 / (gammaOf N B * aN α c N)) *
          ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m ≤
        (1 + C5 / ((B : ℝ) * M)) *
          ∫ p in (M / gammaOf N B)..(1 - M / gammaOf N B),
            Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p := by
  obtain ⟨C, hC⟩ := lem_app_pl_finite_inverse_ii hα
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun N B c i M hN hB hc hM h2M hCBM => ?_⟩
  set γ := gammaOf N B with hγ
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast (by omega : 0 < B)
  have hγ0 : 0 < γ := by rw [hγ]; unfold gammaOf; positivity
  have hM0 : 0 < M := by linarith
  have han : 0 < aN α c N := pg6p2_aN_pos hc hN
  set C5 := max C 1 with hC5
  set L := C5 / ((B : ℝ) * M) with hL
  have hBM : 0 < (B : ℝ) * M := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L ≤ 1 := by rw [hL, div_le_one hBM]; exact hCBM
  have ha : 0 < M / γ := by positivity
  have hab : M / γ ≤ 1 - M / γ := by
    have : M / γ ≤ 1 / 2 := by rw [div_le_iff₀ hγ0]; linarith
    linarith
  have hb1 : 1 - M / γ < 1 := by linarith
  set y := (rowNum i / (N : ℝ)) ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (div_nonneg (pg6_rowNum_pos i).le hNr.le) _
  -- pointwise
  have hpt : ∀ p ∈ Icc (M / γ) (1 - M / γ),
      (1 - L) * (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) ≤
        partBfun B (plSpec α c N) i (γ * p) / aN α c N ∧
      partBfun B (plSpec α c N) i (γ * p) / aN α c N ≤
        (1 + L) * (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) := by
    intro p hp
    have hp0 : 0 < p := lt_of_lt_of_le ha hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    have hbulk := eqn_app_pl_Bi_bulk hα c hN (by omega : 0 < B) hc i hp0 hp1
    rw [show ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) = rowNum i / (N : ℝ) from rfl, ← hy] at hbulk
    have hVN : 0 < finV α N p := pg6p2_finV_pos c hN (by omega) hc hp0 hp1
    have hVC : 0 < contV α p := pg6p2_contV_pos hα ⟨hp0, hp1⟩
    have hlog := hC N B M p hN hB hM hp.1 hp.2
    have hlog' : |Real.log (finV α N p / contV α p)| ≤ L := by
      refine hlog.trans ?_
      rw [hL]
      exact div_le_div_of_nonneg_right (le_max_left _ _) hBM.le
    have hq : 0 ≤ (1 - p) / p := div_nonneg (by linarith) hp0.le
    have hrat := pg6p2_g_ratio (V := finV α N p) (V' := contV α p) (y := y) (q := (1 - p) / p) hVN hVC
      hy0 hq hL0 hL1 hlog'
    have e1 : ∀ V : ℝ, Real.sqrt ((1 - p) / (p * V)) = Real.sqrt ((1 - p) / p / V) := fun V => by
      rw [div_div]
    have hW : partBfun B (plSpec α c N) i (γ * p) / aN α c N =
        Real.sqrt ((1 - p) / p / finV α N p) * (finV α N p / (finV α N p + y)) := by
      rw [hbulk, e1]
      field_simp
    rw [hW]
    have hprof : profF α (rowNum i / (N : ℝ)) p = contV α p / (contV α p + y) := rfl
    rw [hprof, e1]
    have := abs_le.1 hrat
    constructor <;> nlinarith [this.1, this.2]
  -- integrals
  have hx01 : rowNum i / (N : ℝ) ∈ Ioc (0:ℝ) 1 :=
    ⟨div_pos (pg6_rowNum_pos i) hNr, (div_le_one hNr).2 (pg6p2_rowNum_le i)⟩
  have hGint : IntervalIntegrable
      (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p)
      volume (M / γ) (1 - M / γ) := by
    refine (lem_app_pl_Psi_i_integrable hα _ hx01).mono_set ?_
    rw [uIcc_of_le zero_le_one, uIcc_of_le hab]
    exact Icc_subset_Icc ha.le (by linarith)
  have hWcont : ContinuousOn (fun p : ℝ => partBfun B (plSpec α c N) i (γ * p) / aN α c N)
      (Icc (M / γ) (1 - M / γ)) := by
    have h1 := pg6p2_W_cont hα hN (by omega : 0 < B) hc i
    refine ContinuousOn.div_const (h1.comp (continuousOn_const.mul continuousOn_id) ?_) _
    intro p hp
    have hp0 : 0 < p := lt_of_lt_of_le ha hp.1
    have hp1 : p < 1 := lt_of_le_of_lt hp.2 hb1
    refine ⟨mul_pos hγ0 hp0, ?_⟩
    show gammaOf N B * p < gammaOf N B
    nlinarith
  have hWint : IntervalIntegrable (fun p : ℝ => partBfun B (plSpec α c N) i (γ * p) / aN α c N)
      volume (M / γ) (1 - M / γ) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hWcont
  -- change of variables
  have hcomp : ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) =
      γ⁻¹ * ∫ m in M..(γ - M), partBfun B (plSpec α c N) i m := by
    have := intervalIntegral.integral_comp_mul_left (a := M / γ) (b := 1 - M / γ)
      (fun m => partBfun B (plSpec α c N) i m) hγ0.ne'
    rw [this]
    have e1 : γ * (M / γ) = M := by field_simp
    have e2 : γ * (1 - M / γ) = γ - M := by field_simp
    rw [e1, e2, smul_eq_mul]
  have hWeq : ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) / aN α c N =
      (1 / (γ * aN α c N)) * ∫ m in M..(γ - M), partBfun B (plSpec α c N) i m := by
    rw [intervalIntegral.integral_div, hcomp]
    field_simp
  rw [← hWeq]
  constructor
  · calc (1 - L) * ∫ p in (M / γ)..(1 - M / γ),
          Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p
        = ∫ p in (M / γ)..(1 - M / γ), (1 - L) *
          (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) := by
            rw [intervalIntegral.integral_const_mul]
      _ ≤ _ := intervalIntegral.integral_mono_on hab (hGint.const_mul _) hWint
            (fun p hp => (hpt p hp).1)
  · calc ∫ p in (M / γ)..(1 - M / γ), partBfun B (plSpec α c N) i (γ * p) / aN α c N
        ≤ ∫ p in (M / γ)..(1 - M / γ), (1 + L) *
          (Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p) :=
            intervalIntegral.integral_mono_on hab hWint (hGint.const_mul _)
              (fun p hp => (hpt p hp).2)
      _ = _ := by rw [intervalIntegral.integral_const_mul]

private lemma pg6p2_W_top {α : ℝ} (hα : 0 < α) :
    ∃ K6 : ℝ, 0 < K6 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N), 0 < N → 0 < B → 0 < c →
      ∀ m : ℝ, gammaOf N B / 2 ≤ m → m < gammaOf N B →
        partBfun B (plSpec α c N) i m ≤ K6 * aN α c N * ((gammaOf N B - m) / gammaOf N B) := by
  obtain ⟨c3, C3, hc3, hC3, h3⟩ := lem_app_pl_finite_inverse_iii hα
  refine ⟨Real.sqrt (2 / c3), by positivity, fun N B c i hN hB hc m hm1 hm2 => ?_⟩
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hBr : (0:ℝ) < B := by exact_mod_cast hB
  set γ := gammaOf N B with hγ
  have hγ0 : 0 < γ := by rw [hγ]; unfold gammaOf; positivity
  set p := m / γ with hp
  have hp0 : 0 < p := by
    have : 0 < m := by linarith
    positivity
  have hp1 : p < 1 := by rw [hp, div_lt_one hγ0]; exact hm2
  have hphalf : 1 / 2 ≤ p := by rw [hp, le_div_iff₀ hγ0]; linarith
  have hmp : γ * p = m := by rw [hp]; field_simp
  have hbulk := eqn_app_pl_Bi_bulk hα c hN hB hc i hp0 hp1
  rw [← hγ, hmp] at hbulk
  rw [hbulk]
  have hV := pg6p2_finV_pos (α := α) c hN hB hc hp0 hp1
  have hVlo := (h3 N hN p hphalf hp1).1
  have han := pg6p2_aN_pos (α := α) hc hN
  have h1p : 0 < 1 - p := by linarith
  have e : (γ - m) / γ = 1 - p := by rw [hp]; field_simp
  rw [e]
  set V := finV α N p with hVdef
  set y := ((((i : ℕ) : ℝ) + 1) / (N : ℝ)) ^ α with hy
  have hy0 : 0 ≤ y := Real.rpow_nonneg (by positivity) _
  have hfrac : V / (V + y) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ V / (V + y) := by positivity
  have hsq : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (2 / c3) * (1 - p) := by
    rw [show Real.sqrt (2 / c3) * (1 - p) = Real.sqrt (2 / c3 * (1 - p) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1p.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h4 : c3 / (1 - p) ≤ V := hVlo
    rw [div_le_iff₀ h1p] at h4
    -- (1-p) ≤ p V (1-p)... use p ≥ 1/2: p*V ≥ V/2 ≥ c3/(2(1-p))
    have h5 : c3 ≤ V * (1 - p) := h4
    have h6 : (2 / c3 * (1 - p) ^ 2) * (p * V) = 2 * (1 - p) * (p * (V * (1 - p))) / c3 := by
      field_simp
    rw [h6, le_div_iff₀ hc3]
    nlinarith [mul_pos h1p hp0, mul_nonneg h1p.le hc3.le]
  calc aN α c N * Real.sqrt ((1 - p) / (p * V)) * (V / (V + y))
      ≤ aN α c N * (Real.sqrt (2 / c3) * (1 - p)) * 1 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsq han.le) hfrac hfrac0 (by positivity)
    _ = _ := by ring

private lemma pg6p2_f_int {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    IntegrableOn (fun m => Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m)
      (Ioo 0 (gammaOf N B)) := by
  have h := lem_app_pl_drift_participation_i μ hβ0 hβ1 hB hN hpos i
  have hD := pg6_dZero_pos μ hβ0 hβ1 hB hN hanti hpos i
  have hγ := pg6_gamma_pos hB hN
  by_contra hni
  have h0 : ∫ m in Ioo 0 (gammaOf N B),
      Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m = 0 := integral_undef hni
  rw [h0, mul_zero] at h
  have : 0 < Real.sqrt 2 * dZero β B μ i := mul_pos (by positivity) hD
  linarith

private lemma pg6p2_top {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K7 : ℝ, 0 < K7 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ M →
      4 * M ≤ gammaOf N B →
      0 ≤ ∫ m in (gammaOf N B - M)..(gammaOf N B),
        Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m ∧
      ∫ m in (gammaOf N B - M)..(gammaOf N B),
        Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m ≤
        K7 * aN α c N * M ^ 2 / gammaOf N B := by
  obtain ⟨cA, CA, hcA, hA⟩ := lem_app_pl_average_i hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨K6, hK6, hW⟩ := pg6p2_W_top hα
  obtain ⟨C3, hC3, hPhi⟩ := pg6p2_Phi_bounds hα hβ0 hβ1
  have hCA : 0 < CA := lt_of_lt_of_le hcA ((hA 1 le_rfl).1.trans (hA 1 le_rfl).2)
  refine ⟨CA * K6 * (1 + 2 * C3), by positivity, fun N B c i M hN hB hc hM h4 => ?_⟩
  have hγ := pg6_gamma_pos hB hN
  have han := pg6p2_aN_pos (α := α) hc hN
  have hanti := pg6_plSpec_anti (N := N) hα hc
  have hpos := fun j => pg6_plSpec_pos (α := α) (hc) (N := N) j
  set γ := gammaOf N B with hγdef
  set μ := plSpec α c N with hμ
  set f : ℝ → ℝ := fun m => Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m with hf
  have hfint : IntegrableOn f (Ioo 0 γ) := pg6p2_f_int μ hβ0 hβ1 hB hN hanti hpos i
  have hsub : Ioo (γ - M) γ ⊆ Ioo 0 γ := Ioo_subset_Ioo (by linarith) le_rfl
  have hfn : ∀ m ∈ Ioo 0 γ, 0 ≤ f m := fun m hm =>
    pg6_f_nonneg μ hβ0 hβ1 hB hN hanti hpos i hm
  have hMK : 0 < M := by linarith
  have hle : γ - M ≤ γ := by linarith
  rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo]
  refine ⟨setIntegral_nonneg measurableSet_Ioo (fun m hm => hfn m (hsub hm)), ?_⟩
  set Kpt := CA * K6 * (1 + 2 * C3) * aN α c N * M / γ with hKpt
  have hpt : ∀ m ∈ Ioo (γ - M) γ, f m ≤ Kpt := by
    intro m hm
    obtain ⟨hm1, hm2⟩ := hm
    have hm0 : 0 < m := by linarith
    have hmI : m ∈ Ioo 0 γ := ⟨hm0, hm2⟩
    have hm3 : 1 ≤ m := by linarith
    have hgm : 0 < γ - m := by linarith
    have hAm := (hA m hm3).2
    have hAm0 : 0 ≤ Aav β m := (hcA.le.trans (hA m hm3).1)
    have hWm := hW N B c i hN hB hc m (by linarith) hm2
    have hW0 := (pg6p2_W_facts hα).choose_spec.2 N B c hN hB hc i m hmI
    obtain ⟨hP1, hP2⟩ := hPhi N B c hN hB hc m hmI
    have hΦ : Efun β m * thetaN β B μ m ≤ 1 + C3 + C3 / (γ - m) := by
      have : 1 / m ≤ 1 := by rw [div_le_one hm0]; exact hm3
      calc _ ≤ 1 + C3 * (1 / m + 1 / (γ - m)) := hP2
        _ ≤ 1 + C3 * (1 + 1 / (γ - m)) := by nlinarith
        _ = _ := by ring
    have hWm0 : 0 ≤ partBfun B μ i m := hW0.1.le
    have hfeq : f m = Aav β m * partBfun B μ i m * (Efun β m * thetaN β B μ m) := by
      simp only [hf]; ring
    rw [hfeq]
    have hΦ0 : 0 ≤ Efun β m * thetaN β B μ m := by linarith
    calc Aav β m * partBfun B μ i m * (Efun β m * thetaN β B μ m)
        ≤ CA * (K6 * aN α c N * ((γ - m) / γ)) * (1 + C3 + C3 / (γ - m)) := by
          apply mul_le_mul (mul_le_mul hAm hWm hWm0 hCA.le) hΦ hΦ0 (by positivity)
      _ = CA * K6 * aN α c N * (((1 + C3) * (γ - m) + C3) / γ) := by
          field_simp
      _ ≤ CA * K6 * aN α c N * (((1 + C3) * M + C3) / γ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          apply div_le_div_of_nonneg_right _ hγ.le
          nlinarith
      _ ≤ Kpt := by
          rw [hKpt]
          have : (1 + C3) * M + C3 ≤ (1 + 2 * C3) * M := by nlinarith
          calc CA * K6 * aN α c N * (((1 + C3) * M + C3) / γ)
              ≤ CA * K6 * aN α c N * (((1 + 2 * C3) * M) / γ) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                exact div_le_div_of_nonneg_right this hγ.le
            _ = _ := by ring
  have h1 : ∫ m in Ioo (γ - M) γ, f m ≤ ∫ m in Ioo (γ - M) γ, Kpt :=
    setIntegral_mono_on (hfint.mono_set hsub) (integrableOn_const (by simp)) measurableSet_Ioo hpt
  refine h1.trans ?_
  rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith)]
  rw [hKpt]
  have : γ - (γ - M) = M := by ring
  rw [this]
  have hfin : M * (CA * K6 * (1 + 2 * C3) * aN α c N * M / γ) =
      CA * K6 * (1 + 2 * C3) * aN α c N * M ^ 2 / γ := by ring
  rw [hfin]

private lemma pg6p2_W_cd {N B : ℕ} (μ : Fin N → ℝ) (hB : 0 < B) (hN : 0 < N)
    (hpos : ∀ i, 0 < μ i) (i : Fin N) :
    ContDiffOn ℝ 1 (partBfun B μ i) (Ioo 0 (gammaOf N B)) := by
  obtain ⟨-, hb2, -, hcd⟩ := def_app_pl_participation_bij μ hB hN hpos
  have hΛ : ContDiffOn ℝ 1 (partLam B μ) (Ioo 0 (gammaOf N B)) := hcd.of_le (by exact_mod_cast le_top)
  have hmu := hpos i
  have hLp : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < partLam B μ m := fun m hm => hb2.mapsTo hm
  have hu : ContDiffOn ℝ 1 (fun m => (gammaOf N B - m) / (m * partLam B μ m)) (Ioo 0 (gammaOf N B)) := by
    refine (contDiffOn_const.sub contDiffOn_id).div (contDiffOn_id.mul hΛ) (fun m hm => ?_)
    exact (mul_pos hm.1 (hLp m hm)).ne'
  have hs : ContDiffOn ℝ 1 (fun m => Real.sqrt ((gammaOf N B - m) / (m * partLam B μ m)))
      (Ioo 0 (gammaOf N B)) := by
    refine hu.sqrt (fun m hm => ?_)
    exact (div_pos (sub_pos.2 hm.2) (mul_pos hm.1 (hLp m hm))).ne'
  have hf : ContDiffOn ℝ 1 (fun m => partLam B μ m * μ i / (1 + partLam B μ m * μ i))
      (Ioo 0 (gammaOf N B)) := by
    refine (hΛ.mul contDiffOn_const).div (contDiffOn_const.add (hΛ.mul contDiffOn_const)) (fun m hm => ?_)
    have := mul_pos (hLp m hm) hmu
    linarith
  exact hs.mul hf

private lemma pg6p2_W_left {α : ℝ} (hα : 0 < α) :
    ∃ C4 : ℝ, 0 < C4 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ M →
      4 * M ≤ gammaOf N B →
      partBfun B (plSpec α c N) i M ≤
        Real.exp (2 * C4) / M * ∫ m in M..(2 * M), partBfun B (plSpec α c N) i m := by
  obtain ⟨C4, hC4, hW⟩ := pg6p2_W_facts hα
  refine ⟨C4, hC4, fun N B c i M hN hB hc hM h4 => ?_⟩
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B with hγdef
  set W := partBfun B (plSpec α c N) i with hWdef
  have hIcc : ∀ m ∈ Icc M (2 * M), m ∈ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩
  -- log-derivative bound
  have hlog : ∀ m ∈ Icc M (2 * M), HasDerivWithinAt (fun x => Real.log (W x))
      (deriv W m / W m) (Icc M (2 * M)) m := by
    intro m hm
    obtain ⟨hpos, hd, -⟩ := hW N B c hN hB hc i m (hIcc m hm)
    exact (hd.log hpos.ne').hasDerivWithinAt
  have hbd : ∀ m ∈ Icc M (2 * M), ‖deriv W m / W m‖ ≤ 2 * C4 / M := by
    intro m hm
    obtain ⟨hpos, -, hder⟩ := hW N B c hN hB hc i m (hIcc m hm)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    refine hder.trans ?_
    have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1
    have h2 : 1 / (γ - m) ≤ 1 / M := by
      apply one_div_le_one_div_of_le hM0; linarith [hm.2]
    have : (1 / m + 1 / (γ - m)) ≤ 2 / M := by
      have : 2 / M = 1 / M + 1 / M := by ring
      linarith
    calc C4 * W m * (1 / m + 1 / (γ - m)) ≤ C4 * W m * (2 / M) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = 2 * C4 / M * W m := by ring
  have hmvt : ∀ m ∈ Icc M (2 * M), Real.log (W M) ≤ Real.log (W m) + 2 * C4 := by
    intro m hm
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hlog hbd (convex_Icc M (2 * M))
      (show M ∈ Icc M (2 * M) from ⟨le_rfl, by linarith⟩) hm
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
    have h1 := (abs_le.1 this).1
    have h2 : 2 * C4 / M * |m - M| ≤ 2 * C4 := by
      rw [abs_of_nonneg (by linarith [hm.1])]
      rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
      nlinarith [hm.2]
    linarith
  have hWpos : ∀ m ∈ Icc M (2 * M), 0 < W m := fun m hm => (hW N B c hN hB hc i m (hIcc m hm)).1
  have hWM : ∀ m ∈ Icc M (2 * M), W M ≤ Real.exp (2 * C4) * W m := by
    intro m hm
    have hM1 : 0 < W M := hWpos M ⟨le_rfl, by linarith⟩
    have := hmvt m hm
    have h2 : W M ≤ Real.exp (Real.log (W m) + 2 * C4) := by
      calc W M = Real.exp (Real.log (W M)) := (Real.exp_log hM1).symm
        _ ≤ _ := Real.exp_le_exp.2 this
    rw [Real.exp_add, Real.exp_log (hWpos m hm)] at h2
    linarith
  have hcontW : ContinuousOn W (Icc M (2 * M)) := fun m hm =>
    (hW N B c hN hB hc i m (hIcc m hm)).2.1.continuousAt.continuousWithinAt
  have hint : IntervalIntegrable W volume M (2 * M) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le (by linarith)]
    exact hcontW
  have e : Real.exp (2 * C4) * Real.exp (-(2 * C4)) = 1 := by rw [← Real.exp_add]; simp
  have hmono : ∫ m in M..(2 * M), W M * Real.exp (-(2 * C4)) ≤ ∫ m in M..(2 * M), W m := by
    refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint (fun m hm => ?_)
    have := hWM m hm
    have hep := Real.exp_pos (-(2 * C4))
    calc W M * Real.exp (-(2 * C4)) ≤ (Real.exp (2 * C4) * W m) * Real.exp (-(2 * C4)) :=
          mul_le_mul_of_nonneg_right this hep.le
      _ = W m * (Real.exp (2 * C4) * Real.exp (-(2 * C4))) := by ring
      _ = W m := by rw [e, mul_one]
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  have e1 : (2 * M - M) = M := by ring
  rw [e1] at hmono
  have hep := Real.exp_pos (2 * C4)
  rw [div_mul_eq_mul_div, le_div_iff₀ hM0]
  have : M * (W M * Real.exp (-(2 * C4))) * Real.exp (2 * C4) = M * W M := by
    calc _ = M * W M * (Real.exp (2 * C4) * Real.exp (-(2 * C4))) := by ring
      _ = _ := by rw [e, mul_one]
  nlinarith [mul_le_mul_of_nonneg_right hmono hep.le]

private lemma pg6p2_mid {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K8 : ℝ, 0 < K8 ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 0 < B → 0 < c → 1 ≤ M →
      4 * M ≤ gammaOf N B →
      |(∫ m in M..(gammaOf N B - M),
          Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) -
        Real.sqrt (2 * Real.pi) * ∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m| ≤
        K8 / M * (∫ m in M..(gammaOf N B - M), partBfun B (plSpec α c N) i m) +
          K8 * aN α c N * M / gammaOf N B := by
  obtain ⟨cA, CA, hcA, hA⟩ := lem_app_pl_average_i hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨hAint, -⟩ := lem_app_pl_average_ii hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨Cavg, hCavg⟩ := lem_app_pl_average_iii hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨K6, hK6, hWtop⟩ := pg6p2_W_top hα
  obtain ⟨C3, hC3, hPhi⟩ := pg6p2_Phi_bounds hα hβ0 hβ1
  obtain ⟨C4w, hC4w, hWf⟩ := pg6p2_W_facts hα
  obtain ⟨C4l, hC4l, hWleft⟩ := pg6p2_W_left hα
  have hCA : 0 < CA := lt_of_lt_of_le hcA ((hA 1 le_rfl).1.trans (hA 1 le_rfl).2)
  refine ⟨(|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6, by positivity,
    fun N B c i M hN hB hc hM h4 => ?_⟩
  have hγ := pg6_gamma_pos hB hN
  have han := pg6p2_aN_pos (α := α) hc hN
  have hanti := pg6_plSpec_anti (N := N) hα hc
  have hpos := fun j => pg6_plSpec_pos (α := α) hc (N := N) j
  have hM0 : 0 < M := by linarith
  set γ := gammaOf N B with hγdef
  set μ := plSpec α c N with hμ
  set W := partBfun B μ i with hWdef
  set s := Real.sqrt (2 * Real.pi) with hs
  set M' := γ - M with hM'
  have hMM' : M < M' := by rw [hM']; linarith
  have hM2 : 2 * M ≤ M' := by rw [hM']; linarith
  have hIcc : ∀ m ∈ Icc M M', m ∈ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], by rw [hM'] at hm; linarith [hm.2]⟩
  have hWc : ContinuousOn W (Icc M M') := fun m hm =>
    (hWf N B c hN hB hc i m (hIcc m hm)).2.1.continuousAt.continuousWithinAt
  have hWi : IntervalIntegrable W volume M M' := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hMM'.le]; exact hWc
  have hW0 : ∀ m ∈ Icc M M', 0 < W m := fun m hm => (hWf N B c hN hB hc i m (hIcc m hm)).1
  set J := ∫ m in M..M', W m with hJ
  have hJ0 : 0 ≤ J := intervalIntegral.integral_nonneg hMM'.le (fun m hm => (hW0 m hm).le)
  have hAi : IntervalIntegrable (Aav β) volume M M' :=
    ((hAint M' (by linarith)).mono_set (by
      rw [uIcc_of_le hMM'.le, uIcc_of_le (by linarith : (1:ℝ) ≤ M')]
      exact Icc_subset_Icc hM le_rfl))
  have hAW : IntervalIntegrable (fun m => Aav β m * W m) volume M M' := by
    refine hAi.mul_continuousOn ?_
    rw [uIcc_of_le hMM'.le]; exact hWc
  set f : ℝ → ℝ := fun m => Aav β m * W m * Efun β m * thetaN β B μ m with hf
  have hfint : IntegrableOn f (Ioo 0 γ) := pg6p2_f_int μ hβ0 hβ1 hB hN hanti hpos i
  have hfi : IntervalIntegrable f volume M M' := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hMM'.le]
    exact hfint.mono_set hIcc
  -- splitting
  have hR2 : ∫ m in M..M', f m = (∫ m in M..M', Aav β m * W m) + ∫ m in M..M', (f m - Aav β m * W m) := by
    rw [intervalIntegral.integral_sub hfi hAW]; ring
  have hR1 : ∫ m in M..M', Aav β m * W m = (∫ m in M..M', (Aav β m - s) * W m) + s * J := by
    have : ∫ m in M..M', (Aav β m - s) * W m = (∫ m in M..M', Aav β m * W m) - s * J := by
      rw [hJ, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub hAW (hWi.const_mul s)]
      congr 1; ext m; ring
    linarith
  -- bound on R2
  have hR2b : 0 ≤ ∫ m in M..M', (f m - Aav β m * W m) ∧
      ∫ m in M..M', (f m - Aav β m * W m) ≤ 2 * CA * C3 / M * J := by
    have hpt : ∀ m ∈ Icc M M', 0 ≤ f m - Aav β m * W m ∧
        f m - Aav β m * W m ≤ 2 * CA * C3 / M * W m := by
      intro m hm
      have hmI := hIcc m hm
      have hm1 : 1 ≤ m := by linarith [hm.1]
      obtain ⟨hP1, hP2⟩ := hPhi N B c hN hB hc m hmI
      have hAm := hA m hm1
      have hWm := hW0 m hm
      have hfeq : f m - Aav β m * W m = Aav β m * W m * (Efun β m * thetaN β B μ m - 1) := by
        simp only [hf]; ring
      rw [hfeq]
      have hsum : 1 / m + 1 / (γ - m) ≤ 2 / M := by
        have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1
        have h2 : 1 / (γ - m) ≤ 1 / M := by
          apply one_div_le_one_div_of_le hM0
          have := hm.2; rw [hM'] at this; linarith
        have : 2 / M = 1 / M + 1 / M := by ring
        linarith
      have hAW0 : 0 ≤ Aav β m * W m := mul_nonneg (hcA.le.trans hAm.1) hWm.le
      refine ⟨mul_nonneg hAW0 (by linarith), ?_⟩
      have hΦ1 : Efun β m * thetaN β B μ m - 1 ≤ C3 * (2 / M) := by
        have : C3 * (1 / m + 1 / (γ - m)) ≤ C3 * (2 / M) := mul_le_mul_of_nonneg_left hsum hC3.le
        linarith
      calc Aav β m * W m * (Efun β m * thetaN β B μ m - 1) ≤ (CA * W m) * (C3 * (2 / M)) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hAm.2 hWm.le) hΦ1 (by linarith) (by positivity)
        _ = 2 * CA * C3 / M * W m := by ring
    refine ⟨intervalIntegral.integral_nonneg hMM'.le (fun m hm => (hpt m hm).1), ?_⟩
    calc ∫ m in M..M', (f m - Aav β m * W m) ≤ ∫ m in M..M', 2 * CA * C3 / M * W m :=
          intervalIntegral.integral_mono_on hMM'.le (hfi.sub hAW) (hWi.const_mul _)
            (fun m hm => (hpt m hm).2)
      _ = 2 * CA * C3 / M * J := by rw [intervalIntegral.integral_const_mul]
  -- bound on R1 by averaging
  have hWcd : ContDiffOn ℝ 1 W (Icc M M') :=
    (pg6p2_W_cd μ hB hN hpos i).mono hIcc
  have hibp := hCavg M M' hM hMM'.le W hWcd
  have hWM : W M ≤ Real.exp (2 * C4l) / M * J := by
    have h1 := hWleft N B c i M hN hB hc hM h4
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    refine intervalIntegral.integral_mono_interval le_rfl (by linarith) hM2 ?_ hWi
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall (fun m hm => (hW0 m ⟨hm.1.le, hm.2⟩).le)
  have hWM' : W M' ≤ K6 * aN α c N * M / γ := by
    have := hWtop N B c i hN hB hc M' (by rw [hM']; linarith) (by rw [hM']; linarith)
    have e : (γ - M') / γ = M / γ := by rw [hM']; ring
    rw [e] at this
    calc W M' ≤ K6 * aN α c N * (M / γ) := this
      _ = K6 * aN α c N * M / γ := by ring
  have hdw : ∫ m in M..M', |derivWithin W (Icc M M') m| ≤ 2 * C4w / M * J := by
    have hcd := hWcd.continuousOn_derivWithin (uniqueDiffOn_Icc hMM') (le_refl 1)
    have hint : IntervalIntegrable (fun m => |derivWithin W (Icc M M') m|) volume M M' := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hMM'.le]
      exact hcd.abs
    calc ∫ m in M..M', |derivWithin W (Icc M M') m| ≤ ∫ m in M..M', 2 * C4w / M * W m := by
          refine intervalIntegral.integral_mono_on_of_le_Ioo hMM'.le hint (hWi.const_mul _) ?_
          intro m hm
          have hmI := hIcc m ⟨hm.1.le, hm.2.le⟩
          rw [derivWithin_of_mem_nhds (Icc_mem_nhds hm.1 hm.2)]
          obtain ⟨hp, -, hd⟩ := hWf N B c hN hB hc i m hmI
          refine hd.trans ?_
          have h1 : 1 / m ≤ 1 / M := one_div_le_one_div_of_le hM0 hm.1.le
          have h2 : 1 / (γ - m) ≤ 1 / M := by
            apply one_div_le_one_div_of_le hM0
            have := hm.2; rw [hM'] at this; linarith
          have : 1 / m + 1 / (γ - m) ≤ 2 / M := by
            have : 2 / M = 1 / M + 1 / M := by ring
            linarith
          calc C4w * W m * (1 / m + 1 / (γ - m)) ≤ C4w * W m * (2 / M) :=
                mul_le_mul_of_nonneg_left this (by positivity)
            _ = 2 * C4w / M * W m := by ring
      _ = 2 * C4w / M * J := by rw [intervalIntegral.integral_const_mul]
  have hR1b : |∫ m in M..M', (Aav β m - s) * W m| ≤
      |Cavg| * ((Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ) := by
    refine hibp.trans ?_
    rw [abs_of_pos (hW0 M ⟨le_rfl, hMM'.le⟩), abs_of_pos (hW0 M' ⟨hMM'.le, le_rfl⟩)]
    have hbr : W M + W M' + ∫ m in M..M', |derivWithin W (Icc M M') m| ≤
        (Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ := by
      have : (Real.exp (2 * C4l) + 2 * C4w) / M * J =
          Real.exp (2 * C4l) / M * J + 2 * C4w / M * J := by ring
      linarith
    exact (mul_le_mul_of_nonneg_right (le_abs_self Cavg) (by
      have := hW0 M ⟨le_rfl, hMM'.le⟩
      have := hW0 M' ⟨hMM'.le, le_rfl⟩
      have : 0 ≤ ∫ m in M..M', |derivWithin W (Icc M M') m| :=
        intervalIntegral.integral_nonneg hMM'.le (fun m _ => abs_nonneg _)
      linarith)).trans (mul_le_mul_of_nonneg_left hbr (abs_nonneg _))
  -- assemble
  have e : (∫ m in M..M', f m) - s * J =
      (∫ m in M..M', (Aav β m - s) * W m) + ∫ m in M..M', (f m - Aav β m * W m) := by
    rw [hR2, hR1]; ring
  show |(∫ m in M..M', f m) - s * J| ≤ _
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_of_nonneg hR2b.1]
  have h1 := hR1b
  have h2 := hR2b.2
  have hdiff : ((|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6) / M * J +
      ((|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) + |Cavg| * K6) * aN α c N * M / γ -
      (|Cavg| * ((Real.exp (2 * C4l) + 2 * C4w) / M * J + K6 * aN α c N * M / γ) +
        2 * CA * C3 / M * J) =
      |Cavg| * K6 / M * J +
        (|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) * aN α c N * M / γ := by
    field_simp
    ring
  have hnn : 0 ≤ |Cavg| * K6 / M * J +
        (|Cavg| * (Real.exp (2 * C4l) + 2 * C4w) + 2 * CA * C3) * aN α c N * M / γ := by
    positivity
  simp only [hJ] at h1 h2 hnn hdiff
  linarith

private lemma pg6p2_c0_eq : Real.sqrt (2 * Real.pi) / Real.pi = c0 := by
  unfold c0
  have hpi := Real.pi_pos
  rw [eq_comm, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
  have h2 : Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
    Real.mul_self_sqrt (by positivity)
  field_simp
  nlinarith [h2]

private lemma pg6p2_assemble {a γ M T Imid Itop J Ψ0 Ψt ψ K7 K8 K9 C5 L : ℝ}
    (ha : 0 < a) (hγ : 0 < γ) (hM : 1 ≤ M) (hK7 : 0 ≤ K7) (hK8 : 0 ≤ K8) (hK9 : 0 ≤ K9)
    (hC5 : 0 ≤ C5)
    (hT : T = 1 / (Real.pi * γ) * (Imid + Itop))
    (hmid : |Imid - Real.sqrt (2 * Real.pi) * J| ≤ K8 / M * J + K8 * a * M / γ)
    (hItop : 0 ≤ Itop) (hItop' : Itop ≤ K7 * a * M ^ 2 / γ)
    (hJ : 0 ≤ J) (hS5l : (1 - L) * Ψ0 ≤ J / (γ * a)) (hS5u : J / (γ * a) ≤ (1 + L) * Ψ0)
    (hL0 : 0 ≤ L) (hL1 : L ≤ 1) (hLM : L ≤ C5 / M) (hψ : ψ = c0 * (Ψ0 + Ψt))
    (hΨ0 : 0 ≤ Ψ0) (hΨt0 : 0 ≤ Ψt) (hΨt : Ψt ≤ K9 * (M / γ) ^ 2) {K : ℝ}
    (hK : (2 * K8 / Real.pi + c0 * C5) / c0 ≤ K) (hK' : K8 / Real.pi + K7 / Real.pi + c0 * K9 ≤ K) :
    |T - a * ψ| ≤ a * (K / M * ψ + K * (M / γ) ^ 2) := by
  have hpi := Real.pi_pos
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hM0 : 0 < M := by linarith
  set s := Real.sqrt (2 * Real.pi) with hs
  have hsc : s / Real.pi = c0 := pg6p2_c0_eq
  -- J bound
  have hJle : J ≤ 2 * γ * a * Ψ0 := by
    have := (div_le_iff₀ (by positivity : 0 < γ * a)).1 hS5u
    nlinarith [mul_nonneg hΨ0 (by linarith : 0 ≤ 1 - L), mul_pos hγ ha]
  have hΨ0ψ : c0 * Ψ0 ≤ ψ := by rw [hψ]; nlinarith
  -- decomposition
  have hdec : T - a * ψ = 1 / (Real.pi * γ) * (Imid - s * J) + 1 / (Real.pi * γ) * Itop +
      c0 * a * (J / (γ * a) - Ψ0) - c0 * a * Ψt := by
    rw [hT, hψ, ← hsc]
    field_simp
    ring
  have hdiff : |J / (γ * a) - Ψ0| ≤ L * Ψ0 := by
    rw [abs_le]; constructor <;> nlinarith
  have hpg : 0 < 1 / (Real.pi * γ) := by positivity
  have t1 : |1 / (Real.pi * γ) * (Imid - s * J)| ≤ 1 / (Real.pi * γ) * (K8 / M * J + K8 * a * M / γ) := by
    rw [abs_mul, abs_of_pos hpg]
    exact mul_le_mul_of_nonneg_left hmid hpg.le
  have t2 : 1 / (Real.pi * γ) * Itop ≤ 1 / (Real.pi * γ) * (K7 * a * M ^ 2 / γ) :=
    mul_le_mul_of_nonneg_left hItop' hpg.le
  have t3 : |c0 * a * (J / (γ * a) - Ψ0)| ≤ c0 * a * (L * Ψ0) := by
    rw [abs_mul, abs_of_pos (by positivity : 0 < c0 * a)]
    exact mul_le_mul_of_nonneg_left hdiff (by positivity)
  have t4 : 1 / (Real.pi * γ) * (K8 / M * J) ≤ 2 * K8 / Real.pi / M * (a * Ψ0) := by
    have : 1 / (Real.pi * γ) * (K8 / M * J) ≤ 1 / (Real.pi * γ) * (K8 / M * (2 * γ * a * Ψ0)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJle (by positivity)) hpg.le
    refine this.trans (le_of_eq ?_)
    field_simp
  have hMg : M / γ ^ 2 ≤ (M / γ) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    linarith [mul_nonneg (mul_nonneg hM0.le (sub_nonneg.2 hM)) (sq_nonneg γ)]
  have t5 : 1 / (Real.pi * γ) * (K8 * a * M / γ) ≤ K8 / Real.pi * a * (M / γ) ^ 2 := by
    have : 1 / (Real.pi * γ) * (K8 * a * M / γ) = K8 / Real.pi * a * (M / γ ^ 2) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hMg (by positivity)
  have t6 : 1 / (Real.pi * γ) * (K7 * a * M ^ 2 / γ) = K7 / Real.pi * a * (M / γ) ^ 2 := by
    field_simp
  have t7 : c0 * a * (L * Ψ0) ≤ c0 * C5 / M * (a * Ψ0) := by
    have : c0 * a * (L * Ψ0) = c0 * (L * (a * Ψ0)) := by ring
    rw [this]
    have h2 : L * (a * Ψ0) ≤ C5 / M * (a * Ψ0) :=
      mul_le_mul_of_nonneg_right hLM (by positivity)
    calc c0 * (L * (a * Ψ0)) ≤ c0 * (C5 / M * (a * Ψ0)) := mul_le_mul_of_nonneg_left h2 hc0.le
      _ = _ := by ring
  have t8 : c0 * a * Ψt ≤ c0 * K9 * a * (M / γ) ^ 2 := by
    have := mul_le_mul_of_nonneg_left hΨt (by positivity : 0 ≤ c0 * a)
    calc c0 * a * Ψt ≤ c0 * a * (K9 * (M / γ) ^ 2) := this
      _ = _ := by ring
  have hΨ0ψ' : a * Ψ0 ≤ a * (ψ / c0) := by
    apply mul_le_mul_of_nonneg_left _ ha.le
    rw [le_div_iff₀ hc0]; linarith
  rw [hdec]
  have habs : |1 / (Real.pi * γ) * (Imid - s * J) + 1 / (Real.pi * γ) * Itop +
      c0 * a * (J / (γ * a) - Ψ0) - c0 * a * Ψt| ≤
      |1 / (Real.pi * γ) * (Imid - s * J)| + 1 / (Real.pi * γ) * Itop +
        |c0 * a * (J / (γ * a) - Ψ0)| + c0 * a * Ψt := by
    have h1 := abs_sub (1 / (Real.pi * γ) * (Imid - s * J) + 1 / (Real.pi * γ) * Itop +
      c0 * a * (J / (γ * a) - Ψ0)) (c0 * a * Ψt)
    have h2 := abs_add_three (1 / (Real.pi * γ) * (Imid - s * J)) (1 / (Real.pi * γ) * Itop)
      (c0 * a * (J / (γ * a) - Ψ0))
    rw [abs_of_nonneg (by positivity : 0 ≤ c0 * a * Ψt)] at h1
    rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (Real.pi * γ) * Itop)] at h2
    linarith
  refine habs.trans ?_
  -- total
  have hψ0 : 0 ≤ ψ := by rw [hψ]; positivity
  have hX : 0 ≤ (2 * K8 / Real.pi + c0 * C5) := by positivity
  have hKM : 0 ≤ K := by
    have : 0 ≤ (2 * K8 / Real.pi + c0 * C5) / c0 := by positivity
    linarith
  have e1 : 1 / (Real.pi * γ) * (K8 / M * J + K8 * a * M / γ) =
      1 / (Real.pi * γ) * (K8 / M * J) + 1 / (Real.pi * γ) * (K8 * a * M / γ) := by ring
  have f1 : (2 * K8 / Real.pi / M) * (a * Ψ0) + c0 * C5 / M * (a * Ψ0) ≤ K / M * (a * ψ) := by
    have e2 : (2 * K8 / Real.pi / M) * (a * Ψ0) + c0 * C5 / M * (a * Ψ0) =
        (2 * K8 / Real.pi + c0 * C5) / M * (a * Ψ0) := by ring
    rw [e2]
    have h1 : (2 * K8 / Real.pi + c0 * C5) / M * (a * Ψ0) ≤
        (2 * K8 / Real.pi + c0 * C5) / M * (a * (ψ / c0)) :=
      mul_le_mul_of_nonneg_left hΨ0ψ' (by positivity)
    have h2 : (2 * K8 / Real.pi + c0 * C5) / M * (a * (ψ / c0)) =
        ((2 * K8 / Real.pi + c0 * C5) / c0) / M * (a * ψ) := by field_simp
    have h3 : ((2 * K8 / Real.pi + c0 * C5) / c0) / M * (a * ψ) ≤ K / M * (a * ψ) :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hK hM0.le) (by positivity)
    linarith
  have f2 : (K8 / Real.pi * a * (M / γ) ^ 2 + K7 / Real.pi * a * (M / γ) ^ 2 +
      c0 * K9 * a * (M / γ) ^ 2) ≤ K * a * (M / γ) ^ 2 := by
    have : (K8 / Real.pi * a * (M / γ) ^ 2 + K7 / Real.pi * a * (M / γ) ^ 2 +
      c0 * K9 * a * (M / γ) ^ 2) = (K8 / Real.pi + K7 / Real.pi + c0 * K9) * (a * (M / γ) ^ 2) := by ring
    rw [this]
    calc _ ≤ K * (a * (M / γ) ^ 2) := mul_le_mul_of_nonneg_right hK' (by positivity)
      _ = _ := by ring
  have hmain : |1 / (Real.pi * γ) * (Imid - s * J)| + 1 / (Real.pi * γ) * Itop +
      |c0 * a * (J / (γ * a) - Ψ0)| + c0 * a * Ψt ≤
      (2 * K8 / Real.pi / M) * (a * Ψ0) + K8 / Real.pi * a * (M / γ) ^ 2 +
        (K7 / Real.pi * a * (M / γ) ^ 2) + c0 * C5 / M * (a * Ψ0) + c0 * K9 * a * (M / γ) ^ 2 := by
    rw [e1] at t1
    linarith [t3, t7, t8, t5, t6, t4, t2]
  calc _ ≤ _ := hmain
    _ ≤ a * (K / M * ψ + K * (M / γ) ^ 2) := by
      have : a * (K / M * ψ + K * (M / γ) ^ 2) = K / M * (a * ψ) + K * a * (M / γ) ^ 2 := by ring
      rw [this]
      linarith [f1, f2]

private lemma pg6p2_G_nonneg {α : ℝ} (hα : 0 < α) {x p : ℝ} (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    0 ≤ Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
  have hV := pg6p2_contV_pos hα hp
  unfold profF
  have : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have := hp.1
  positivity

private lemma pg6p2_G_top {α : ℝ} (hα : 0 < α) :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 0 < x → ∀ p : ℝ, 1 / 2 ≤ p → p < 1 →
      Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ K * (1 - p) := by
  obtain ⟨c3, C3, hc3, hC3, h3⟩ := lem_app_pl_continuum_iii_half hα
  refine ⟨Real.sqrt (2 / c3), by positivity, fun x hx p hphalf hp1 => ?_⟩
  have hp0 : 0 < p := by linarith
  have hV := pg6p2_contV_pos hα ⟨hp0, hp1⟩
  have hVlo := (h3 p hphalf hp1).1
  have h1p : 0 < 1 - p := by linarith
  set V := contV α p with hVdef
  have hy : 0 < x ^ α := Real.rpow_pos_of_pos hx _
  have hfrac : V / (V + x ^ α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hfrac0 : 0 ≤ V / (V + x ^ α) := by positivity
  have hsq : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (2 / c3) * (1 - p) := by
    rw [show Real.sqrt (2 / c3) * (1 - p) = Real.sqrt (2 / c3 * (1 - p) ^ 2) by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq h1p.le]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by positivity)]
    have h4 : c3 / (1 - p) ≤ V := hVlo
    rw [div_le_iff₀ h1p] at h4
    have h5 : c3 ≤ V * (1 - p) := h4
    have h6 : (2 / c3 * (1 - p) ^ 2) * (p * V) = 2 * (1 - p) * (p * (V * (1 - p))) / c3 := by
      field_simp
    rw [h6, le_div_iff₀ hc3]
    nlinarith [mul_pos h1p hp0, mul_nonneg h1p.le hc3.le]
  unfold profF
  rw [← hVdef]
  calc Real.sqrt ((1 - p) / (p * V)) * (V / (V + x ^ α))
      ≤ (Real.sqrt (2 / c3) * (1 - p)) * 1 :=
        mul_le_mul hsq hfrac hfrac0 (by positivity)
    _ = _ := by ring

private lemma pg6p2_psi_split {α : ℝ} (hα : 0 < α) :
    ∃ K9 : ℝ, 0 < K9 ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ 1 / 2 →
      psiRes α η x = c0 * ((∫ p in η..(1 - η), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) +
        ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p) ∧
      0 ≤ ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ∧
      ∫ p in (1 - η)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ K9 * η ^ 2 := by
  obtain ⟨K, hK, hKt⟩ := pg6p2_G_top hα
  refine ⟨K, hK, fun x hx η hη hη2 => ?_⟩
  have hint := lem_app_pl_Psi_i_integrable hα x hx
  have h1 : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume η (1 - η) := hint.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hη.le (by linarith))
  have h2 : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume (1 - η) 1 := hint.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl)
  refine ⟨?_, ?_, ?_⟩
  · unfold psiRes
    rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2]
  · rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo (fun p hp =>
      pg6p2_G_nonneg hα hx.1 ⟨by linarith [hp.1], hp.2⟩)
  · rw [intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    have hsub : Ioo (1 - η) 1 ⊆ Ioo 0 1 := Ioo_subset_Ioo (by linarith) le_rfl
    have hI2 : IntegrableOn (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
        (Ioo (1 - η) 1) := by
      have := h2
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)] at this
      exact (integrableOn_Ioc_iff_integrableOn_Ioo).1 this
    have hle : ∫ p in Ioo (1 - η) 1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
        ∫ p in Ioo (1 - η) 1, K * η :=
      setIntegral_mono_on hI2 (integrableOn_const (by simp)) measurableSet_Ioo (fun p hp => by
        have := hKt x hx.1 p (by linarith [hp.1]) hp.2
        have h3 : 1 - p ≤ η := by linarith [hp.1]
        nlinarith [hK])
    refine hle.trans ?_
    rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioo_of_le (by linarith)]
    have : 1 - (1 - η) = η := by ring
    rw [this]; nlinarith [hK, hη]

private lemma pg6p2_psi_lower {α : ℝ} (hα : 0 < α) :
    ∃ cΨ : ℝ, 0 < cΨ ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ 1 / 4 →
      cΨ ≤ psiRes α η x := by
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hx1 : (1:ℝ) ∈ Ioc (0:ℝ) 1 := ⟨one_pos, le_rfl⟩
  have hint1 := lem_app_pl_Psi_i_integrable hα 1 hx1
  have hint1' : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p)
      volume (1 / 4) (1 / 2) := hint1.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) (by norm_num))
  have hpos : 0 < ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on hint1' (fun p hp => ?_) (by norm_num)
    have hp0 : 0 < p := by linarith [hp.1]
    have hp1 : p < 1 := by linarith [hp.2]
    have hV := pg6p2_contV_pos hα ⟨hp0, hp1⟩
    unfold profF
    have : (0:ℝ) < 1 ^ α := Real.rpow_pos_of_pos one_pos _
    have h1 : 0 < (1 - p) / (p * contV α p) := div_pos (by linarith) (by positivity)
    have := Real.sqrt_pos.2 h1
    positivity
  refine ⟨c0 * ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p,
    mul_pos hc0 hpos, fun x hx η hη hη4 => ?_⟩
  unfold psiRes
  refine mul_le_mul_of_nonneg_left ?_ hc0.le
  have hintx := lem_app_pl_Psi_i_integrable hα x hx
  have hintxη : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume η 1 := hintx.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by linarith)]
    exact Icc_subset_Icc hη.le le_rfl)
  have hintx' : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume (1 / 4) (1 / 2) := hintx.mono_set (by
    rw [uIcc_of_le zero_le_one, uIcc_of_le (by norm_num)]
    exact Icc_subset_Icc (by norm_num) (by norm_num))
  have h1 : ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α 1 p ≤
      ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    refine intervalIntegral.integral_mono_on (by norm_num) hint1' hintx' (fun p hp => ?_)
    have hp0 : 0 < p := by linarith [hp.1]
    have hp1 : p < 1 := by linarith [hp.2]
    have hV := pg6p2_contV_pos hα ⟨hp0, hp1⟩
    unfold profF
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hxa : x ^ α ≤ 1 ^ α := Real.rpow_le_rpow hx.1.le hx.2 hα.le
    have hx0a : 0 < x ^ α := Real.rpow_pos_of_pos hx.1 _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hV hx0a]
  have h2 : ∫ p in (1 / 4 : ℝ)..(1 / 2), Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
      ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := by
    refine intervalIntegral.integral_mono_interval hη4 (by norm_num) (by norm_num) ?_ hintxη
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall (fun p hp => ?_)
    simp only [Pi.zero_apply]
    rcases hp.2.eq_or_lt with h | h
    · rw [h]; simp
    · exact pg6p2_G_nonneg hα hx.1 ⟨lt_of_lt_of_le hη hp.1.le, h⟩
  linarith

private lemma pg6p2_tail_det {α β : ℝ} (hα : 0 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N B : ℕ) (c : ℝ) (i : Fin N) (M : ℝ), 0 < N → 2 ≤ B → 0 < c → 1 ≤ M →
      4 * M ≤ gammaOf N B → K ≤ (B : ℝ) * M →
      |sqrt2DPiece β B (plSpec α c N) i M (gammaOf N B) -
          aN α c N * psiRes α (M / gammaOf N B) (rowNum i / (N : ℝ))| ≤
        aN α c N * (K / M * psiRes α (M / gammaOf N B) (rowNum i / (N : ℝ)) +
          K * (M / gammaOf N B) ^ 2) := by
  obtain ⟨K7, hK7, htop⟩ := pg6p2_top hα hβ0 hβ1
  obtain ⟨K8, hK8, hmid⟩ := pg6p2_mid hα hβ0 hβ1
  obtain ⟨C5, hC5, hS5⟩ := pg6p2_S5 hα
  obtain ⟨K9, hK9, hpsi⟩ := pg6p2_psi_split hα
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hpi := Real.pi_pos
  set K := C5 + (2 * K8 / Real.pi + c0 * C5) / c0 + (K8 / Real.pi + K7 / Real.pi + c0 * K9) with hK
  have hX : 0 ≤ (2 * K8 / Real.pi + c0 * C5) / c0 := by positivity
  have hY : 0 ≤ K8 / Real.pi + K7 / Real.pi + c0 * K9 := by positivity
  refine ⟨K, by positivity, fun N B c i M hN hB hc hM h4 hKBM => ?_⟩
  have hB0 : 0 < B := by omega
  have hγ := pg6_gamma_pos hB0 hN
  have han := pg6p2_aN_pos (α := α) hc hN
  have hNr : (0:ℝ) < N := by exact_mod_cast hN
  have hanti := pg6_plSpec_anti (N := N) hα hc
  have hpos := fun j => pg6_plSpec_pos (α := α) hc (N := N) j
  set γ := gammaOf N B with hγdef
  set μ := plSpec α c N with hμ
  have hM0 : 0 < M := by linarith
  have hBr : (2:ℝ) ≤ B := by exact_mod_cast hB
  have hMM' : M < γ - M := by linarith
  have hC5BM : C5 ≤ (B : ℝ) * M := by
    have : C5 ≤ K := by rw [hK]; linarith
    linarith
  -- the sqrt2DPiece
  set f : ℝ → ℝ := fun m => Aav β m * partBfun B μ i m * Efun β m * thetaN β B μ m with hf
  have hfint : IntegrableOn f (Ioo 0 γ) := pg6p2_f_int μ hβ0 hβ1 hB0 hN hanti hpos i
  have hsub1 : Icc M (γ - M) ⊆ Ioo 0 γ := fun m hm => ⟨by linarith [hm.1], by linarith [hm.2]⟩
  have hfi1 : IntervalIntegrable f volume M (γ - M) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hMM'.le]
    exact hfint.mono_set hsub1
  have hfi2 : IntervalIntegrable f volume (γ - M) γ := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith), integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hfint.mono_set (Ioo_subset_Ioo (by linarith) le_rfl)
  have hT : sqrt2DPiece β B μ i M γ =
      1 / (Real.pi * γ) * ((∫ m in M..(γ - M), f m) + ∫ m in (γ - M)..γ, f m) := by
    unfold sqrt2DPiece
    rw [intervalIntegral.integral_add_adjacent_intervals hfi1 hfi2,
      intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  obtain ⟨htop0, htop1⟩ := htop N B c i M hN hB0 hc hM h4
  have hmid' := hmid N B c i M hN hB0 hc hM h4
  obtain ⟨hS5l, hS5u⟩ := hS5 N B c i M hN hB hc hM (by linarith) hC5BM
  -- psi
  have hx01 : rowNum i / (N : ℝ) ∈ Ioc (0:ℝ) 1 :=
    ⟨div_pos (pg6_rowNum_pos i) hNr, (div_le_one hNr).2 (pg6p2_rowNum_le i)⟩
  have hη0 : 0 < M / γ := by positivity
  have hη2 : M / γ ≤ 1 / 2 := by rw [div_le_iff₀ hγ]; linarith
  obtain ⟨hψ, hΨt0, hΨt⟩ := hpsi (rowNum i / (N : ℝ)) hx01 (M / γ) hη0 hη2
  -- Ψ0 ≥ 0
  set Ψ0 := ∫ p in (M / γ)..(1 - M / γ),
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p with hΨ0
  have hΨ0nn : 0 ≤ Ψ0 := by
    rw [hΨ0, intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
    exact setIntegral_nonneg measurableSet_Ioo (fun p hp =>
      pg6p2_G_nonneg hα hx01.1 ⟨lt_trans hη0 hp.1, by linarith [hp.2, hη0]⟩)
  set J := ∫ m in M..(γ - M), partBfun B μ i m with hJ
  have hJ0 : 0 ≤ J := by
    rw [hJ]
    refine intervalIntegral.integral_nonneg hMM'.le (fun m hm => ?_)
    obtain ⟨hp, -, -⟩ := (pg6p2_W_facts hα).choose_spec.2 N B c hN hB0 hc i m (hsub1 hm)
    exact hp.le
  set L := C5 / ((B : ℝ) * M) with hL
  have hBM : 0 < (B : ℝ) * M := by positivity
  have hL0 : 0 ≤ L := by positivity
  have hL1 : L ≤ 1 := by rw [hL, div_le_one hBM]; exact hC5BM
  have hLM : L ≤ C5 / M := by
    rw [hL]
    apply div_le_div_of_nonneg_left hC5.le hM0
    nlinarith
  have hEq := pg6p2_assemble (a := aN α c N) (γ := γ) (M := M) (T := sqrt2DPiece β B μ i M γ)
    (Imid := ∫ m in M..(γ - M), f m) (Itop := ∫ m in (γ - M)..γ, f m) (J := J) (Ψ0 := Ψ0)
    (Ψt := ∫ p in (1 - M / γ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α (rowNum i / (N : ℝ)) p)
    (ψ := psiRes α (M / γ) (rowNum i / (N : ℝ))) (K7 := K7) (K8 := K8) (K9 := K9) (C5 := C5) (L := L)
    han hγ hM hK7.le hK8.le hK9.le hC5.le hT hmid' htop0 htop1 hJ0 (by
      rw [div_eq_inv_mul, ← one_div]; exact hS5l) (by rw [div_eq_inv_mul, ← one_div]; exact hS5u)
    hL0 hL1 hLM hψ hΨ0nn hΨt0 hΨt (K := K) (by rw [hK]; linarith) (by rw [hK]; linarith)
  exact hEq

/-- `lem:app-pl-tail` (snapshot `cr-2026-10-23`). LaTeX, verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[Averaged tail]\label{lem:app-pl-tail}
There is $C$ such that, for every fixed $M\ge M_0(\alpha,\bmom)$,
\[
\limsup_{N\to\infty}\sup_{1\le i\le N}\Big|\frac{\sqrt2\,\mathfrak d_i^{>M}}{a_N\Psi_\alpha^{[M/\gamma]}(i/N)}-1\Big|\le\frac CM .
\]
\end{lemma}
-/
theorem lem_app_pl_tail {α β : ℝ} :
    ∃ C M₀ : ℝ, 0 < M₀ ∧ ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
    ∀ M : ℝ, M₀ ≤ M → ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n),
      |sqrt2DPiece β (B n) (plSpec α (c n) (N n)) i M (gammaOf (N n) (B n)) /
          (aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum i / (N n : ℝ))) - 1|
        ≤ C / M + ε := by
  by_cases hαβ : 0 < α ∧ 0 < β ∧ β < 1
  · obtain ⟨hα, hβ0, hβ1⟩ := hαβ
    obtain ⟨K, hK, hdet⟩ := pg6p2_tail_det hα hβ0 hβ1
    obtain ⟨cΨ, hcΨ, hlow⟩ := pg6p2_psi_lower hα
    refine ⟨K, 1, one_pos, fun N B c hreg M hM ε hε => ?_⟩
    have hM0 : 0 < M := by linarith
    filter_upwards [hreg.hγ.eventually_ge_atTop (4 * M),
      hreg.hγ.eventually_ge_atTop (M * K / (ε * cΨ) + 1),
      hreg.hB.eventually_ge_atTop (max 2 K)] with n h1 h3 h4 i
    have hB2 : (2:ℝ) ≤ (B n : ℝ) := (le_max_left _ _).trans h4
    have hB2' : 2 ≤ B n := by exact_mod_cast hB2
    have hKB : K ≤ (B n : ℝ) * M := by
      have : K ≤ (B n : ℝ) := (le_max_right _ _).trans h4
      nlinarith
    have hγ : 4 * M ≤ gammaOf (N n) (B n) := h1
    have hγ0 := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    have hNr : (0:ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hdi := hdet (N n) (B n) (c n) i M (hreg.hNpos n) hB2' (hreg.hcpos n) hM hγ hKB
    set γ := gammaOf (N n) (B n)
    set ψ := psiRes α (M / γ) (rowNum i / (N n : ℝ)) with hψ
    set a := aN α (c n) (N n)
    set T := sqrt2DPiece β (B n) (plSpec α (c n) (N n)) i M γ
    have han : 0 < a := pg6p2_aN_pos (α := α) (hreg.hcpos n) (hreg.hNpos n)
    have hx01 : rowNum i / (N n : ℝ) ∈ Ioc (0:ℝ) 1 :=
      ⟨div_pos (pg6_rowNum_pos i) hNr, (div_le_one hNr).2 (pg6p2_rowNum_le i)⟩
    have h3' : M * K / (ε * cΨ) + 1 ≤ γ := h3
    have hMγ : M / γ ≤ 1 / 4 := by rw [div_le_iff₀ hγ0]; linarith
    have hψc : cΨ ≤ ψ := hlow _ hx01 (M / γ) (div_pos hM0 hγ0) hMγ
    have hψ0 : 0 < ψ := lt_of_lt_of_le hcΨ hψc
    have hden : 0 < a * ψ := mul_pos han hψ0
    have e : T / (a * ψ) - 1 = (T - a * ψ) / (a * ψ) := by
      have := han.ne'; have := hψ0.ne'; field_simp
    rw [e, abs_div, abs_of_pos hden, div_le_iff₀ hden]
    refine hdi.trans ?_
    have hsm : K * (M / γ) ^ 2 ≤ ε * cΨ := by
      have h5 : M / γ ≤ ε * cΨ / K := by
        rw [div_le_div_iff₀ hγ0 hK]
        have : M * K / (ε * cΨ) < γ := by linarith [h3']
        rw [div_lt_iff₀ (by positivity)] at this
        nlinarith
      have h6 : (M / γ) ^ 2 ≤ M / γ := by
        have := div_pos hM0 hγ0
        nlinarith
      calc K * (M / γ) ^ 2 ≤ K * (ε * cΨ / K) := mul_le_mul_of_nonneg_left (h6.trans h5) hK.le
        _ = ε * cΨ := by field_simp
    calc a * (K / M * ψ + K * (M / γ) ^ 2) ≤ a * (K / M * ψ + ε * ψ) := by
          apply mul_le_mul_of_nonneg_left _ han.le
          nlinarith
      _ = (K / M + ε) * (a * ψ) := by ring
  · exact ⟨1, 1, one_pos, fun N B c hreg => absurd ⟨hreg.hα, hreg.hβ0, hreg.hβ1⟩ hαβ⟩

/-! ### P-G.6.P4 helpers: the large-`y` end -/

private lemma pg6p5_phi_eq {α β y : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) (hy : 0 < y) :
    profPhi α β y = 1 / Real.pi * ∫ m in Ioi (0:ℝ), Aav β m * m ^ (-(α + 1) / 2) *
      (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m) := by
  simpa only [Aav] using (pg6p4_change_integral (α := α) (β := β) (y := y) hβ0 hβ1
    (by simpa only [Aav] using (pg6p4_m_integrable hα hβ0 hβ1 hy))).2

/-- `h(m) = 𝒜(m) √m` tends to `𝔰_2^{-1/2}` as `m ↓ 0`. -/
private lemma pg6p5_A_sqrt_tendsto {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    Tendsto (fun m : ℝ => Aav β m * m ^ (1 / 2 : ℝ)) (𝓝[>] 0)
      (𝓝 (1 / Real.sqrt (sPow β 2))) := by
  have hs2 : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]; apply div_pos <;> linarith
  have hQ := lem_app_pl_weights_i_Q hβ0.le hβ1
  have hE := lem_app_pl_weights_i_E hβ0.le hβ1
  have hmne : ∀ᶠ m : ℝ in 𝓝[>] 0, m / sPow β 2 ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact (div_pos hm hs2).ne'
  have hmne' : ∀ᶠ m : ℝ in 𝓝[>] 0, m ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact ne_of_gt hm
  have hQ1 := (isEquivalent_iff_tendsto_one hmne).1 hQ
  have hE1 := (isEquivalent_iff_tendsto_one hmne').1 hE
  -- Q/m → 1/s2
  have hQm : Tendsto (fun m : ℝ => Qm β m / m) (𝓝[>] 0) (𝓝 (1 / sPow β 2)) := by
    have := hQ1.div_const (sPow β 2)
    refine (this.congr' ?_).trans_eq (by simp)
    filter_upwards [self_mem_nhdsWithin] with m hm
    have hm' : (0:ℝ) < m := hm
    simp only [Pi.div_apply]
    field_simp
  have hEm : Tendsto (fun m : ℝ => m / Efun β m) (𝓝[>] 0) (𝓝 1) := by
    have := hE1.inv₀ one_ne_zero
    refine (this.congr' ?_).trans_eq (by simp)
    filter_upwards [self_mem_nhdsWithin] with m hm
    simp only [Pi.div_apply, inv_div]
  have hsq : Tendsto (fun m : ℝ => Real.sqrt (Qm β m / m)) (𝓝[>] 0)
      (𝓝 (Real.sqrt (1 / sPow β 2))) :=
    (Real.continuous_sqrt.tendsto _).comp hQm
  have hQ0 : Tendsto (Qm β) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun m : ℝ => (Qm β m / m) * m) (𝓝[>] 0) (𝓝 ((1 / sPow β 2) * 0)) :=
      hQm.mul (tendsto_id.mono_left nhdsWithin_le_nhds)
    rw [mul_zero] at h1
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m hm
    have hm' : (0:ℝ) < m := hm
    field_simp
  have hLw : Tendsto (fun m : ℝ => Lw (emaW β) (Qm β m)) (𝓝[>] 0) (𝓝 1) := by
    have hw := pg6p4_wseq hβ0.le hβ1
    obtain ⟨-, -, -, hLc, -, -, -, -, hL0, -⟩ := lem_app_de_scalar_ii hw
    have hL0' : Lw (emaW β) 0 = 1 := by rw [hL0]; exact tsum_emaW hβ0.le hβ1
    have hc := (hLc 0 (Set.mem_Ici.2 le_rfl)).tendsto
    rw [hL0'] at hc
    refine hc.comp (tendsto_nhdsWithin_iff.2 ⟨hQ0, ?_⟩)
    filter_upwards [self_mem_nhdsWithin] with m hm
    exact Set.mem_Ici.2 (pg6p4_Qm_spec hβ0 hβ1 hm).1.le
  have hprod := (hsq.mul hLw).mul hEm
  have hval : Real.sqrt (1 / sPow β 2) * 1 * 1 = 1 / Real.sqrt (sPow β 2) := by
    rw [mul_one, mul_one, Real.sqrt_div' _ hs2.le, Real.sqrt_one]
  rw [hval] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  have hm' : (0:ℝ) < m := hm
  have hQpos := (pg6p4_Qm_spec hβ0 hβ1 hm').1
  have hEpos := pg6p4_E_pos hβ0 hβ1 hm'
  unfold Aav
  rw [Real.sqrt_div hQpos.le, ← Real.sqrt_eq_rpow]
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.2 hm'
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm'.le
  field_simp
  rw [Real.sq_sqrt hm'.le]
  ring


private lemma pg6p5_A_sqrt_small {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ B : ℝ, 0 < B ∧ ∀ m : ℝ, 0 < m → m ≤ 1 → 0 ≤ Aav β m * m ^ (1 / 2 : ℝ) ∧
      Aav β m * m ^ (1 / 2 : ℝ) ≤ B := by
  obtain ⟨c, hc, hcF⟩ := pg6p2_F_lower hβ0 hβ1 (zero_lt_one : (0:ℝ) < 1)
  obtain ⟨cE, CE, hcE, -, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  refine ⟨1 / (Real.sqrt c * cE), by positivity, fun m hm hm1 => ?_⟩
  obtain ⟨hQ, hr⟩ := pg6p4_Qm_spec hβ0 hβ1 hm
  have hLpos := pg6p4_Lw_pos hβ0 hβ1 hQ.le
  have hLle := pg6p4_Lw_le_one hβ0 hβ1 hQ.le
  have hElo : cE * m ≤ Efun β m := by simpa [min_eq_left hm1] using (hE m hm).1
  have hEpos : 0 < Efun β m := lt_of_lt_of_le (mul_pos hcE hm) hElo
  have hFc := hcF m ⟨hm, hm1⟩
  have hrm : Qm β m * Fw (emaW β) (Qm β m) = m := hr
  have hQle : Qm β m ≤ m / c := by
    rw [le_div_iff₀ hc]; nlinarith
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hsqQ : Real.sqrt (Qm β m) ≤ Real.sqrt m / Real.sqrt c := by
    rw [← Real.sqrt_div hm.le]; exact Real.sqrt_le_sqrt hQle
  have hsm : (m ^ (1 / 2 : ℝ)) = Real.sqrt m := (Real.sqrt_eq_rpow m).symm
  rw [hsm]
  have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.2 hm
  have hmm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm.le
  constructor
  · unfold Aav; positivity
  · unfold Aav
    rw [div_mul_eq_mul_div, div_le_iff₀ hEpos]
    have h1 : Real.sqrt (Qm β m) * Lw (emaW β) (Qm β m) * Real.sqrt m ≤ Real.sqrt m / Real.sqrt c * 1 * Real.sqrt m := by
      apply mul_le_mul _ le_rfl hsm0.le (by positivity)
      exact mul_le_mul hsqQ hLle hLpos.le (by positivity)
    have h2 : Real.sqrt m / Real.sqrt c * 1 * Real.sqrt m = m / Real.sqrt c := by
      rw [mul_one, div_mul_eq_mul_div, hmm]
    have h3 : m / Real.sqrt c ≤ 1 / (Real.sqrt c * cE) * Efun β m := by
      calc m / Real.sqrt c = 1 / (Real.sqrt c * cE) * (cE * m) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hElo (by positivity)
    linarith

private lemma pg6p5_hh_facts {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ContinuousOn (fun m : ℝ => Aav β m * m ^ (1 / 2 : ℝ) * (1 + (α - 1) * (Efun β m / m))) (Ioi 0) ∧
    Tendsto (fun m : ℝ => Aav β m * m ^ (1 / 2 : ℝ) * (1 + (α - 1) * (Efun β m / m))) (𝓝[>] 0)
      (𝓝 (1 / Real.sqrt (sPow β 2) * α)) ∧
    ∃ B K1 : ℝ, 0 < B ∧ 0 < K1 ∧ ∀ w tt : ℝ, 0 < w → 0 < tt → tt ≤ 1 →
      0 ≤ Aav β (tt * w) * (tt * w) ^ (1 / 2 : ℝ) * (1 + (α - 1) * (Efun β (tt * w) / (tt * w))) ∧
      Aav β (tt * w) * (tt * w) ^ (1 / 2 : ℝ) * (1 + (α - 1) * (Efun β (tt * w) / (tt * w))) ≤
        B + K1 * w ^ (1 / 2 : ℝ) := by
  have hα0 : 0 < α := by linarith
  refine ⟨?_, ?_, ?_⟩
  · refine ((pg6p4_Aav_continuousOn hβ0 hβ1).mul ?_).mul ?_
    · exact ContinuousOn.rpow_const continuousOn_id (fun m hm => Or.inl (ne_of_gt hm))
    · exact continuousOn_const.add (continuousOn_const.mul
        ((pg6p5_Efun_continuousOn hβ0 hβ1).div continuousOn_id (fun m hm => ne_of_gt hm)))
  · have hE := lem_app_pl_weights_i_E hβ0.le hβ1
    have hmne' : ∀ᶠ m : ℝ in 𝓝[>] 0, m ≠ 0 := by
      filter_upwards [self_mem_nhdsWithin] with m hm
      exact ne_of_gt hm
    have hE1 := (isEquivalent_iff_tendsto_one hmne').1 hE
    have hE2 : Tendsto (fun m : ℝ => Efun β m / m) (𝓝[>] 0) (𝓝 1) := hE1
    have hT : Tendsto (fun m : ℝ => 1 + (α - 1) * (Efun β m / m)) (𝓝[>] 0) (𝓝 α) := by
      have := (tendsto_const_nhds (x := (1:ℝ))).add (hE2.const_mul (α - 1))
      simpa using this
    exact (pg6p5_A_sqrt_tendsto hβ0 hβ1).mul hT
  · obtain ⟨BA, hBA, hsmall⟩ := pg6p5_A_sqrt_small hβ0 hβ1
    obtain ⟨K, C, hK, hC, -, hAl⟩ := pg6p4_Aav_upper hβ0 hβ1
    refine ⟨α * BA, α * C, by positivity, by positivity, fun w tt hw htt htt1 => ?_⟩
    have hm : 0 < tt * w := mul_pos htt hw
    have hT := pg6p4_theta_bounds hα hβ0 hβ1 hm
    have hT' : 1 ≤ 1 + (α - 1) * (Efun β (tt * w) / (tt * w)) ∧
        1 + (α - 1) * (Efun β (tt * w) / (tt * w)) ≤ α := by
      simpa only [mul_div_assoc] using hT
    have hsq : 0 ≤ w ^ (1 / 2 : ℝ) := Real.rpow_nonneg hw.le _
    rcases le_total (tt * w) 1 with hm1 | hm1
    · obtain ⟨h0, h1⟩ := hsmall (tt * w) hm hm1
      refine ⟨mul_nonneg h0 (by linarith [hT'.1]), ?_⟩
      calc _ ≤ BA * α := mul_le_mul h1 hT'.2 (by linarith [hT'.1]) hBA.le
        _ = α * BA := by ring
        _ ≤ α * BA + α * C * w ^ (1 / 2 : ℝ) := by
          have : 0 ≤ α * C * w ^ (1 / 2 : ℝ) := by positivity
          linarith
    · obtain ⟨h0, h1⟩ := hAl (tt * w) hm1
      have hsq1 : (tt * w) ^ (1 / 2 : ℝ) ≤ w ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow hm.le (by nlinarith) (by norm_num)
      have hsq0 : 0 ≤ (tt * w) ^ (1 / 2 : ℝ) := Real.rpow_nonneg hm.le _
      refine ⟨mul_nonneg (mul_nonneg h0 hsq0) (by linarith [hT'.1]), ?_⟩
      have : Aav β (tt * w) * (tt * w) ^ (1 / 2 : ℝ) ≤ C * w ^ (1 / 2 : ℝ) :=
        mul_le_mul h1 hsq1 hsq0 hC.le
      calc _ ≤ (C * w ^ (1 / 2 : ℝ)) * α := mul_le_mul this hT'.2 (by linarith [hT'.1]) (by positivity)
        _ = α * C * w ^ (1 / 2 : ℝ) := by ring
        _ ≤ α * BA + α * C * w ^ (1 / 2 : ℝ) := by
          have : 0 ≤ α * BA := by positivity
          linarith

private def pg6p5_k0 (α w : ℝ) : ℝ := w ^ (α / 2 - 1) / (1 + w ^ α)

private lemma pg6p5_k0_facts {α : ℝ} (hα : 1 < α) :
    IntegrableOn (pg6p5_k0 α) (Ioi 0) ∧ ∫ w in Ioi (0:ℝ), pg6p5_k0 α w = Real.pi / α ∧
    IntegrableOn (fun w : ℝ => w ^ (1 / 2 : ℝ) * pg6p5_k0 α w) (Ioi 0) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨h1, h2⟩ := pg6p5_beta (α := α) (s := α / 2) hα0 (by linarith) (by linarith)
  refine ⟨h1, ?_, ?_⟩
  · rw [show pg6p5_k0 α = fun w => w ^ (α / 2 - 1) / (1 + w ^ α) from rfl, h2]
    have : Real.sin (Real.pi * (α / 2) / α) = 1 := by
      rw [show Real.pi * (α / 2) / α = Real.pi / 2 by field_simp]
      exact Real.sin_pi_div_two
    rw [this]; ring
  · obtain ⟨h3, -⟩ := pg6p5_beta (α := α) (s := (α + 1) / 2) hα0 (by linarith) (by linarith)
    refine h3.congr_fun (fun w hw => ?_) measurableSet_Ioi
    have hw' : (0:ℝ) < w := hw
    unfold pg6p5_k0
    rw [← mul_div_assoc, ← Real.rpow_add hw']
    congr 2; ring

private lemma pg6p5_P_scale {α β y : ℝ} (hα : 1 < α) (hy : 0 < y) :
    ∫ m in Ioi (0:ℝ), Aav β m * m ^ (-(α + 1) / 2) *
      (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m) =
    y ^ (1 / 2 : ℝ) * ∫ w in Ioi (0:ℝ),
      (Aav β (y ^ (-(1 / α)) * w) * (y ^ (-(1 / α)) * w) ^ (1 / 2 : ℝ) *
        (1 + (α - 1) * (Efun β (y ^ (-(1 / α)) * w) / (y ^ (-(1 / α)) * w)))) * pg6p5_k0 α w := by
  have hα0 : 0 < α := by linarith
  set tt : ℝ := y ^ (-(1 / α)) with htt
  have htt0 : 0 < tt := Real.rpow_pos_of_pos hy _
  have httα : tt ^ α = y⁻¹ := by
    rw [htt, ← Real.rpow_mul hy.le, show -(1 / α) * α = -1 by field_simp, Real.rpow_neg_one]
  set g : ℝ → ℝ := fun m => Aav β m * m ^ (-(α + 1) / 2) *
      (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m) with hg
  have hscale := integral_comp_mul_left_Ioi g 0 htt0
  simp only [mul_zero, smul_eq_mul] at hscale
  have hpt : ∀ w ∈ Ioi (0:ℝ), g (tt * w) = tt ^ (-(α + 2) / 2) *
      ((Aav β (tt * w) * (tt * w) ^ (1 / 2 : ℝ) *
        (1 + (α - 1) * (Efun β (tt * w) / (tt * w)))) * pg6p5_k0 α w) := by
    intro w hw
    have hw' : (0:ℝ) < w := hw
    have hm : 0 < tt * w := mul_pos htt0 hw'
    have hya : y * (tt * w) ^ α = w ^ α := by
      rw [Real.mul_rpow htt0.le hw'.le, httα]
      field_simp
    have e1 : (tt * w) ^ (-(α + 1) / 2) = (tt * w) ^ (1 / 2 : ℝ) * (tt ^ (-(α + 2) / 2) * w ^ (-(α + 2) / 2)) := by
      rw [← Real.mul_rpow htt0.le hw'.le, ← Real.rpow_add hm]; congr 1; ring
    have e2 : pg6p5_k0 α w = w ^ (-(α + 2) / 2) * (w ^ α / (1 + w ^ α)) := by
      unfold pg6p5_k0
      rw [mul_div_assoc', ← Real.rpow_add hw']
      congr 2; ring
    simp only [hg]
    rw [hya, e1, e2]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul] at hscale
  have hsc : ∫ m in Ioi (0:ℝ), g m = tt * (tt ^ (-(α + 2) / 2) * ∫ w in Ioi (0:ℝ),
      (Aav β (tt * w) * (tt * w) ^ (1 / 2 : ℝ) *
        (1 + (α - 1) * (Efun β (tt * w) / (tt * w)))) * pg6p5_k0 α w) := by
    rw [hscale]; field_simp
  show ∫ m in Ioi (0:ℝ), g m = _
  rw [hsc, ← mul_assoc, ← Real.rpow_one_add' htt0.le (by linarith [show (0:ℝ) < α from hα0] : (1 + -(α + 2) / 2) ≠ 0)]
  congr 1
  rw [htt, ← Real.rpow_mul hy.le]
  congr 1
  field_simp
  ring

private lemma pg6p5_ii_proof {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsEquivalent atTop (fun y : ℝ => profPhi α β y) (fun y : ℝ => Real.sqrt (y / sPow β 2)) := by
  have hα0 : 0 < α := by linarith
  have hs2 : 0 < sPow β 2 := by rw [sPow_two hβ0.le hβ1]; apply div_pos <;> linarith
  obtain ⟨hcont, hlim, B, K1, hB, hK1, hbd⟩ := pg6p5_hh_facts hα hβ0 hβ1
  obtain ⟨hk0, hk0I, hk1⟩ := pg6p5_k0_facts hα
  set hh : ℝ → ℝ := fun m => Aav β m * m ^ (1 / 2 : ℝ) * (1 + (α - 1) * (Efun β m / m)) with hhdef
  set L : ℝ := 1 / Real.sqrt (sPow β 2) with hL
  have hk0nn : ∀ w : ℝ, 0 < w → 0 ≤ pg6p5_k0 α w := by
    intro w hw
    unfold pg6p5_k0
    have := Real.rpow_pos_of_pos hw α
    positivity
  have hk0c : ContinuousOn (pg6p5_k0 α) (Ioi 0) := by
    unfold pg6p5_k0
    refine ContinuousOn.div (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw)))
      (continuousOn_const.add (ContinuousOn.rpow_const continuousOn_id (fun w hw => Or.inl (ne_of_gt hw)))) ?_
    intro w hw
    have := Real.rpow_pos_of_pos (show (0:ℝ) < w from hw) α
    positivity
  -- DCT
  have hdct : Tendsto (fun y : ℝ => ∫ w in Ioi (0:ℝ), hh (y ^ (-(1 / α)) * w) * pg6p5_k0 α w) atTop
      (𝓝 (∫ w in Ioi (0:ℝ), (L * α) * pg6p5_k0 α w)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun w => B * pg6p5_k0 α w + K1 * (w ^ (1 / 2 : ℝ) * pg6p5_k0 α w)) ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
      have hc : ContinuousOn (fun w : ℝ => hh (y ^ (-(1 / α)) * w) * pg6p5_k0 α w) (Ioi 0) := by
        refine (hcont.comp (continuousOn_const.mul continuousOn_id) ?_).mul hk0c
        intro w hw
        exact mul_pos (Real.rpow_pos_of_pos hy _) hw
      exact hc.aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [eventually_ge_atTop (1:ℝ)] with y hy
      have hy0 : 0 < y := by linarith
      have htt0 : 0 < y ^ (-(1 / α)) := Real.rpow_pos_of_pos hy0 _
      have htt1 : y ^ (-(1 / α)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hy (by have : 0 < 1 / α := by positivity
                                                    linarith)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw' : (0:ℝ) < w := hw
      obtain ⟨h0, h1⟩ := hbd w (y ^ (-(1 / α))) hw' htt0 htt1
      have hk := hk0nn w hw'
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 hk)]
      calc hh (y ^ (-(1 / α)) * w) * pg6p5_k0 α w ≤ (B + K1 * w ^ (1 / 2 : ℝ)) * pg6p5_k0 α w :=
            mul_le_mul_of_nonneg_right h1 hk
        _ = _ := by ring
    · exact (hk0.const_mul B).add ((hk1.const_mul K1))
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hw' : (0:ℝ) < w := hw
      have hp : Tendsto (fun y : ℝ => y ^ (-(1 / α)) * w) atTop (𝓝[>] 0) := by
        have h0 : Tendsto (fun y : ℝ => y ^ (-(1 / α))) atTop (𝓝 0) :=
          tendsto_rpow_neg_atTop (by positivity)
        refine tendsto_nhdsWithin_iff.2 ⟨by simpa using h0.mul_const w, ?_⟩
        filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
        exact mul_pos (Real.rpow_pos_of_pos hy _) hw'
      exact (hlim.comp hp).mul_const _
  rw [integral_const_mul, hk0I] at hdct
  have hval : L * α * (Real.pi / α) = Real.pi * L := by field_simp
  rw [hval] at hdct
  have hsq0 : 0 < Real.sqrt (sPow β 2) := Real.sqrt_pos.2 hs2
  have hfin := hdct.const_mul (Real.sqrt (sPow β 2) / Real.pi)
  have hone : Real.sqrt (sPow β 2) / Real.pi * (Real.pi * L) = 1 := by
    rw [hL]; field_simp
  rw [hone] at hfin
  refine isEquivalent_of_tendsto_one (hfin.congr' ?_)
  filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
  show Real.sqrt (sPow β 2) / Real.pi * _ = profPhi α β y / Real.sqrt (y / sPow β 2)
  rw [pg6p5_phi_eq hα hβ0 hβ1 hy, pg6p5_P_scale hα hy, Real.sqrt_div hy.le, ← Real.sqrt_eq_rpow]
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have hpi := Real.pi_pos
  have key : ∀ I : ℝ, Real.sqrt (sPow β 2) / Real.pi * I =
      1 / Real.pi * (Real.sqrt y * I) / (Real.sqrt y / Real.sqrt (sPow β 2)) := by
    intro I; field_simp
  exact key _

/-- `lem:app-pl-super`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{lemma}[The supercritical drift profile]\label{lem:app-pl-super}
Let $\alpha>1$ and $p_\alpha\defeq(\alpha-1)/(2\alpha)$. The function $\Phi_{\alpha,\bmom}$ of
\cref{eqn:app-pl-Phi} is finite, positive and continuous on $(0,\infty)$, and
\[
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\quad(y\to\infty),\qquad \Phi_{\alpha,\bmom}(y)\sim d_\alpha y^{p_\alpha}\quad(y\downarrow0).
\]
Under \cref{assum:app-pl-regime}, for every row sequence $i\to\infty$ with $i/N\to0$,
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{b_N}\sim\Phi_{\alpha,\bmom}\big((i_{\mathrm c}/i)^\alpha\big).
\]
\end{lemma}
-/
theorem lem_app_pl_super_ii {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    IsEquivalent atTop (fun y : ℝ => profPhi α β y) (fun y : ℝ => Real.sqrt (y / sPow β 2)) := by
  exact pg6p5_ii_proof hα hβ0 hβ1

/-! #### Abstract asymptotic combinators -/

private lemma pg6_equiv_of_err {D X : ℕ → ℝ} (hX : ∀ᶠ n in atTop, 0 < X n) (C M0 : ℝ)
    (h : ∀ M : ℝ, M0 ≤ M → ∀ ε > 0, ∀ᶠ n in atTop, |D n - X n| ≤ (C / M + ε) * X n) :
    IsEquivalent atTop D X := by
  rw [IsEquivalent, isLittleO_iff]
  intro c hc
  set M : ℝ := max (max M0 1) (2 * |C| / c) with hMdef
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : M0 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hMc : 2 * |C| / c ≤ M := le_max_right _ _
  have hMpos : 0 < M := by linarith
  have hCM : C / M ≤ c / 2 := by
    have h1 : |C| ≤ M * c / 2 := by
      rw [div_le_iff₀ hc] at hMc; linarith
    calc C / M ≤ |C| / M := div_le_div_of_nonneg_right (le_abs_self C) hMpos.le
      _ ≤ (M * c / 2) / M := div_le_div_of_nonneg_right h1 hMpos.le
      _ = c / 2 := by field_simp
  filter_upwards [h M hM0 (c / 2) (by positivity), hX] with n hn hXn
  rw [Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hXn]
  calc |D n - X n| ≤ (C / M + c / 2) * X n := hn
    _ ≤ c * X n := by nlinarith

/-- Subsequence principle for equivalence of a sequence with a positive one. -/
private lemma pg6_equiv_subseq {u v : ℕ → ℝ} (hv : ∀ n, 0 < v n)
    (h : ∀ φ : ℕ → ℕ, Tendsto φ atTop atTop → ∃ ψ : ℕ → ℕ, Tendsto ψ atTop atTop ∧
      IsEquivalent atTop (fun n => u (φ (ψ n))) (fun n => v (φ (ψ n)))) :
    IsEquivalent atTop u v := by
  apply isEquivalent_of_tendsto_one
  show Tendsto (fun n => u n / v n) atTop (𝓝 1)
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨ψ, hψ, hE⟩ := h φ hφ
  refine ⟨ψ, ?_⟩
  have := (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun n => (hv _).ne'))).1 hE
  exact this


private lemma pg6_reg_comp {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    assum_app_pl_regime α β (fun n => N (φ n)) (fun n => B (φ n)) (fun n => c (φ n)) :=
  ⟨hreg.hα, hreg.hβ0, hreg.hβ1, fun n => hreg.hNpos _, fun n => hreg.hBpos _,
    fun n => hreg.hcpos _, hreg.hN.comp hφ, hreg.hB.comp hφ, hreg.hγ.comp hφ⟩

private lemma pg6_gamma_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) :
    Tendsto (fun n => gammaOf (N n) (B n)) atTop atTop := hreg.hγ

/-- The combination of the head, the tail and the split. -/
private lemma pg6_combine {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (H T : ℕ → ℝ) (hH : ∀ n, 0 < H n) (hT : ∀ n, 0 ≤ T n)
    (hhead : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M - H n| ≤ ε * (H n + T n))
    (hA : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) - T n|
        ≤ ε * (H n + T n)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => H n + T n) := by
  obtain ⟨C, M₀, hM₀, htail⟩ := lem_app_pl_tail (α := α) (β := β)
  have hX : ∀ n, 0 < H n + T n := fun n => by linarith [hH n, hT n]
  refine pg6_equiv_of_err (Eventually.of_forall hX) (2 * |C|) (max M₀ (2 * |C| + 1)) ?_
  intro M hM ε hε
  have hMM0 : M₀ ≤ M := le_trans (le_max_left _ _) hM
  have hMC : 2 * |C| + 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMpos : 0 < M := by linarith
  set ε1 : ℝ := min (1 / 4) (ε / 4) with hε1
  have hε1pos : 0 < ε1 := lt_min (by norm_num) (by positivity)
  have hε1a : ε1 ≤ 1 / 4 := min_le_left _ _
  have hε1b : 4 * ε1 ≤ ε := by have := min_le_right (1 / 4 : ℝ) (ε / 4); linarith
  have hCM : |C| / M ≤ 1 / 2 := by
    rw [div_le_iff₀ hMpos]; nlinarith [abs_nonneg C]
  filter_upwards [htail N B c hreg M hMM0 ε1 hε1pos, hhead M hMpos ε1 hε1pos,
    hA M hMpos ε1 hε1pos, hreg.hγ.eventually_gt_atTop M] with n htl hhd hAn hγM
  have hsplit := pg6_split (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n) (hreg.hNpos n)
    (pg6_plSpec_anti hreg.hα (hreg.hcpos n)) (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n)
    hMpos hγM
  set t := sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n)) with ht
  set h := sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M with hh
  set A := aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) with hAdef
  have htl' := htl (i n)
  have hX := hX n
  have hHn := hH n
  have hTn := hT n
  have hAT : |A - T n| ≤ ε1 * (H n + T n) := hAn
  have hAabs : |A| ≤ 2 * (H n + T n) := by
    have : |A| ≤ |T n| + |A - T n| := by
      have := abs_add_le (T n) (A - T n)
      simpa using this
    rw [abs_of_nonneg hTn] at this
    nlinarith
  have hCle : C / M ≤ |C| / M := div_le_div_of_nonneg_right (le_abs_self C) hMpos.le
  have hr : |t / A - 1| ≤ |C| / M + ε1 := by linarith
  have hA0 : A ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hr
    norm_num at hr
    linarith
  have htA : |t - A| ≤ (|C| / M + ε1) * |A| := by
    have : t - A = A * (t / A - 1) := by field_simp
    rw [this, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hr (abs_nonneg _) |>.trans (le_refl _)
  have hrnn : 0 ≤ |C| / M + ε1 := by positivity
  have h1 : (|C| / M + ε1) * |A| ≤ (|C| / M + ε1) * (2 * (H n + T n)) :=
    mul_le_mul_of_nonneg_left hAabs hrnn
  have hD : Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) = h + t := hsplit
  show |Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) - (H n + T n)| ≤ _
  rw [hD]
  have e1 : |h + t - (H n + T n)| ≤ |h - H n| + |t - A| + |A - T n| := by
    have : h + t - (H n + T n) = (h - H n) + (t - A) + (A - T n) := by ring
    rw [this]
    exact (abs_add_le _ _).trans (by linarith [abs_add_le (h - H n) (t - A)])
  have e2 : (2 * |C|) / M = 2 * (|C| / M) := by ring
  rw [e2]
  have e3 := mul_le_mul_of_nonneg_right hε1b hX.le
  nlinarith [e1, hhd, htA, h1, hAT, e3]


/-! #### The restricted profile approaches the full one, uniformly for `x` bounded below -/

private lemma pg6_contV_pos {α : ℝ} (hα : 0 < α) {p : ℝ} (hp : p ∈ Ioo (0:ℝ) 1) :
    0 < contV α p := by
  have hex : ∃ V, V ∈ Ioi (0:ℝ) ∧ contS α V = p := (def_app_pl_profiles_S_bij hα).2.surjOn hp
  exact Function.invFunOn_mem hex

private lemma pg6_psi_approx {α : ℝ} (hα : 0 < α) {x0 : ℝ} (hx0 : 0 < x0) (hx01 : x0 ≤ 1) :
    ∀ ε > 0, ∃ η0 : ℝ, 0 < η0 ∧ η0 ≤ 1 ∧ ∀ η : ℝ, 0 < η → η ≤ η0 → ∀ x : ℝ, x0 ≤ x → x ≤ 1 →
      |psiRes α η x - profPsi α x| ≤ ε := by
  intro ε hε
  set g : ℝ → ℝ → ℝ := fun x p => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p with hg
  have hint : ∀ x ∈ Ioc (0:ℝ) 1, IntervalIntegrable (g x) volume 0 1 :=
    lem_app_pl_Psi_i_integrable hα
  have hint0 := hint x0 ⟨hx0, hx01⟩
  have hcont := intervalIntegral.continuousOn_primitive_interval' hint0
    (left_mem_uIcc (a := (0:ℝ)) (b := 1))
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hcw : ContinuousWithinAt (fun b => ∫ t in (0:ℝ)..b, g x0 t) (uIcc 0 1) 0 :=
    hcont 0 (left_mem_uIcc)
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ, hδ, hδ'⟩ := hcw (ε / c0) (by positivity)
  refine ⟨min (δ / 2) 1, lt_min (by positivity) one_pos, min_le_right _ _, ?_⟩
  intro η hη hηle x hxl hxu
  have hη1 : η ≤ 1 := hηle.trans (min_le_right _ _)
  have hηδ : η < δ := lt_of_le_of_lt (hηle.trans (min_le_left _ _)) (by linarith)
  have hxpos : 0 < x := lt_of_lt_of_le hx0 hxl
  have hix := hint x ⟨hxpos, hxu⟩
  have hi0η : IntervalIntegrable (g x) volume 0 η :=
    hix.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hη.le]
      exact Icc_subset_Icc le_rfl hη1)
  have hiη1 : IntervalIntegrable (g x) volume η 1 :=
    hix.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hη1]
      exact Icc_subset_Icc hη.le le_rfl)
  have hdiff : profPsi α x - psiRes α η x = c0 * ∫ t in (0:ℝ)..η, g x t := by
    unfold profPsi psiRes
    have := intervalIntegral.integral_add_adjacent_intervals hi0η hiη1
    have e : ∫ t in (0:ℝ)..1, g x t = ∫ p in (0:ℝ)..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := rfl
    have e2 : ∫ t in η..1, g x t = ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p := rfl
    rw [← e, ← e2, ← this]
    ring
  -- monotonicity in x
  have hmono : ∀ p ∈ Ioo (0:ℝ) η, g x p ≤ g x0 p := by
    intro p hp
    have hp1 : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, lt_of_lt_of_le hp.2 hη1⟩
    have hV := pg6_contV_pos hα hp1
    simp only [hg, profF]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    have hxa : x0 ^ α ≤ x ^ α := Real.rpow_le_rpow hx0.le hxl hα.le
    have hx0a : 0 < x0 ^ α := Real.rpow_pos_of_pos hx0 _
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hV hx0a]
  have hnn : ∀ p ∈ Icc (0:ℝ) η, 0 ≤ g x p := by
    intro p hp
    rcases hp.1.eq_or_lt with h0 | h0
    · simp only [hg, ← h0, zero_mul, div_zero, Real.sqrt_zero, le_refl]
    rcases (hp.2.trans hη1).eq_or_lt with h | h
    · simp only [hg, h, sub_self, zero_div, Real.sqrt_zero, zero_mul, le_refl]
    · have hp1 : p ∈ Ioo (0:ℝ) 1 := ⟨h0, h⟩
      have hV := pg6_contV_pos hα hp1
      simp only [hg, profF]
      have : 0 < x ^ α := Real.rpow_pos_of_pos hxpos _
      positivity
  have hi0η0 : IntervalIntegrable (g x0) volume 0 η :=
    hint0.mono_set (by
      rw [uIcc_of_le zero_le_one, uIcc_of_le hη.le]
      exact Icc_subset_Icc le_rfl hη1)
  have hle : ∫ t in (0:ℝ)..η, g x t ≤ ∫ t in (0:ℝ)..η, g x0 t :=
    intervalIntegral.integral_mono_on_of_le_Ioo hη.le hi0η hi0η0 hmono
  have hge : 0 ≤ ∫ t in (0:ℝ)..η, g x t :=
    intervalIntegral.integral_nonneg_of_ae_restrict hη.le (by
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall (fun p hp => hnn p hp))
  have hdist := hδ' (x := η) (by rw [uIcc_of_le zero_le_one]; exact ⟨hη.le, hη1⟩)
    (by rw [Real.dist_eq, sub_zero, abs_of_pos hη]; exact hηδ)
  rw [Real.dist_eq, intervalIntegral.integral_same, sub_zero] at hdist
  have h1 := (abs_lt.1 hdist).2
  rw [abs_sub_comm, abs_of_nonneg (by rw [hdiff]; positivity), hdiff]
  calc c0 * ∫ t in (0:ℝ)..η, g x t ≤ c0 * (ε / c0) :=
        mul_le_mul_of_nonneg_left (hle.trans h1.le) hc0.le
    _ = ε := by field_simp


private lemma pg6_aN_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) : 0 < aN α c N := by
  unfold aN
  have : (0 : ℝ) < N := by exact_mod_cast hN
  positivity

private lemma pg6_rowNum_le {N : ℕ} (i : Fin N) : rowNum i ≤ (N : ℝ) := by
  unfold rowNum
  have : ((i : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast i.isLt
  exact this

/-- `√(μ_i/(γ 𝔰_2)) = a_N √((i/N)^{-α}/(γ 𝔰_2))`. -/
private lemma pg6_H_eq {α c : ℝ} (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (i : Fin N)
    (s2 : ℝ) (hs2 : 0 < s2) :
    Real.sqrt (plSpec α c N i / (gammaOf N B * s2)) =
      aN α c N * Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * s2)) := by
  have hr := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ := pg6_gamma_pos hB hN
  have ha : aN α c N = Real.sqrt (c * (N : ℝ) ^ (-α)) := by
    unfold aN
    rw [Real.sqrt_mul hc.le, Real.sqrt_eq_rpow ((N : ℝ) ^ (-α)), ← Real.rpow_mul hNr.le]
    congr 2
    ring
  rw [ha, ← Real.sqrt_mul (by positivity), pg6_plSpec_eq]
  congr 1
  rw [Real.div_rpow hr.le hNr.le]
  have : 0 < (N : ℝ) ^ (-α) := Real.rpow_pos_of_pos hNr _
  field_simp


private lemma pg6_cutW_eq {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    cutW β α c N B i = Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * sPow β 2)) := by
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have ha := pg6_aN_pos (α := α) hc hN
  unfold cutW
  rw [pg6_H_eq hc hN hB i _ hs2]
  field_simp

private lemma pg6_cutW_pos {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) : 0 < cutW β α c N B i := by
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hγ := pg6_gamma_pos hB hN
  have hx : 0 < rowNum i / (N : ℝ) := div_pos (pg6_rowNum_pos i) (by exact_mod_cast hN)
  rw [pg6_cutW_eq hc hβ0 hβ1 hN hB i]
  apply Real.sqrt_pos.2
  have := Real.rpow_pos_of_pos hx (-α)
  positivity

private lemma pg6_aW_eq {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    aN α c N * cutW β α c N B i =
      Real.sqrt (plSpec α c N i / (gammaOf N B * sPow β 2)) := by
  have ha := pg6_aN_pos (α := α) hc hN
  unfold cutW
  field_simp



/-- Bulk rows: `x = i/N` bounded below. -/
private lemma pg6_bulk {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n)) {x0 : ℝ} (hx0 : 0 < x0)
    (hxl : ∀ᶠ n in atTop, x0 ≤ rowNum (i n) / (N n : ℝ)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  have hα := hreg.hα
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have hxu : ∀ n, rowNum (i n) / (N n : ℝ) ≤ 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    rw [div_le_one this]; exact pg6_rowNum_le _
  have hx0' : x0 ≤ 1 := by
    obtain ⟨n, hn⟩ := hxl.exists
    exact hn.trans (hxu n)
  obtain ⟨κ, hκ, hκle⟩ := lem_app_pl_Psi_i_lower hα
  set H : ℕ → ℝ := fun n => Real.sqrt (plSpec α (c n) (N n) (i n) /
    (gammaOf (N n) (B n) * sPow β 2)) with hHdef
  set T : ℕ → ℝ := fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)) with hTdef
  have han : ∀ n, 0 < aN α (c n) (N n) := fun n => pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n)
  have hH : ∀ n, 0 < H n := fun n => by
    simp only [hHdef]
    apply Real.sqrt_pos.2
    have := pg6_plSpec_pos (α := α) (hreg.hcpos n) (i n)
    have := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    positivity
  have hTκ : ∀ᶠ n in atTop, κ * aN α (c n) (N n) ≤ T n := by
    filter_upwards [hxl] with n hn
    simp only [hTdef]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hκle _ ⟨lt_of_lt_of_le hx0 hn, hxu n⟩) (han n).le
  have hT : ∀ᶠ n in atTop, 0 < T n := by
    filter_upwards [hTκ] with n hn
    exact lt_of_lt_of_le (mul_pos hκ (han n)) hn
  -- H ≤ ρ a
  set ρ : ℕ → ℝ := fun n => Real.sqrt (x0 ^ (-α) / (gammaOf (N n) (B n) * sPow β 2)) with hρ
  have hρ0 : Tendsto ρ atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => x0 ^ (-α) / (gammaOf (N n) (B n) * sPow β 2)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := x0 ^ (-α))).div_atTop
        (hreg.hγ.atTop_mul_const hs2)
      simpa [gammaOf] using this
    have := (Real.continuous_sqrt.tendsto 0).comp h1
    rw [Real.sqrt_zero] at this
    exact this
  have hHρ : ∀ᶠ n in atTop, H n ≤ ρ n * aN α (c n) (N n) := by
    filter_upwards [hxl] with n hn
    simp only [hHdef, hρ]
    rw [pg6_H_eq (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) _ hs2, mul_comm]
    refine mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt ?_) (han n).le
    have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact Real.rpow_le_rpow_of_nonpos hx0 hn (by linarith)
  -- H = o(T)
  have hHT : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, H n ≤ δ * T n := by
    intro δ hδ
    filter_upwards [hHρ, hTκ, hρ0.eventually (gt_mem_nhds (show (0:ℝ) < δ * κ by positivity))] with
      n h1 h2 h3
    have := han n
    calc H n ≤ ρ n * aN α (c n) (N n) := h1
      _ ≤ (δ * κ) * aN α (c n) (N n) := mul_le_mul_of_nonneg_right h3.le this.le
      _ = δ * (κ * aN α (c n) (N n)) := by ring
      _ ≤ δ * T n := mul_le_mul_of_nonneg_left h2 hδ.le
  have hT0 : ∀ n, 0 ≤ T n := fun n => by
    simp only [hTdef]
    exact mul_nonneg (han n).le (lem_app_pl_Psi_i_pos hα _ ⟨div_pos (pg6_rowNum_pos _)
      (by exact_mod_cast hreg.hNpos n), hxu n⟩).le
  have hcomb : IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => H n + T n) := by
    refine pg6_combine hreg i H T hH (fun n => ?_) ?_ ?_
    · simp only [hTdef]
      exact mul_nonneg (han n).le (lem_app_pl_Psi_i_pos hα _ ⟨div_pos (pg6_rowNum_pos _)
        (by exact_mod_cast hreg.hNpos n), hxu n⟩).le
    · intro M hM ε hε
      obtain ⟨Ch, hCh⟩ := lem_app_pl_head_i (α := α) (β := β) M hM
      set K : ℝ := |Ch| * Real.sqrt (sPow β 2) + 1 with hK
      have hKpos : 0 < K := by positivity
      filter_upwards [hCh N B c hreg, hHT (ε / K) (by positivity), hreg.hγ.eventually_ge_atTop M]
        with n h1 h2 h3
      have hpn := pg6_piece_nonneg (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n)
        (hreg.hNpos n) (pg6_plSpec_anti hα (hreg.hcpos n))
        (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n) (le_refl (0:ℝ)) h3
      have h1' := h1 (i n)
      have hsq : Real.sqrt (plSpec α (c n) (N n) (i n) / gammaOf (N n) (B n)) =
          Real.sqrt (sPow β 2) * H n := by
        simp only [hHdef]
        rw [← Real.sqrt_mul hs2.le]
        congr 1
        field_simp
      rw [hsq] at h1'
      have hHn := hH n
      have hTn := hT0 n
      have hbound : sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M ≤
          |Ch| * Real.sqrt (sPow β 2) * H n := by
        calc _ ≤ Ch * (Real.sqrt (sPow β 2) * H n) := h1'
          _ ≤ |Ch| * (Real.sqrt (sPow β 2) * H n) :=
              mul_le_mul_of_nonneg_right (le_abs_self Ch) (by positivity)
          _ = _ := by ring
      have hKH : K * H n ≤ ε * T n := by
        calc K * H n ≤ K * (ε / K * T n) := mul_le_mul_of_nonneg_left h2 hKpos.le
          _ = ε * T n := by field_simp
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2)), hHn, hT0 n,
          mul_nonneg (mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2))) hHn.le]
      · nlinarith
    · intro M hM ε hε
      obtain ⟨η0, hη0, hη01, hη⟩ := pg6_psi_approx hα hx0 hx0' (ε * κ) (by positivity)
      filter_upwards [hxl, hTκ, hreg.hγ.eventually_ge_atTop (M / η0),
        hreg.hγ.eventually_gt_atTop 0] with n hn h2 h3 h4
      have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
      have hpos' : 0 < M / gammaOf (N n) (B n) := by positivity
      have hle' : M / gammaOf (N n) (B n) ≤ η0 := by
        have h3' : M / η0 ≤ gammaOf (N n) (B n) := h3
        rw [div_le_iff₀ hγ]
        rw [div_le_iff₀ hη0] at h3'
        linarith
      have h5 := hη _ hpos' hle' _ hn (hxu n)
      have han' := han n
      have hHn := hH n
      have hTn := hT0 n
      have e : aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
          T n = aN α (c n) (N n) * (psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
            profPsi α (rowNum (i n) / (N n : ℝ))) := by simp only [hTdef]; ring
      rw [e, abs_mul, abs_of_pos han']
      calc aN α (c n) (N n) * |_| ≤ aN α (c n) (N n) * (ε * κ) :=
            mul_le_mul_of_nonneg_left h5 han'.le
        _ = ε * (κ * aN α (c n) (N n)) := by ring
        _ ≤ ε * T n := mul_le_mul_of_nonneg_left h2 hε.le
        _ ≤ ε * (H n + T n) := by nlinarith
  have h2 : IsEquivalent atTop (fun n => H n + T n) T := by
    rw [IsEquivalent, isLittleO_iff]
    intro δ hδ
    filter_upwards [hHT δ hδ, hT] with n h1 h2
    simp only [Pi.sub_apply, add_sub_cancel_right, Real.norm_eq_abs]
    rw [abs_of_pos (hH n), abs_of_pos h2]
    exact h1
  refine ⟨hcomb.trans h2, hcomb.congr_right (Eventually.of_forall (fun n => ?_))⟩
  simp only [hHdef, hTdef]
  rw [← pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)]
  ring


private lemma pg6_dAl_pos {α : ℝ} (hα : 1 < α) : 0 < dAl α := by
  have h0 : 0 < α := by linarith
  have hc : 0 < Real.cos (Real.pi / (2 * α)) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have : 0 < Real.pi / (2 * α) := by positivity
      linarith [Real.pi_pos]
    · rw [div_lt_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  unfold dAl c0
  positivity

/-- The algebra behind `b_N d_α y^{p_α} = d_α √(c K_α) N^{-1/2} i^{-(α-1)/2}`. -/
private lemma pg6_R_alg {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (i : Fin N) :
    bN α c N B * (dAl α * ((icCross α B / rowNum i) ^ α) ^ ((α - 1) / (2 * α))) =
      dAl α * Real.sqrt (c * Kc α) * (N : ℝ) ^ (-(1 : ℝ) / 2) * rowNum i ^ (-(α - 1) / 2) := by
  obtain ⟨hb0, hb2⟩ := pg6_bN_sq hα hc hN hB
  have hic := pg6_icCross_pos hα hB
  have hr := pg6_rowNum_pos i
  have hd := pg6_dAl_pos hα
  have hK := pg6_Kc_pos hα
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h0 : 0 < α := by linarith
  have hy : 0 < (icCross α B / rowNum i) ^ α := Real.rpow_pos_of_pos (div_pos hic hr) _
  have hL : 0 ≤ bN α c N B * (dAl α * ((icCross α B / rowNum i) ^ α) ^ ((α - 1) / (2 * α))) :=
    mul_nonneg hb0 (mul_nonneg hd.le (Real.rpow_nonneg hy.le _))
  have hR : 0 ≤ dAl α * Real.sqrt (c * Kc α) * (N : ℝ) ^ (-(1 : ℝ) / 2) * rowNum i ^ (-(α - 1) / 2) :=
    mul_nonneg (mul_nonneg (mul_nonneg hd.le (Real.sqrt_nonneg _)) (Real.rpow_nonneg hNr.le _))
      (Real.rpow_nonneg hr.le _)
  rw [← sq_eq_sq₀ hL hR]
  have e1 : (((icCross α B / rowNum i) ^ α) ^ ((α - 1) / (2 * α))) ^ 2 =
      (icCross α B / rowNum i) ^ (α - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le, ← Real.rpow_mul (div_pos hic hr).le]
    congr 1
    push_cast
    field_simp
  have e2 : ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le, ← Real.rpow_neg_one]
    congr 1; push_cast; ring
  have e3 : (rowNum i ^ (-(α - 1) / 2)) ^ 2 = (rowNum i ^ (α - 1))⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr.le, ← Real.rpow_neg hr.le]
    congr 1; push_cast; ring
  have e4 : Real.sqrt (c * Kc α) ^ 2 = c * Kc α := Real.sq_sqrt (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow, hb2, e1, e2, e3, e4, Real.div_rpow hic.le hr.le]
  have e5 : icCross α B ^ (α - 1) = icCross α B ^ α / icCross α B := by
    rw [Real.rpow_sub hic, Real.rpow_one]
  have hicB : icCross α B = (B : ℝ) / Kc α := rfl
  have : 0 < icCross α B ^ α := Real.rpow_pos_of_pos hic _
  have : 0 < rowNum i ^ (α - 1) := Real.rpow_pos_of_pos hr _
  rw [e5]
  rw [hicB]
  field_simp


/-! ### P-G.6.P4: the joint statement `lem_app_pl_super_iv` -/

private lemma pg6_psiR_alg {α c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 0 < N) (i : Fin N) :
    aN α c N * (dAl α * Real.sqrt (Kc α) * (rowNum i / (N : ℝ)) ^ (-(α - 1) / 2)) =
      dAl α * Real.sqrt (c * Kc α) * (N : ℝ) ^ (-(1 : ℝ) / 2) * rowNum i ^ (-(α - 1) / 2) := by
  have hr := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have h1 : (N : ℝ) ^ (-(1 : ℝ) / 2) = (N : ℝ) ^ (-α / 2) / (N : ℝ) ^ (-(α - 1) / 2) := by
    rw [← Real.rpow_sub hNr]; congr 1; ring
  have h2 : 0 < (N : ℝ) ^ (-(α - 1) / 2) := Real.rpow_pos_of_pos hNr _
  unfold aN
  rw [Real.sqrt_mul hc.le, Real.div_rpow hr.le hNr.le, h1]
  field_simp

private lemma pg6_psi_small {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n))
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    IsEquivalent atTop
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
        (fun n => dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
          rowNum (i n) ^ (-(α - 1) / 2)) := by
  have hx' : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall (fun n =>
      div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n))⟩
  have h1 := (lem_app_pl_Psi_ii_gt hα).comp_tendsto hx'
  have h2 : IsEquivalent atTop (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
      (fun n => aN α (c n) (N n) * (dAl α * Real.sqrt (Kc α) *
        (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2))) :=
    (IsEquivalent.refl (u := fun n => aN α (c n) (N n))).mul h1
  refine h2.congr_right (Eventually.of_forall (fun n => ?_))
  exact pg6_psiR_alg (hreg.hcpos n) (hreg.hNpos n) (i n)


private lemma pg6_bN_pos {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) :
    0 < bN α c N B := by
  obtain ⟨h0, h2⟩ := pg6_bN_sq hα hc hN hB
  have hic := pg6_icCross_pos hα hB
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast hB
  have hp : 0 < c / ((N : ℝ) / (B : ℝ) * icCross α B ^ α) := by positivity
  rcases h0.eq_or_lt with h | h
  · rw [← h] at h2; norm_num at h2; linarith
  · exact h

private lemma pg6p6_mN_at_inv {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) =
      gammaOf N B * finS α N ((rowNum i / (N : ℝ)) ^ α) := by
  have hpos := pg6_plSpec_pos (α := α) hc i
  have hr := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [eqn_app_pl_SN_mN α c hN hB hc (one_div_pos.2 hpos)]
  congr 2
  rw [pg6_plSpec_eq, Real.div_rpow hr.le hNr.le, Real.rpow_neg hr.le, Real.rpow_neg hNr.le]
  have : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hr _
  have : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
  field_simp

private lemma pg6p6_hrow {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n))
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0)) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hS := lem_app_pl_continuum_i_gt hα
  have hS1 := (isEquivalent_iff_tendsto_one (by
    filter_upwards [self_mem_nhdsWithin] with V hV
    have : 0 < V := hV
    have := Real.rpow_pos_of_pos this (1 / α)
    positivity)).1 hS
  have hev : ∀ᶠ V : ℝ in 𝓝[>] 0, contS α V ≤ 2 * (Kc α * V ^ (1 / α)) := by
    filter_upwards [hS1.eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num)),
      self_mem_nhdsWithin] with V h1 hV
    have hp : 0 < Kc α * V ^ (1 / α) := by
      have : 0 < V := hV
      have := Real.rpow_pos_of_pos this (1 / α)
      positivity
    simp only [Pi.div_apply] at h1
    rw [div_lt_iff₀ hp] at h1
    linarith
  obtain ⟨V0, hV0, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hx' : Tendsto (fun n => (rowNum (i n) / (N n : ℝ)) ^ α) atTop (𝓝 0) := by
    have := (Real.continuousAt_rpow_const 0 α (Or.inr hα0.le)).tendsto.comp hx
    rw [Real.zero_rpow hα0.ne'] at this
    exact this
  have h2 : Tendsto (fun n => 2 * (rowNum (i n) / icCross α (B n))) atTop (𝓝 0) := by
    simpa using h.const_mul 2
  refine squeeze_zero' (Eventually.of_forall (fun n => ?_)) ?_ h2
  · rw [pg6p6_mN_at_inv hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)]
    have := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    have : 0 ≤ finS α (N n) ((rowNum (i n) / (N n : ℝ)) ^ α) := by
      have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
      have hx0 : 0 < rowNum (i n) / (N n : ℝ) := div_pos (pg6_rowNum_pos _) hNr
      unfold finS
      refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => ?_))
      have h1 := Real.rpow_pos_of_pos hx0 α
      have h2 : 0 ≤ ((j : ℝ) / (N n : ℝ)) ^ α := Real.rpow_nonneg (by positivity) _
      positivity
    positivity
  · filter_upwards [hx'.eventually (gt_mem_nhds hV0)] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    have hx0 : 0 < rowNum (i n) / (N n : ℝ) := div_pos (pg6_rowNum_pos _) hNr
    have hVpos := Real.rpow_pos_of_pos hx0 α
    rw [pg6p6_mN_at_inv hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)]
    have hsm : contS α ((rowNum (i n) / (N n : ℝ)) ^ α) ≤
        2 * (Kc α * ((rowNum (i n) / (N n : ℝ)) ^ α) ^ (1 / α)) := hsub ⟨hVpos, hn⟩
    have hfin := (lem_app_pl_finite_inverse_i_a hα0 (hreg.hNpos n) _ hVpos).1
    have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    have hroot : ((rowNum (i n) / (N n : ℝ)) ^ α) ^ (1 / α) = rowNum (i n) / (N n : ℝ) := by
      rw [← Real.rpow_mul hx0.le, mul_one_div_cancel hα0.ne', Real.rpow_one]
    rw [hroot] at hsm
    calc gammaOf (N n) (B n) * finS α (N n) ((rowNum (i n) / (N n : ℝ)) ^ α)
        ≤ gammaOf (N n) (B n) * (2 * (Kc α * (rowNum (i n) / (N n : ℝ)))) := by
          apply mul_le_mul_of_nonneg_left _ hγ.le
          have : finS α (N n) ((rowNum (i n) / (N n : ℝ)) ^ α) ≤ contS α ((rowNum (i n) / (N n : ℝ)) ^ α) := by
            linarith
          exact this.trans hsm
      _ = 2 * (rowNum (i n) / icCross α (B n)) := by
          unfold gammaOf icCross
          have := hK.ne'
          field_simp

private lemma pg6p6_end_real {α s2 : ℝ} (hα : 1 < α) (hs2 : 0 < s2) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, Y ≤ y → dAl α * y ^ ((α - 1) / (2 * α)) ≤ ε * Real.sqrt (y / s2) := by
  have hα0 : 0 < α := by linarith
  have hp : (α - 1) / (2 * α) - 1 / 2 < 0 := by
    have : (α - 1) / (2 * α) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hd := pg6_dAl_pos hα
  have hT := (tendsto_rpow_neg_atTop (y := -((α - 1) / (2 * α) - 1 / 2)) (by linarith)).const_mul
    (dAl α * Real.sqrt s2)
  rw [mul_zero] at hT
  obtain ⟨Y, hY⟩ := (Filter.eventually_atTop.1 (hT.eventually (gt_mem_nhds (show (0:ℝ) < ε by exact hε))))
  refine ⟨max Y 1, by positivity, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := le_trans (le_max_right _ _) hy
  have hy0 : 0 < y := by linarith
  have h1 := hY y (le_trans (le_max_left _ _) hy)
  rw [neg_neg] at h1
  have e : Real.sqrt (y / s2) = y ^ (1 / 2 : ℝ) / Real.sqrt s2 := by
    rw [Real.sqrt_div hy0.le, Real.sqrt_eq_rpow]
  rw [e]
  have hss : 0 < Real.sqrt s2 := Real.sqrt_pos.2 hs2
  have hy12 : 0 < y ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hy0 _
  have e2 : y ^ ((α - 1) / (2 * α)) = y ^ ((α - 1) / (2 * α) - 1 / 2) * y ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hy0]; congr 1; ring
  rw [e2]
  have h2 : dAl α * Real.sqrt s2 * y ^ ((α - 1) / (2 * α) - 1 / 2) ≤ ε := h1.le
  calc dAl α * (y ^ ((α - 1) / (2 * α) - 1 / 2) * y ^ (1 / 2 : ℝ))
      = (dAl α * Real.sqrt s2 * y ^ ((α - 1) / (2 * α) - 1 / 2)) * y ^ (1 / 2 : ℝ) / Real.sqrt s2 := by
        field_simp
    _ ≤ ε * y ^ (1 / 2 : ℝ) / Real.sqrt s2 := by
        gcongr
    _ = ε * (y ^ (1 / 2 : ℝ) / Real.sqrt s2) := by ring

private lemma pg6p6_E1 {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0)) :
    IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) := by
  have hα0 : 0 < α := by linarith
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  set H : ℕ → ℝ := fun n => Real.sqrt (plSpec α (c n) (N n) (i n) /
    (gammaOf (N n) (B n) * sPow β 2)) with hHdef
  have hH : ∀ n, 0 < H n := fun n => by
    simp only [hHdef]
    apply Real.sqrt_pos.2
    have := pg6_plSpec_pos (α := α) (hreg.hcpos n) (i n)
    have := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    positivity
  have hrow := pg6p6_hrow hreg hα i hx h
  have hpos : ∀ n, 0 < rowNum (i n) / icCross α (B n) := fun n =>
    div_pos (pg6_rowNum_pos _) (pg6_icCross_pos hα (hreg.hBpos n))
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop atTop := by
    have h1 : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall hpos⟩
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    have h3 := (tendsto_rpow_atTop (by linarith : 0 < α)).comp h2
    refine h3.congr (fun n => ?_)
    simp [Function.comp, inv_div]
  have hcomb := pg6_combine hreg i H (fun _ => 0) hH (fun _ => le_rfl) ?_ ?_
  · simpa using hcomb
  · intro M hM ε hε
    have := (lem_app_pl_head_ii hreg M hM i hrow).isLittleO.def hε
    filter_upwards [this] with n hn
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hn
    have e' : |Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))| = H n :=
      abs_of_pos (hH n)
    rw [e'] at hn
    simpa using hn
  · intro M hM ε hε
    have hxpos : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Ioc (0 : ℝ) 1 := fun n => by
      have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
      exact ⟨div_pos (pg6_rowNum_pos _) this, (div_le_one this).2 (pg6_rowNum_le _)⟩
    have hPsi := (pg6_psi_small hreg hα i hx).isBigO
    obtain ⟨Cp, hCp⟩ := hPsi.bound
    obtain ⟨Y, hY0, hY⟩ := pg6p6_end_real (α := α) (s2 := sPow β 2) hα hs2
      (show 0 < ε / (|Cp| + 1) by positivity)
    filter_upwards [hy.eventually_ge_atTop Y, hCp, hreg.hγ.eventually_ge_atTop M] with n hn1 hn2 hn3
    have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    have hη0 : 0 < M / gammaOf (N n) (B n) := by positivity
    have hη1 : M / gammaOf (N n) (B n) ≤ 1 := by rw [div_le_one hγ]; exact hn3
    have han := pg6_aN_pos (α := α) (hreg.hcpos n) (hreg.hNpos n)
    obtain ⟨hr0, hr1⟩ := pg6p3_res_bounds hα0 (hxpos n) hη0.le hη1
    have hbN := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
    have hRn := pg6_R_alg hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)
    have hHn := pg6_bN_main hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) (sPow β 2) hs2
    simp only [Real.norm_eq_abs] at hn2
    have hRpos : 0 ≤ dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
        rowNum (i n) ^ (-(α - 1) / 2) := by
      rw [← hRn]
      have := pg6_dAl_pos hα
      have := Real.rpow_nonneg (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos (i n))).le α
      positivity
    simp only [sub_zero, add_zero]
    rw [abs_of_nonneg (mul_nonneg han.le hr0)]
    have h1 : aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) ≤
        aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)) :=
      mul_le_mul_of_nonneg_left hr1 han.le
    have hΨnn : 0 ≤ aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)) :=
      le_trans (mul_nonneg han.le hr0) h1
    rw [abs_of_nonneg hΨnn, abs_of_nonneg hRpos] at hn2
    set R := dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
        rowNum (i n) ^ (-(α - 1) / 2) with hR
    have hy' := hY _ hn1
    have hHn' : H n = bN α (c n) (N n) (B n) * Real.sqrt ((icCross α (B n) / rowNum (i n)) ^ α / sPow β 2) := hHn.symm
    have hR' : R = bN α (c n) (N n) (B n) * (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α))) := hRn.symm
    have hRle : R ≤ ε / (|Cp| + 1) * H n := by
      rw [hR', hHn']
      calc bN α (c n) (N n) (B n) * (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α)))
          ≤ bN α (c n) (N n) (B n) * (ε / (|Cp| + 1) * Real.sqrt ((icCross α (B n) / rowNum (i n)) ^ α / sPow β 2)) :=
            mul_le_mul_of_nonneg_left hy' hbN.le
        _ = _ := by ring
    have hCp0 : Cp ≤ |Cp| := le_abs_self Cp
    have hHn0 := hH n
    calc aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ))
        ≤ aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)) := h1
      _ ≤ Cp * R := hn2
      _ ≤ |Cp| * R := mul_le_mul_of_nonneg_right hCp0 hRpos
      _ ≤ |Cp| * (ε / (|Cp| + 1) * H n) := mul_le_mul_of_nonneg_left hRle (abs_nonneg _)
      _ ≤ ε * H n := by
          have habs := abs_nonneg Cp
          have : |Cp| * (ε / (|Cp| + 1)) ≤ ε := by
            rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_right this hHn0.le]

private lemma pg6p6_uf_bound {α x p : ℝ} (hα : 0 < α) (hx : 0 < x) (hp : p ∈ Ioo (0:ℝ) 1) :
    Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤ Real.sqrt (contV α p / p) / x ^ α := by
  have hV := (pg6p3_prof_contV_spec hα hp).1
  have hp0 : 0 < p := hp.1
  have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  set V := contV α p with hVdef
  have h1 : Real.sqrt ((1 - p) / (p * V)) ≤ Real.sqrt (1 / (p * V)) := by
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right (by linarith) (by positivity)
  have h2 : profF α x p ≤ V / x ^ α := by
    unfold profF
    rw [← hVdef]
    apply div_le_div_of_nonneg_left hV.le hD (by linarith)
  have h3 : Real.sqrt (1 / (p * V)) * V = Real.sqrt (V / p) := by
    rw [show V / p = (1 / (p * V)) * V ^ 2 by field_simp, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hV.le]
  have hs0 : 0 ≤ Real.sqrt ((1 - p) / (p * V)) := Real.sqrt_nonneg _
  have hf0 : 0 ≤ profF α x p := by unfold profF; positivity
  calc Real.sqrt ((1 - p) / (p * V)) * profF α x p
      ≤ Real.sqrt (1 / (p * V)) * (V / x ^ α) :=
        mul_le_mul h1 h2 hf0 (Real.sqrt_nonneg _)
    _ = Real.sqrt (V / p) / x ^ α := by rw [← h3]; ring

private lemma pg6p6_cut_A {α : ℝ} (hα : 1 < α) :
    ∃ p0 C : ℝ, 0 < p0 ∧ p0 ≤ 1 / 2 ∧ 0 < C ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ p0 →
      profPsi α x - psiRes α η x ≤ C * η ^ ((α + 1) / 2) / x ^ α := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hV := lem_app_pl_continuum_iii_gt hα
  have hV1 := (isEquivalent_iff_tendsto_one (by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have : 0 < p := hp
    have := Real.rpow_pos_of_pos (div_pos this hK) α
    exact this.ne')).1 hV
  have hev : ∀ᶠ p : ℝ in 𝓝[>] 0, contV α p ≤ 2 * (p / Kc α) ^ α := by
    filter_upwards [hV1.eventually (gt_mem_nhds (show (1:ℝ) < 2 by norm_num)),
      self_mem_nhdsWithin] with p h1 hp
    have hp' : 0 < p := hp
    have hq := Real.rpow_pos_of_pos (div_pos hp' hK) α
    simp only [Pi.div_apply] at h1
    rw [div_lt_iff₀ hq] at h1
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  set p0 : ℝ := min (u / 2) (1 / 2) with hp0
  have hp0pos : 0 < p0 := lt_min (by linarith [show (0:ℝ) < u from hu]) (by norm_num)
  have hp0u : p0 < u := lt_of_le_of_lt (min_le_left _ _) (by linarith [show (0:ℝ) < u from hu])
  have hp0h : p0 ≤ 1 / 2 := min_le_right _ _
  set Cs : ℝ := Real.sqrt (2 * (Kc α) ^ (-α)) with hCs
  have hCs0 : 0 < Cs := Real.sqrt_pos.2 (by positivity)
  refine ⟨p0, c0 * Cs / ((α + 1) / 2), hp0pos, hp0h, by
    have : 0 < c0 := by unfold c0; positivity
    positivity, ?_⟩
  intro x hxI η hη hηp0
  have hx : 0 < x := hxI.1
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx α
  have hη1 : η ≤ 1 := by linarith
  set g : ℝ → ℝ := fun p => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p with hg
  have hint : IntervalIntegrable g volume 0 1 := lem_app_pl_Psi_i_integrable hα0 x hxI
  have h0η : IntervalIntegrable g volume 0 η := hint.mono_set (by
    rw [uIcc_of_le hη.le, uIcc_of_le zero_le_one]; exact Icc_subset_Icc le_rfl hη1)
  have hη1i : IntervalIntegrable g volume η 1 := hint.mono_set (by
    rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hη.le le_rfl)
  have hdiff : profPsi α x - psiRes α η x = c0 * ∫ p in (0:ℝ)..η, g p := by
    unfold psiRes profPsi
    rw [← intervalIntegral.integral_add_adjacent_intervals h0η hη1i]
    ring
  rw [hdiff]
  have hmaj : IntervalIntegrable (fun p : ℝ => Cs * p ^ ((α - 1) / 2) / x ^ α) volume 0 η := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := η)
      (show (-1 : ℝ) < (α - 1) / 2 by linarith))
    exact (this.const_mul Cs).div_const _
  have hle : ∫ p in (0:ℝ)..η, g p ≤ ∫ p in (0:ℝ)..η, Cs * p ^ ((α - 1) / 2) / x ^ α := by
    refine intervalIntegral.integral_mono_on_of_le_Ioo hη.le h0η hmaj (fun p hp => ?_)
    have hp1 : p ∈ Ioo (0:ℝ) 1 := ⟨hp.1, by linarith [hp.2]⟩
    refine (pg6p6_uf_bound hα0 hx hp1).trans ?_
    apply div_le_div_of_nonneg_right _ hD.le
    have hV := (pg6p3_prof_contV_spec hα0 hp1).1
    have hpu : contV α p ≤ 2 * (p / Kc α) ^ α := hsub ⟨hp.1, by linarith [hp.2, hηp0, hp0u]⟩
    have hp0' : 0 < p := hp.1
    have h1 : contV α p / p ≤ 2 * Kc α ^ (-α) * p ^ (α - 1) := by
      rw [div_le_iff₀ hp0']
      calc contV α p ≤ 2 * (p / Kc α) ^ α := hpu
        _ = 2 * Kc α ^ (-α) * p ^ (α - 1) * p := by
          rw [Real.div_rpow hp0'.le hK.le, Real.rpow_neg hK.le, Real.rpow_sub_one hp0'.ne']
          have : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
          field_simp
    calc Real.sqrt (contV α p / p) ≤ Real.sqrt (2 * Kc α ^ (-α) * p ^ (α - 1)) := Real.sqrt_le_sqrt h1
      _ = Cs * p ^ ((α - 1) / 2) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_eq_rpow (p ^ (α - 1)), ← Real.rpow_mul hp0'.le]
          congr 3; ring
  have hval : ∫ p in (0:ℝ)..η, Cs * p ^ ((α - 1) / 2) / x ^ α = Cs / x ^ α * (η ^ ((α + 1) / 2) / ((α + 1) / 2)) := by
    have e : ∀ p : ℝ, Cs * p ^ ((α - 1) / 2) / x ^ α = (Cs / x ^ α) * p ^ ((α - 1) / 2) := fun p => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : (-1 : ℝ) < (α - 1) / 2))]
    rw [Real.zero_rpow (by linarith : (α - 1) / 2 + 1 ≠ 0)]
    congr 2
    · congr 1; ring
    · ring
  rw [hval] at hle
  calc c0 * ∫ p in (0:ℝ)..η, g p ≤ c0 * (Cs / x ^ α * (η ^ ((α + 1) / 2) / ((α + 1) / 2))) :=
        mul_le_mul_of_nonneg_left hle hc0.le
    _ = c0 * Cs / ((α + 1) / 2) * η ^ ((α + 1) / 2) / x ^ α := by ring

private lemma pg6p6_cut_B {α : ℝ} (hα : 1 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ x0 : ℝ, 0 < δ ∧ 0 < x0 ∧ x0 ≤ 1 ∧ ∀ x : ℝ, x ∈ Ioc (0:ℝ) x0 → ∀ η : ℝ, 0 < η → η ≤ δ * x →
      profPsi α x - psiRes α η x ≤ ε * profPsi α x := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hd := pg6_dAl_pos hα
  obtain ⟨p0, C, hp0, hp0h, hC, hA⟩ := pg6p6_cut_A hα
  have hPs := lem_app_pl_Psi_ii_gt hα
  have hne : ∀ᶠ x : ℝ in 𝓝[>] 0, dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have h1 : 0 < x := hx
    have h2 := Real.rpow_pos_of_pos h1 (-(α - 1) / 2)
    have h3 := Real.sqrt_pos.2 hK
    exact (by positivity : 0 < dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2)).ne'
  have hPs1 := (isEquivalent_iff_tendsto_one hne).1 hPs
  set c1 : ℝ := dAl α * Real.sqrt (Kc α) / 2 with hc1
  have hc1pos : 0 < c1 := by
    have := Real.sqrt_pos.2 hK
    positivity
  have hev : ∀ᶠ x : ℝ in 𝓝[>] 0, c1 * x ^ (-(α - 1) / 2) ≤ profPsi α x := by
    filter_upwards [hPs1.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with x h1 hx
    have hx' : 0 < x := hx
    have hq := Real.rpow_pos_of_pos hx' (-(α - 1) / 2)
    have hp : 0 < dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2) := by
      have := Real.sqrt_pos.2 hK
      positivity
    simp only [Pi.div_apply] at h1
    rw [lt_div_iff₀ hp] at h1
    rw [hc1]; nlinarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu' : 0 < u := hu
  set q : ℝ := (α + 1) / 2 with hq
  have hq0 : 0 < q := by rw [hq]; linarith
  set δ : ℝ := min p0 ((ε * c1 / C) ^ (1 / q)) with hδ
  have hδpos : 0 < δ := lt_min hp0 (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨δ, min (u / 2) 1, hδpos, lt_min (by linarith) one_pos, min_le_right _ _, ?_⟩
  intro x hx η hη hηx
  have hx0 : 0 < x := hx.1
  have hx1 : x ≤ 1 := hx.2.trans (min_le_right _ _)
  have hxu : x < u := lt_of_le_of_lt (hx.2.trans (min_le_left _ _)) (by linarith)
  have hΨ : c1 * x ^ (-(α - 1) / 2) ≤ profPsi α x := hsub ⟨hx0, hxu⟩
  have hηp0 : η ≤ p0 := by
    calc η ≤ δ * x := hηx
      _ ≤ δ * 1 := mul_le_mul_of_nonneg_left hx1 hδpos.le
      _ ≤ p0 := by rw [mul_one]; exact min_le_left _ _
  refine (hA x ⟨hx0, hx1⟩ η hη hηp0).trans ?_
  have hD : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
  have h1 : η ^ q ≤ (δ * x) ^ q := Real.rpow_le_rpow hη.le hηx hq0.le
  have h2 : δ ^ q ≤ ε * c1 / C := by
    calc δ ^ q ≤ ((ε * c1 / C) ^ (1 / q)) ^ q :=
          Real.rpow_le_rpow hδpos.le (min_le_right _ _) hq0.le
      _ = ε * c1 / C := by
          rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hq0.ne', Real.rpow_one]
  have e1 : x ^ q / x ^ α = x ^ (-(α - 1) / 2) := by
    rw [← Real.rpow_sub hx0]; congr 1; rw [hq]; ring
  calc C * η ^ q / x ^ α ≤ C * (δ * x) ^ q / x ^ α := by
        apply div_le_div_of_nonneg_right _ hD.le
        exact mul_le_mul_of_nonneg_left h1 hC.le
    _ = C * δ ^ q * (x ^ q / x ^ α) := by
        rw [Real.mul_rpow hδpos.le hx0.le]; ring
    _ = (C * δ ^ q) * x ^ (-(α - 1) / 2) := by rw [e1]
    _ ≤ (ε * c1) * x ^ (-(α - 1) / 2) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_pos_of_pos hx0 _).le
        have : C * δ ^ q ≤ C * (ε * c1 / C) := mul_le_mul_of_nonneg_left h2 hC.le
        rwa [mul_div_cancel₀ _ hC.ne'] at this
    _ = ε * (c1 * x ^ (-(α - 1) / 2)) := by ring
    _ ≤ ε * profPsi α x := mul_le_mul_of_nonneg_left hΨ hε.le

private lemma pg6p6_small_real {α s2 : ℝ} (hα : 1 < α) (hs2 : 0 < s2) {ε : ℝ} (hε : 0 < ε) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ y : ℝ, 0 < y → y ≤ Y →
      Real.sqrt (y / s2) ≤ ε * (dAl α * y ^ ((α - 1) / (2 * α))) := by
  have hα0 : 0 < α := by linarith
  have hd := pg6_dAl_pos hα
  have hp : 0 < 1 / 2 - (α - 1) / (2 * α) := by
    have : (α - 1) / (2 * α) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith
    linarith
  have hT : Tendsto (fun y : ℝ => y ^ (1 / 2 - (α - 1) / (2 * α))) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuousAt_rpow_const (0:ℝ) _ (Or.inr hp.le)).tendsto
    rw [Real.zero_rpow hp.ne'] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hss : 0 < Real.sqrt s2 := Real.sqrt_pos.2 hs2
  have hev : ∀ᶠ y : ℝ in 𝓝[>] 0, y ^ (1 / 2 - (α - 1) / (2 * α)) < ε * dAl α * Real.sqrt s2 :=
    hT.eventually (gt_mem_nhds (by positivity))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨u / 2, by linarith [show (0:ℝ) < u from hu], fun y hy hyu => ?_⟩
  have hyy : y < u := lt_of_le_of_lt hyu (by linarith [show (0:ℝ) < u from hu])
  have h1 : y ^ (1 / 2 - (α - 1) / (2 * α)) < ε * dAl α * Real.sqrt s2 := hsub ⟨hy, hyy⟩
  have e : Real.sqrt (y / s2) = y ^ (1 / 2 - (α - 1) / (2 * α)) * y ^ ((α - 1) / (2 * α)) / Real.sqrt s2 := by
    rw [← Real.rpow_add hy, Real.sqrt_div hy.le, Real.sqrt_eq_rpow]
    congr 2; ring
  rw [e, div_le_iff₀ hss]
  have hp2 : 0 < y ^ ((α - 1) / (2 * α)) := Real.rpow_pos_of_pos hy _
  calc y ^ (1 / 2 - (α - 1) / (2 * α)) * y ^ ((α - 1) / (2 * α))
      ≤ (ε * dAl α * Real.sqrt s2) * y ^ ((α - 1) / (2 * α)) :=
        mul_le_mul_of_nonneg_right h1.le hp2.le
    _ = ε * (dAl α * y ^ ((α - 1) / (2 * α))) * Real.sqrt s2 := by ring

private lemma pg6p6_E2 {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) := by
  have hα0 : 0 < α := by linarith
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have hK := pg6_Kc_pos hα
  have hxpos : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Ioc (0 : ℝ) 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨div_pos (pg6_rowNum_pos _) this, (div_le_one this).2 (pg6_rowNum_le _)⟩
  set H : ℕ → ℝ := fun n => Real.sqrt (plSpec α (c n) (N n) (i n) /
    (gammaOf (N n) (B n) * sPow β 2)) with hHdef
  set T : ℕ → ℝ := fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)) with hTdef
  have han : ∀ n, 0 < aN α (c n) (N n) := fun n => pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n)
  have hH : ∀ n, 0 < H n := fun n => by
    simp only [hHdef]
    apply Real.sqrt_pos.2
    have := pg6_plSpec_pos (α := α) (hreg.hcpos n) (i n)
    have := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    positivity
  have hT0 : ∀ n, 0 < T n := fun n => by
    simp only [hTdef]
    exact mul_pos (han n) (lem_app_pl_Psi_i_pos hα0 _ (hxpos n))
  -- y_n → 0+
  have hpos : ∀ n, 0 < icCross α (B n) / rowNum (i n) := fun n =>
    div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝[>] 0) := by
    have h1 : Tendsto (fun n => icCross α (B n) / rowNum (i n)) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp h
      refine this.congr (fun n => ?_)
      simp [Function.comp, inv_div]
    have h2 : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr (by linarith))).tendsto.comp h1
      rw [Real.zero_rpow (by linarith)] at this
      exact this
    exact tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall (fun n =>
      Real.rpow_pos_of_pos (hpos n) _)⟩
  -- T ~ R
  have hTR := pg6_psi_small hreg hα i hx
  have hTR' := hTR.isLittleO.def (show (0:ℝ) < 1 / 2 by norm_num)
  -- H ≤ δ T
  have hHT : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, H n ≤ δ * T n := by
    intro δ hδ
    obtain ⟨Y, hY0, hY⟩ := pg6p6_small_real (α := α) (s2 := sPow β 2) hα hs2 (show 0 < δ / 2 by positivity)
    filter_upwards [hy.eventually (Ioo_mem_nhdsGT hY0), hTR'] with n hn1 hn2
    have hbN := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
    have hRn := pg6_R_alg hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)
    have hHn := pg6_bN_main hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) (sPow β 2) hs2
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hn2
    set R := dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
        rowNum (i n) ^ (-(α - 1) / 2) with hR
    have hRpos : 0 < R := by
      rw [← hRn]
      have := pg6_dAl_pos hα
      have := Real.rpow_pos_of_pos (hpos n) α
      have := Real.rpow_pos_of_pos this ((α - 1) / (2 * α))
      positivity
    have hTn : R / 2 ≤ T n := by
      have := (abs_le.1 hn2).1
      rw [abs_of_pos hRpos] at this
      simp only [hTdef] at this ⊢
      linarith
    have hyy := hY _ (Real.rpow_pos_of_pos (hpos n) α) hn1.2.le
    have hHle : H n ≤ δ / 2 * R := by
      have e1 : H n = bN α (c n) (N n) (B n) *
          Real.sqrt ((icCross α (B n) / rowNum (i n)) ^ α / sPow β 2) := hHn.symm
      rw [e1, ← hRn]
      calc bN α (c n) (N n) (B n) * Real.sqrt ((icCross α (B n) / rowNum (i n)) ^ α / sPow β 2)
          ≤ bN α (c n) (N n) (B n) * (δ / 2 * (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α)))) :=
            mul_le_mul_of_nonneg_left hyy hbN.le
        _ = _ := by ring
    calc H n ≤ δ / 2 * R := hHle
      _ = δ * (R / 2) := by ring
      _ ≤ δ * T n := mul_le_mul_of_nonneg_left hTn hδ.le
  have hcomb : IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => H n + T n) := by
    refine pg6_combine hreg i H T hH (fun n => (hT0 n).le) ?_ ?_
    · intro M hM ε hε
      obtain ⟨Ch, hCh⟩ := lem_app_pl_head_i (α := α) (β := β) M hM
      set K : ℝ := |Ch| * Real.sqrt (sPow β 2) + 1 with hK'
      have hKpos : 0 < K := by positivity
      filter_upwards [hCh N B c hreg, hHT (ε / K) (by positivity), hreg.hγ.eventually_ge_atTop M]
        with n h1 h2 h3
      have hpn := pg6_piece_nonneg (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n)
        (hreg.hNpos n) (pg6_plSpec_anti hα0 (hreg.hcpos n))
        (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n) (le_refl (0:ℝ)) h3
      have h1' := h1 (i n)
      have hsq : Real.sqrt (plSpec α (c n) (N n) (i n) / gammaOf (N n) (B n)) =
          Real.sqrt (sPow β 2) * H n := by
        simp only [hHdef]
        rw [← Real.sqrt_mul hs2.le]
        congr 1
        field_simp
      rw [hsq] at h1'
      have hHn := hH n
      have hTn := hT0 n
      have hbound : sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M ≤
          |Ch| * Real.sqrt (sPow β 2) * H n := by
        calc _ ≤ Ch * (Real.sqrt (sPow β 2) * H n) := h1'
          _ ≤ |Ch| * (Real.sqrt (sPow β 2) * H n) :=
              mul_le_mul_of_nonneg_right (le_abs_self Ch) (by positivity)
          _ = _ := by ring
      have hKH : K * H n ≤ ε * T n := by
        calc K * H n ≤ K * (ε / K * T n) := mul_le_mul_of_nonneg_left h2 hKpos.le
          _ = ε * T n := by field_simp
      rw [abs_le]
      constructor
      · nlinarith [mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2)), hHn, hTn,
          mul_nonneg (mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2))) hHn.le]
      · nlinarith
    · intro M hM ε hε
      obtain ⟨δ, x0, hδ, hx0, hx01, hcut⟩ := pg6p6_cut_B hα hε
      -- eventually x_n ≤ x0 and M/γ ≤ δ x_n
      have hx1 : ∀ᶠ n in atTop, rowNum (i n) / (N n : ℝ) ≤ x0 :=
        hx.eventually (ge_mem_nhds hx0)
      have hr2 : ∀ᶠ n in atTop, M * Kc α / δ ≤ rowNum (i n) / icCross α (B n) :=
        h.eventually_ge_atTop _
      filter_upwards [hx1, hr2, hreg.hγ.eventually_ge_atTop M] with n hn1 hn2 hn3
      have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
      have hη0 : 0 < M / gammaOf (N n) (B n) := by positivity
      have hη1 : M / gammaOf (N n) (B n) ≤ 1 := by rw [div_le_one hγ]; exact hn3
      have hηx : M / gammaOf (N n) (B n) ≤ δ * (rowNum (i n) / (N n : ℝ)) := by
        have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
        have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
        have hr := pg6_rowNum_pos (i n)
        have hic := pg6_icCross_pos hα (hreg.hBpos n)
        have e : M / gammaOf (N n) (B n) = M * (B n : ℝ) / N n := by
          unfold gammaOf; field_simp
        rw [e, div_le_iff₀ hNr]
        have : M * Kc α / δ ≤ rowNum (i n) / icCross α (B n) := hn2
        rw [div_le_div_iff₀ hδ hic] at this
        have e2 : icCross α (B n) = (B n : ℝ) / Kc α := rfl
        rw [e2] at this
        have : M * Kc α * ((B n : ℝ) / Kc α) ≤ rowNum (i n) * δ := this
        have e3 : M * Kc α * ((B n : ℝ) / Kc α) = M * B n := by field_simp
        rw [e3] at this
        calc M * (B n : ℝ) ≤ rowNum (i n) * δ := this
          _ = δ * (rowNum (i n) / (N n : ℝ)) * N n := by field_simp
      have h5 := hcut _ ⟨(hxpos n).1, hn1⟩ _ hη0 hηx
      obtain ⟨hr0, hr1⟩ := pg6p3_res_bounds hα0 (hxpos n) hη0.le hη1
      have han' := han n
      have hHn := hH n
      have hTn := hT0 n
      have e : aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
          T n = -(aN α (c n) (N n) * (profPsi α (rowNum (i n) / (N n : ℝ)) -
            psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))) := by
        simp only [hTdef]; ring
      rw [e, abs_neg, abs_of_nonneg (mul_nonneg han'.le (by linarith))]
      calc aN α (c n) (N n) * (profPsi α (rowNum (i n) / (N n : ℝ)) -
            psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
          ≤ aN α (c n) (N n) * (ε * profPsi α (rowNum (i n) / (N n : ℝ))) :=
            mul_le_mul_of_nonneg_left h5 han'.le
        _ = ε * T n := by simp only [hTdef]; ring
        _ ≤ ε * (H n + T n) := by nlinarith
  have h2 : IsEquivalent atTop (fun n => H n + T n) T := by
    rw [IsEquivalent, isLittleO_iff]
    intro δ hδ
    filter_upwards [hHT δ hδ, Eventually.of_forall hT0] with n h1 h2
    simp only [Pi.sub_apply, add_sub_cancel_right, Real.norm_eq_abs]
    rw [abs_of_pos (hH n), abs_of_pos h2]
    exact h1
  exact hcomb.trans h2

private lemma pg6p6_abs_combine {D : ℕ → ℝ} {Φ : ℝ} (a b : ℝ → ℕ → ℝ) (ΦM : ℝ → ℝ)
    (C1 M0 κ : ℝ) (hM0 : 0 < M0) (hκ : 0 < κ)
    (hsplit : ∀ M : ℝ, M0 ≤ M → ∀ᶠ n in atTop, D n = a M n + b M n)
    (ha : ∀ M : ℝ, M0 ≤ M → Tendsto (a M) atTop (𝓝 (ΦM M)))
    (hΦM : Tendsto ΦM atTop (𝓝 Φ))
    (hb : ∀ M : ℝ, M0 ≤ M → ∀ᶠ n in atTop, 0 ≤ b M n ∧ b M n ≤ C1 * M ^ (-κ)) :
    Tendsto D atTop (𝓝 Φ) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h1 : ∀ᶠ M : ℝ in atTop, dist (ΦM M) Φ < ε / 3 :=
    (Metric.tendsto_nhds.1 hΦM) (ε / 3) (by positivity)
  have h2 : ∀ᶠ M : ℝ in atTop, |C1| * M ^ (-κ) < ε / 3 := by
    have := (tendsto_rpow_neg_atTop hκ).const_mul |C1|
    rw [mul_zero] at this
    exact this.eventually (gt_mem_nhds (by positivity))
  obtain ⟨M, hM1, hM2, hM3⟩ := (h1.and (h2.and (eventually_ge_atTop M0))).exists
  filter_upwards [hsplit M hM3, (Metric.tendsto_nhds.1 (ha M hM3)) (ε / 3) (by positivity),
    hb M hM3] with n hn1 hn2 hn3
  rw [Real.dist_eq] at hM1 hn2 ⊢
  rw [hn1]
  have hMp : 0 ≤ M ^ (-κ) := by
    have : (0:ℝ) < M := lt_of_lt_of_le hM0 hM3
    exact (Real.rpow_pos_of_pos this _).le
  have hCb : C1 * M ^ (-κ) ≤ |C1| * M ^ (-κ) := mul_le_mul_of_nonneg_right (le_abs_self C1) hMp
  rw [abs_lt] at hM1 hn2 ⊢
  obtain ⟨hb0, hb1⟩ := hn3
  constructor <;> linarith [hM1.1, hM1.2, hn2.1, hn2.2]

private lemma pg6p6_contV_mono {α p q : ℝ} (hα : 0 < α) (hp : p ∈ Ioo (0:ℝ) 1) (hq : q ∈ Ioo (0:ℝ) 1)
    (hpq : p ≤ q) : contV α p ≤ contV α q := by
  obtain ⟨hVp, hSp⟩ := pg6p3_prof_contV_spec hα hp
  obtain ⟨hVq, hSq⟩ := pg6p3_prof_contV_spec hα hq
  by_contra hlt
  push_neg at hlt
  have := (def_app_pl_profiles_S_bij hα).1 hVq hVp hlt
  rw [hSp, hSq] at this
  linarith

private lemma pg6p6_u_bound {α : ℝ} (hα : 1 < α) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ p : ℝ, p ∈ Ioo (0:ℝ) 1 →
      Real.sqrt ((1 - p) / (p * contV α p)) ≤ Cu * p ^ (-((α + 1) / 2)) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hV := lem_app_pl_continuum_iii_gt hα
  have hV1 := (isEquivalent_iff_tendsto_one (by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have : 0 < p := hp
    have := Real.rpow_pos_of_pos (div_pos this hK) α
    exact this.ne')).1 hV
  have hev : ∀ᶠ p : ℝ in 𝓝[>] 0, (1 / 2) * (p / Kc α) ^ α ≤ contV α p := by
    filter_upwards [hV1.eventually (lt_mem_nhds (show (1 / 2 : ℝ) < 1 by norm_num)),
      self_mem_nhdsWithin] with p h1 hp
    have hp' : 0 < p := hp
    have hq := Real.rpow_pos_of_pos (div_pos hp' hK) α
    simp only [Pi.div_apply] at h1
    rw [lt_div_iff₀ hq] at h1
    linarith
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu' : 0 < u := hu
  set p1 : ℝ := min (u / 2) (1 / 2) with hp1
  have hp1pos : 0 < p1 := lt_min (by linarith) (by norm_num)
  have hp1u : p1 < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hp1h : p1 ≤ 1 / 2 := min_le_right _ _
  have hp1I : p1 ∈ Ioo (0:ℝ) 1 := ⟨hp1pos, by linarith⟩
  have hv1 : 0 < contV α p1 := (pg6p3_prof_contV_spec hα0 hp1I).1
  set C1 : ℝ := Real.sqrt (2 * Kc α ^ α) with hC1
  set C2 : ℝ := Real.sqrt (1 / (p1 * contV α p1)) with hC2
  refine ⟨max C1 C2, lt_max_of_lt_left (Real.sqrt_pos.2 (by positivity)), fun p hp => ?_⟩
  have hp0 : 0 < p := hp.1
  have hV0 := (pg6p3_prof_contV_spec hα0 hp).1
  have hs1 : Real.sqrt ((1 - p) / (p * contV α p)) ≤ Real.sqrt (1 / (p * contV α p)) := by
    apply Real.sqrt_le_sqrt
    exact div_le_div_of_nonneg_right (by linarith [hp.2]) (by positivity)
  have hpow : 0 < p ^ (-((α + 1) / 2)) := Real.rpow_pos_of_pos hp0 _
  refine hs1.trans ?_
  rcases le_or_gt p p1 with hle | hgt
  · have hlow : (1 / 2) * (p / Kc α) ^ α ≤ contV α p := hsub ⟨hp0, lt_of_le_of_lt hle hp1u⟩
    have h1 : 1 / (p * contV α p) ≤ 2 * Kc α ^ α * (p ^ (-((α + 1) / 2))) ^ 2 := by
      have hq : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
      have hpa : 0 < p ^ α := Real.rpow_pos_of_pos hp0 α
      have e : (p ^ (-((α + 1) / 2))) ^ 2 = (p ^ α * p)⁻¹ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le,
          show (-((α + 1) / 2)) * (((2:ℕ):ℝ)) = -(α + 1) by push_cast; ring, Real.rpow_neg hp0.le,
          Real.rpow_add_one hp0.ne']
      rw [e, Real.div_rpow hp0.le hK.le] at *
      have hlow2 : (1 / 2) * (p ^ α / Kc α ^ α) ≤ contV α p := hlow
      calc 1 / (p * contV α p) ≤ 1 / (p * ((1 / 2) * (p ^ α / Kc α ^ α))) := by
            apply one_div_le_one_div_of_le (by positivity)
            exact mul_le_mul_of_nonneg_left hlow2 hp0.le
        _ = 2 * Kc α ^ α * (p ^ α * p)⁻¹ := by field_simp
    calc Real.sqrt (1 / (p * contV α p)) ≤ Real.sqrt (2 * Kc α ^ α * (p ^ (-((α + 1) / 2))) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = C1 * p ^ (-((α + 1) / 2)) := by
          rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hpow.le]
      _ ≤ max C1 C2 * p ^ (-((α + 1) / 2)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  · have hmono := pg6p6_contV_mono hα0 hp1I hp hgt.le
    have h1 : 1 / (p * contV α p) ≤ 1 / (p1 * contV α p1) := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul hgt.le hmono hv1.le hp0.le
    have hge : 1 ≤ p ^ (-((α + 1) / 2)) := by
      apply Real.one_le_rpow_of_pos_of_le_one_of_nonpos hp0 hp.2.le
      linarith
    calc Real.sqrt (1 / (p * contV α p)) ≤ C2 := Real.sqrt_le_sqrt h1
      _ ≤ max C1 C2 := le_max_right _ _
      _ = max C1 C2 * 1 := (mul_one _).symm
      _ ≤ max C1 C2 * p ^ (-((α + 1) / 2)) :=
          mul_le_mul_of_nonneg_left hge (le_trans (Real.sqrt_nonneg _) (le_max_left _ _))

private lemma pg6p6_psi_upper {α : ℝ} (hα : 1 < α) :
    ∃ Cu : ℝ, 0 < Cu ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ x : ℝ, x ∈ Ioc (0:ℝ) 1 →
      psiRes α η x ≤ Cu * η ^ (-((α - 1) / 2)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨Cu0, hCu0, hu⟩ := pg6p6_u_bound hα
  have hc0 : 0 < c0 := by unfold c0; positivity
  have hκ : 0 < (α - 1) / 2 := by linarith
  refine ⟨c0 * Cu0 / ((α - 1) / 2), by positivity, fun η hη hη1 x hx => ?_⟩
  unfold psiRes
  have hint : IntervalIntegrable (fun p : ℝ => Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p)
      volume η 1 :=
    (lem_app_pl_Psi_i_integrable hα0 x hx).mono_set (by
      rw [uIcc_of_le hη1, uIcc_of_le zero_le_one]; exact Icc_subset_Icc hη.le le_rfl)
  have hmaj : IntervalIntegrable (fun p : ℝ => Cu0 * p ^ (-((α + 1) / 2))) volume η 1 := by
    have := intervalIntegral.intervalIntegrable_rpow (μ := volume) (r := -((α + 1) / 2)) (a := η) (b := 1)
      (Or.inr (by
        rw [uIcc_of_le hη1]; intro h0; exact absurd h0.1 (not_le.2 hη)))
    exact this.const_mul Cu0
  have hle : ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p ≤
      ∫ p in η..1, Cu0 * p ^ (-((α + 1) / 2)) := by
    refine intervalIntegral.integral_mono_on hη1 hint hmaj (fun p hp => ?_)
    have hp0 : 0 < p := lt_of_lt_of_le hη hp.1
    have hpow : 0 < p ^ (-((α + 1) / 2)) := Real.rpow_pos_of_pos hp0 _
    rcases eq_or_lt_of_le hp.2 with h1 | h1
    · rw [h1]
      simp only [sub_self, zero_div, Real.sqrt_zero, zero_mul, Real.one_rpow, mul_one]
      exact hCu0.le
    · have hp1 : p ∈ Ioo (0:ℝ) 1 := ⟨hp0, h1⟩
      have hV := (pg6p3_prof_contV_spec hα0 hp1).1
      have hf1 : profF α x p ≤ 1 := by
        unfold profF
        have := Real.rpow_pos_of_pos hx.1 α
        rw [div_le_one (by positivity)]; linarith
      have hf0 : 0 ≤ profF α x p := by
        unfold profF
        have := Real.rpow_pos_of_pos hx.1 α
        positivity
      calc Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
          ≤ Real.sqrt ((1 - p) / (p * contV α p)) * 1 :=
            mul_le_mul_of_nonneg_left hf1 (Real.sqrt_nonneg _)
        _ ≤ Cu0 * p ^ (-((α + 1) / 2)) := by rw [mul_one]; exact hu p hp1
  have hval : ∫ p in η..1, Cu0 * p ^ (-((α + 1) / 2)) =
      Cu0 * ((1 ^ (-((α + 1) / 2) + 1) - η ^ (-((α + 1) / 2) + 1)) / (-((α + 1) / 2) + 1)) := by
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inr ⟨by linarith, by
      rw [uIcc_of_le hη1]; intro h0; exact absurd h0.1 (not_le.2 hη)⟩)]
  rw [hval] at hle
  have e1 : -((α + 1) / 2) + 1 = -((α - 1) / 2) := by ring
  rw [e1, Real.one_rpow] at hle
  have hηp : 0 < η ^ (-((α - 1) / 2)) := Real.rpow_pos_of_pos hη _
  have e2 : (1 - η ^ (-((α - 1) / 2))) / (-((α - 1) / 2)) = (η ^ (-((α - 1) / 2)) - 1) / ((α - 1) / 2) := by
    field_simp; ring
  rw [e2] at hle
  calc c0 * ∫ p in η..1, Real.sqrt ((1 - p) / (p * contV α p)) * profF α x p
      ≤ c0 * (Cu0 * ((η ^ (-((α - 1) / 2)) - 1) / ((α - 1) / 2))) :=
        mul_le_mul_of_nonneg_left hle hc0.le
    _ ≤ c0 * (Cu0 * (η ^ (-((α - 1) / 2)) / ((α - 1) / 2))) := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        apply mul_le_mul_of_nonneg_left _ hCu0.le
        exact div_le_div_of_nonneg_right (by linarith) hκ.le
    _ = c0 * Cu0 / ((α - 1) / 2) * η ^ (-((α - 1) / 2)) := by ring

private lemma pg6p6_aN_gamma {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) :
    aN α c N * gammaOf N B ^ ((α - 1) / 2) = Kc α ^ (-α / 2) * bN α c N B := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ := pg6_gamma_pos hB hN
  obtain ⟨hb0, hb2⟩ := pg6_bN_sq hα hc hN hB
  have hL0 : 0 ≤ aN α c N * gammaOf N B ^ ((α - 1) / 2) :=
    mul_nonneg (pg6_aN_pos hc hN).le (Real.rpow_nonneg hγ.le _)
  have hR0 : 0 ≤ Kc α ^ (-α / 2) * bN α c N B :=
    mul_nonneg (Real.rpow_nonneg hK.le _) hb0
  rw [← sq_eq_sq₀ hL0 hR0, mul_pow, mul_pow, hb2]
  have e1 : aN α c N ^ 2 = c * (N : ℝ) ^ (-α) := by
    unfold aN
    rw [mul_pow, Real.sq_sqrt hc.le, ← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    congr 2; push_cast; ring
  have e2 : (gammaOf N B ^ ((α - 1) / 2)) ^ 2 = gammaOf N B ^ (α - 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hγ.le]; congr 1; push_cast; ring
  have e3 : (Kc α ^ (-α / 2)) ^ 2 = (Kc α ^ α)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hK.le, ← Real.rpow_neg_one, ← Real.rpow_mul hK.le]
    congr 1; push_cast; ring
  rw [e1, e2, e3]
  have hic : icCross α B ^ α = (B : ℝ) ^ α / Kc α ^ α := by
    unfold icCross; rw [Real.div_rpow hBr.le hK.le]
  rw [hic]
  have hNa : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr α
  have hBa : 0 < (B : ℝ) ^ α := Real.rpow_pos_of_pos hBr α
  have hKa : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
  have e4 : gammaOf N B ^ (α - 1) = (N : ℝ) ^ α / (N : ℝ) / ((B : ℝ) ^ α / (B : ℝ)) := by
    unfold gammaOf
    rw [Real.div_rpow hNr.le hBr.le, Real.rpow_sub_one hNr.ne', Real.rpow_sub_one hBr.ne']
  have e5 : (N : ℝ) ^ (-α) = ((N : ℝ) ^ α)⁻¹ := Real.rpow_neg hNr.le _
  rw [e4, e5]
  field_simp

private lemma pg6p6_tail_bound {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) :
    ∃ C1 M0 : ℝ, 0 < C1 ∧ 0 < M0 ∧ ∀ M : ℝ, M0 ≤ M → ∀ᶠ n in atTop,
      0 ≤ sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n)) /
          bN α (c n) (N n) (B n) ∧
      sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n)) /
          bN α (c n) (N n) (B n) ≤ C1 * M ^ (-((α - 1) / 2)) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  obtain ⟨C, M₀, hM₀, htail⟩ := lem_app_pl_tail (α := α) (β := β)
  obtain ⟨Cu, hCu, hpsi⟩ := pg6p6_psi_upper hα
  obtain ⟨cΨ, hcΨ, hlow⟩ := pg6p2_psi_lower hα0
  have hκ : 0 < (α - 1) / 2 := by linarith
  refine ⟨(2 + |C| / M₀) * Cu * Kc α ^ (-α / 2) + 1, M₀, by positivity, hM₀, fun M hM => ?_⟩
  have hM0 : 0 < M := lt_of_lt_of_le hM₀ hM
  filter_upwards [htail N B c hreg M hM 1 one_pos, hreg.hγ.eventually_ge_atTop (4 * M)] with n h1 h2
  have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
  have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
  have hx01 : rowNum (i n) / (N n : ℝ) ∈ Ioc (0:ℝ) 1 :=
    ⟨div_pos (pg6_rowNum_pos _) hNr, (div_le_one hNr).2 (pg6_rowNum_le _)⟩
  have hη0 : 0 < M / gammaOf (N n) (B n) := by positivity
  have hη4 : M / gammaOf (N n) (B n) ≤ 1 / 4 := by
    rw [div_le_iff₀ hγ]; have : 4 * M ≤ gammaOf (N n) (B n) := h2; linarith
  have han := pg6_aN_pos (α := α) (hreg.hcpos n) (hreg.hNpos n)
  have hbN := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
  have hψlow := hlow _ hx01 _ hη0 hη4
  have hψpos : 0 < psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) :=
    lt_of_lt_of_le hcΨ hψlow
  have hden : 0 < aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) :=
    mul_pos han hψpos
  have hT0 := pg6_piece_nonneg (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n)
    (hreg.hNpos n) (pg6_plSpec_anti hα0 (hreg.hcpos n))
    (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n) (hM0.le) le_rfl
  refine ⟨div_nonneg hT0 hbN.le, ?_⟩
  set T := sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n))
  set ψ := psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ))
  have hr := h1 (i n)
  have hr2 : T / (aN α (c n) (N n) * ψ) ≤ 1 + (|C| / M + 1) := by
    have := (abs_le.1 hr).2
    have h3 : C / M ≤ |C| / M := div_le_div_of_nonneg_right (le_abs_self C) hM0.le
    linarith
  have hTle : T ≤ (2 + |C| / M) * (aN α (c n) (N n) * ψ) := by
    rw [div_le_iff₀ hden] at hr2
    nlinarith
  have hψle := hpsi _ hη0 (by linarith) _ hx01
  have hag := pg6p6_aN_gamma hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
  have hηpow : (M / gammaOf (N n) (B n)) ^ (-((α - 1) / 2)) =
      gammaOf (N n) (B n) ^ ((α - 1) / 2) * M ^ (-((α - 1) / 2)) := by
    rw [Real.div_rpow hM0.le hγ.le, Real.rpow_neg hγ.le, div_inv_eq_mul, mul_comm]
  have hMp : 0 < M ^ (-((α - 1) / 2)) := Real.rpow_pos_of_pos hM0 _
  have hKp : 0 < Kc α ^ (-α / 2) := Real.rpow_pos_of_pos hK _
  have hcoef : 0 ≤ 2 + |C| / M := by positivity
  have hstep : T ≤ (2 + |C| / M) * (Cu * Kc α ^ (-α / 2) * M ^ (-((α - 1) / 2))) * bN α (c n) (N n) (B n) := by
    calc T ≤ (2 + |C| / M) * (aN α (c n) (N n) * ψ) := hTle
      _ ≤ (2 + |C| / M) * (aN α (c n) (N n) * (Cu * (M / gammaOf (N n) (B n)) ^ (-((α - 1) / 2)))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hψle han.le) hcoef
      _ = (2 + |C| / M) * (Cu * M ^ (-((α - 1) / 2)) * (aN α (c n) (N n) * gammaOf (N n) (B n) ^ ((α - 1) / 2))) := by
          rw [hηpow]; ring
      _ = _ := by rw [hag]; ring
  rw [div_le_iff₀ hbN]
  refine hstep.trans ?_
  have hCM : |C| / M ≤ |C| / M₀ := div_le_div_of_nonneg_left (abs_nonneg C) hM₀ hM
  have hfin : (2 + |C| / M) * (Cu * Kc α ^ (-α / 2) * M ^ (-((α - 1) / 2))) ≤
      ((2 + |C| / M₀) * Cu * Kc α ^ (-α / 2) + 1) * M ^ (-((α - 1) / 2)) := by
    have : (2 + |C| / M) * (Cu * Kc α ^ (-α / 2) * M ^ (-((α - 1) / 2))) ≤
        (2 + |C| / M₀) * (Cu * Kc α ^ (-α / 2) * M ^ (-((α - 1) / 2))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [this]
  exact mul_le_mul_of_nonneg_right hfin hbN.le

private lemma pg6p6_Z_eq {α c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (i : Fin N) {m lam : ℝ} (hm : 0 < m) (hmγ : m < gammaOf N B) (hlam : 0 < lam) :
    Real.sqrt ((gammaOf N B - m) / (m * lam)) * (lam * plSpec α c N i) / (gammaOf N B * bN α c N B) =
      Real.sqrt (1 - m / gammaOf N B) * Real.sqrt (c * lam / (m * icCross α B) ^ α) *
        (icCross α B / rowNum i) ^ α * m ^ ((α - 1) / 2) := by
  have hα0 : 0 < α := by linarith
  have hγ := pg6_gamma_pos hB hN
  have hic := pg6_icCross_pos hα hB
  have hr := pg6_rowNum_pos i
  have hbN := pg6_bN_pos hα hc hN hB
  obtain ⟨-, hb2⟩ := pg6_bN_sq hα hc hN hB
  have hμ := pg6_plSpec_pos (α := α) hc i
  have hs1 : 0 < gammaOf N B - m := by linarith
  have hL0 : 0 ≤ Real.sqrt ((gammaOf N B - m) / (m * lam)) * (lam * plSpec α c N i) / (gammaOf N B * bN α c N B) := by
    positivity
  have hR0 : 0 ≤ Real.sqrt (1 - m / gammaOf N B) * Real.sqrt (c * lam / (m * icCross α B) ^ α) *
        (icCross α B / rowNum i) ^ α * m ^ ((α - 1) / 2) := by positivity
  rw [← sq_eq_sq₀ hL0 hR0]
  have hbN2 : bN α c N B ^ 2 = c / (gammaOf N B * icCross α B ^ α) := by
    rw [hb2]; rfl
  have e1 : (Real.sqrt ((gammaOf N B - m) / (m * lam)) * (lam * plSpec α c N i) / (gammaOf N B * bN α c N B)) ^ 2
      = ((gammaOf N B - m) / (m * lam)) * (lam * plSpec α c N i) ^ 2 / (gammaOf N B ^ 2 * bN α c N B ^ 2) := by
    rw [div_pow]; simp only [mul_pow]; rw [Real.sq_sqrt (by positivity)]
  have e2 : (Real.sqrt (1 - m / gammaOf N B) * Real.sqrt (c * lam / (m * icCross α B) ^ α) *
        (icCross α B / rowNum i) ^ α * m ^ ((α - 1) / 2)) ^ 2 =
      (1 - m / gammaOf N B) * (c * lam / (m * icCross α B) ^ α) * ((icCross α B / rowNum i) ^ α) ^ 2 *
        (m ^ ((α - 1) / 2)) ^ 2 := by
    have h1 : 0 ≤ 1 - m / gammaOf N B := by
      rw [sub_nonneg, div_le_one hγ]; linarith
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt h1, Real.sq_sqrt (by positivity)]
  rw [e1, e2, hbN2]
  have e3 : (m ^ ((α - 1) / 2)) ^ 2 = m ^ α / m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm.le, ← Real.rpow_sub_one hm.ne']
    congr 1; push_cast; ring
  have e4 : ((icCross α B / rowNum i) ^ α) ^ 2 = (icCross α B ^ α / rowNum i ^ α) ^ 2 := by
    rw [Real.div_rpow hic.le hr.le]
  have e5 : (m * icCross α B) ^ α = m ^ α * icCross α B ^ α := Real.mul_rpow hm.le hic.le
  have e6 : plSpec α c N i = c * (rowNum i ^ α)⁻¹ := by
    rw [pg6_plSpec_eq, Real.rpow_neg hr.le]
  rw [e3, e4, e5, e6]
  have ha : 0 < icCross α B ^ α := Real.rpow_pos_of_pos hic α
  have hb : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hr α
  have hc' : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hγne := hγ.ne'
  have hmne := hm.ne'
  have hlne := hlam.ne'
  have hcne := hc.ne'
  field_simp

private lemma pg6p6_Fn_eq {α β c : ℝ} (hα : 1 < α) (hc : 0 < c) {N B : ℕ} (hN : 0 < N) (hB : 0 < B)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    1 / (Real.pi * gammaOf N B * bN α c N B) *
      (Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) =
    1 / Real.pi * Aav β m *
      ((Real.sqrt (1 - m / gammaOf N B) *
          Real.sqrt (c * partLam B (plSpec α c N) m / (m * icCross α B) ^ α) *
          (icCross α B / rowNum i) ^ α * m ^ ((α - 1) / 2)) /
        (1 + c * partLam B (plSpec α c N) m / (m * icCross α B) ^ α *
          (icCross α B / rowNum i) ^ α * m ^ α)) *
      (Efun β m * thetaN β B (plSpec α c N) m) := by
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => pg6_plSpec_pos hc j
  have hlam : 0 < partLam B (plSpec α c N) m := (pg6p2_Lam_hasDeriv _ hB hN hpos hm).1
  have hZ := pg6p6_Z_eq hα hc hN hB i hm.1 hm.2 hlam
  have hγ := pg6_gamma_pos hB hN
  have hbN := pg6_bN_pos hα hc hN hB
  have hic := pg6_icCross_pos hα hB
  have hr := pg6_rowNum_pos i
  set lam := partLam B (plSpec α c N) m with hlamdef
  have hmα : 0 < m ^ α := Real.rpow_pos_of_pos hm.1 α
  have ht : lam * plSpec α c N i = c * lam / (m * icCross α B) ^ α * (icCross α B / rowNum i) ^ α * m ^ α := by
    rw [pg6_plSpec_eq, Real.mul_rpow hm.1.le hic.le, Real.div_rpow hic.le hr.le, Real.rpow_neg hr.le]
    have ha : 0 < icCross α B ^ α := Real.rpow_pos_of_pos hic α
    have hb : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hr α
    field_simp
  unfold partBfun partF
  rw [← hlamdef]
  have hπ := Real.pi_pos
  have h1 : 0 < 1 + lam * plSpec α c N i := by
    have := pg6_plSpec_pos (α := α) hc i
    positivity
  rw [← ht]
  rw [← hZ]
  field_simp

private lemma pg6p6_Etheta {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      ∀ m : ℝ, 0 < m → m ≤ gammaOf N B / 2 →
        1 ≤ Efun β m * thetaN β B (plSpec α c N) m ∧
        Efun β m * thetaN β B (plSpec α c N) m ≤ Cθ := by
  have hα0 : 0 < α := by linarith
  obtain ⟨cE, CE, hcE, hcC, hE⟩ := lem_app_pl_weights_iii_E hβ0 hβ1
  obtain ⟨C, hC⟩ := lem_app_pl_elasticity_ii hα0 hβ0 hβ1
  have hCEp : 0 < CE := lt_of_lt_of_le hcE hcC
  refine ⟨3 * |C| * CE + 1, by positivity, fun N B c hN hB hc hγ2 m hm hmγ => ?_⟩
  have hγ := pg6_gamma_pos hB hN
  have hmI : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  obtain ⟨h1, h2⟩ := hC N B c hN hB hc m hmI
  refine ⟨h2, ?_⟩
  have hEpos := pg6p4_E_pos hβ0 hβ1 hm
  have hE1 := (hE m hm).2
  have hmin1 : min m 1 ≤ 1 := min_le_right _ _
  have hminm : min m 1 ≤ m := min_le_left _ _
  have hECE : Efun β m ≤ CE := hE1.trans (by nlinarith)
  have hEm : Efun β m / m ≤ CE := by
    rw [div_le_iff₀ hm]
    calc Efun β m ≤ CE * min m 1 := hE1
      _ ≤ CE * m := mul_le_mul_of_nonneg_left hminm (by linarith)
      _ = CE * m := rfl
  have hγm : 1 ≤ gammaOf N B - m := by linarith
  have hEg : Efun β m / (gammaOf N B - m) ≤ CE := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hθ := h1
  calc Efun β m * thetaN β B (plSpec α c N) m
      ≤ Efun β m * (C * (1 + 1 / m + 1 / (gammaOf N B - m))) :=
        mul_le_mul_of_nonneg_left hθ hEpos.le
    _ ≤ Efun β m * (|C| * (1 + 1 / m + 1 / (gammaOf N B - m))) := by
        apply mul_le_mul_of_nonneg_left _ hEpos.le
        apply mul_le_mul_of_nonneg_right (le_abs_self C)
        have : 0 ≤ 1 / m := by positivity
        have : 0 ≤ 1 / (gammaOf N B - m) := by positivity
        linarith
    _ = |C| * (Efun β m + Efun β m / m + Efun β m / (gammaOf N B - m)) := by
        field_simp
    _ ≤ |C| * (CE + CE + CE) := by
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg C)
        linarith
    _ ≤ 3 * |C| * CE + 1 := by nlinarith

private lemma pg6p6_mono4 {T A A' s S y mk e Ct : ℝ} (hT : 0 ≤ T) (hA : 0 ≤ A) (hAA : A ≤ A')
    (hs : 0 ≤ s) (hsS : s ≤ S) (hy : 0 ≤ y) (hmk : 0 ≤ mk) (he0 : 0 ≤ e) (he : e ≤ Ct) :
    T * A * (s * y * mk) * e ≤ T * A' * (S * y * mk) * Ct := by
  have h1 : T * A ≤ T * A' := mul_le_mul_of_nonneg_left hAA hT
  have h2 : s * y * mk ≤ S * y * mk :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsS hy) hmk
  have h3 : T * A * (s * y * mk) ≤ T * A' * (S * y * mk) :=
    mul_le_mul h1 h2 (by positivity) (by nlinarith [mul_nonneg hT (hA.trans hAA)])
  exact mul_le_mul h3 he he0 (by
    have : 0 ≤ T * A' := mul_nonneg hT (hA.trans hAA)
    have : 0 ≤ S * y * mk := mul_nonneg (mul_nonneg (hs.trans hsS) hy) hmk
    positivity)

private lemma pg6p6_lift_p {K0 K1 y p q : ℝ} (h : K0 ≤ K1) (hK0 : 0 ≤ K0) (hy : 0 ≤ y) (hp : 0 ≤ p)
    (hq : 0 ≤ q) : K0 * y * p ≤ K1 * y * (p + q) := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h) hy) hp, mul_nonneg (mul_nonneg (hK0.trans h) hy) hq]

private lemma pg6p6_lift_q {K0 K1 y p q : ℝ} (h : K0 ≤ K1) (hK0 : 0 ≤ K0) (hy : 0 ≤ y) (hp : 0 ≤ p)
    (hq : 0 ≤ q) : K0 * y * q ≤ K1 * y * (p + q) := by
  nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 h) hy) hq, mul_nonneg (mul_nonneg (hK0.trans h) hy) hp]

private lemma pg6p6_Fn_bound {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ K1 K2 : ℝ, 0 < K1 ∧ 0 < K2 ∧ ∀ (N B : ℕ) (c : ℝ), 0 < N → 0 < B → 0 < c → 2 ≤ gammaOf N B →
      ∀ i : Fin N, ∀ m : ℝ, 0 < m → m ≤ gammaOf N B / 2 →
        0 ≤ 1 / (Real.pi * gammaOf N B * bN α c N B) *
            (Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) ∧
        (1 / (B : ℝ) ≤ m →
          1 / (Real.pi * gammaOf N B * bN α c N B) *
            (Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) ≤
          K1 * (icCross α B / rowNum i) ^ α * (m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2))) ∧
        (m ≤ 1 / (B : ℝ) →
          1 / (Real.pi * gammaOf N B * bN α c N B) *
            (Aav β m * partBfun B (plSpec α c N) i m * Efun β m * thetaN β B (plSpec α c N) m) ≤
          K2 * (icCross α B / rowNum i) ^ α * Real.sqrt ((B : ℝ) / icCross α B ^ α) * m ^ (-(1 / 2 : ℝ))) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  obtain ⟨C₁, C₂, hC₁, hC₂, hv1⟩ := lem_app_pl_finite_inverse_v_i hα
  obtain ⟨D₁, D₂, hD₁, hD₂, hv2⟩ := lem_app_pl_finite_inverse_v_ii hα
  obtain ⟨BA, hBA, hAs⟩ := pg6p5_A_sqrt_small hβ0 hβ1
  obtain ⟨-, Ca, -, hCa, -, hAl⟩ := pg6p4_Aav_upper hβ0 hβ1
  obtain ⟨Cθ, hCθ, hEθ⟩ := pg6p6_Etheta hα hβ0 hβ1
  have hπ := Real.pi_pos
  refine ⟨1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1,
    1 / Real.pi * BA * Cθ * Real.sqrt D₂ + 1, by positivity, by positivity, ?_⟩
  intro N B c hN hB hc hγ2 i m hm hmγ
  have hγ := pg6_gamma_pos hB hN
  have hmI : m ∈ Ioo 0 (gammaOf N B) := ⟨hm, by linarith⟩
  have heq := pg6p6_Fn_eq (β := β) hα hc hN hB i hmI
  have hpos : ∀ j, 0 < plSpec α c N j := fun j => pg6_plSpec_pos hc j
  have hlam : 0 < partLam B (plSpec α c N) m := (pg6p2_Lam_hasDeriv _ hB hN hpos hmI).1
  have hic := pg6_icCross_pos hα hB
  have hr := pg6_rowNum_pos i
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  obtain ⟨hEθ1, hEθ2⟩ := hEθ N B c hN hB hc hγ2 m hm hmγ
  set lam := partLam B (plSpec α c N) m with hlamdef
  set u : ℝ := c * lam / (m * icCross α B) ^ α with hu
  set y : ℝ := (icCross α B / rowNum i) ^ α with hy
  have hmic : 0 < (m * icCross α B) ^ α := Real.rpow_pos_of_pos (mul_pos hm hic) α
  have hu0 : 0 < u := by positivity
  have hy0 : 0 < y := Real.rpow_pos_of_pos (div_pos hic hr) α
  have hmα : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hmκ : 0 < m ^ ((α - 1) / 2) := Real.rpow_pos_of_pos hm _
  have hA0 : 0 ≤ Aav β m := by
    have hQ := (pg6p4_Qm_spec hβ0 hβ1 hm).1
    have hL := pg6p4_Lw_pos hβ0 hβ1 hQ.le
    have hE := pg6p4_E_pos hβ0 hβ1 hm
    unfold Aav; positivity
  -- A bound for small m
  have hAsm : m ≤ 1 → Aav β m ≤ BA * m ^ (-(1 / 2 : ℝ)) := by
    intro h
    have := (hAs m hm h).2
    have hsq : 0 < m ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hm _
    rw [Real.rpow_neg hm.le, ← div_eq_mul_inv, le_div_iff₀ hsq]
    exact this
  have hsqrt_u : ∀ U : ℝ, u ≤ U → Real.sqrt u ≤ Real.sqrt U := fun U h => Real.sqrt_le_sqrt h
  -- the shape
  have hshape : ∀ x : ℝ, x = 1 / Real.pi * Aav β m *
      ((Real.sqrt (1 - m / gammaOf N B) * Real.sqrt u * y * m ^ ((α - 1) / 2)) / (1 + u * y * m ^ α)) *
        (Efun β m * thetaN β B (plSpec α c N) m) → 0 ≤ x ∧
      x ≤ 1 / Real.pi * Aav β m * (Real.sqrt u * y * m ^ ((α - 1) / 2)) *
        (Efun β m * thetaN β B (plSpec α c N) m) := by
    intro x hx
    have h1 : 0 ≤ 1 - m / gammaOf N B := by
      rw [sub_nonneg, div_le_one hγ]; linarith
    have h2 : Real.sqrt (1 - m / gammaOf N B) ≤ 1 := by
      rw [Real.sqrt_le_one]; linarith [div_nonneg hm.le hγ.le]
    have hden : 1 ≤ 1 + u * y * m ^ α := by
      have : 0 ≤ u * y * m ^ α := by positivity
      linarith
    have hnum0 : 0 ≤ Real.sqrt u * y * m ^ ((α - 1) / 2) := by positivity
    have hEθ0 : 0 ≤ Efun β m * thetaN β B (plSpec α c N) m := by linarith
    refine ⟨by rw [hx]; positivity, ?_⟩
    rw [hx]
    have hfrac : (Real.sqrt (1 - m / gammaOf N B) * Real.sqrt u * y * m ^ ((α - 1) / 2)) / (1 + u * y * m ^ α)
        ≤ Real.sqrt u * y * m ^ ((α - 1) / 2) := by
      rw [div_le_iff₀ (by linarith)]
      calc Real.sqrt (1 - m / gammaOf N B) * Real.sqrt u * y * m ^ ((α - 1) / 2)
          = Real.sqrt (1 - m / gammaOf N B) * (Real.sqrt u * y * m ^ ((α - 1) / 2)) := by ring
        _ ≤ 1 * (Real.sqrt u * y * m ^ ((α - 1) / 2)) := mul_le_mul_of_nonneg_right h2 hnum0
        _ = Real.sqrt u * y * m ^ ((α - 1) / 2) := one_mul _
        _ ≤ (Real.sqrt u * y * m ^ ((α - 1) / 2)) * (1 + u * y * m ^ α) := by
            nlinarith [mul_nonneg hnum0 (show 0 ≤ u * y * m ^ α by positivity)]
    have hA1 : 0 ≤ 1 / Real.pi * Aav β m := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac hA1) hEθ0
  refine ⟨?_, fun hBm => ?_, fun hBm => ?_⟩
  · rw [heq]; exact (hshape _ rfl).1
  · rw [heq]
    refine (hshape _ rfl).2.trans ?_
    obtain ⟨hl, hup⟩ := hv1 N B c m hN hB hc hBm hmγ
    have hBmpos : 0 < (B : ℝ) * m := mul_pos hBr hm
    have hBma : 0 < ((B : ℝ) * m) ^ α := Real.rpow_pos_of_pos hBmpos α
    have hKa : 0 < Kc α ^ α := Real.rpow_pos_of_pos hK α
    have e : (m * icCross α B) ^ α = ((B : ℝ) * m) ^ α / Kc α ^ α := by
      unfold icCross
      rw [← Real.div_rpow hBmpos.le hK.le]; congr 1; ring
    have hU : u ≤ C₂ * Kc α ^ α := by
      rw [hu, e, div_div_eq_mul_div, div_le_iff₀ hBma]
      calc c * lam * Kc α ^ α ≤ C₂ * ((B : ℝ) * m) ^ α * Kc α ^ α :=
            mul_le_mul_of_nonneg_right hup hKa.le
        _ = C₂ * Kc α ^ α * ((B : ℝ) * m) ^ α := by ring
    have hsU := hsqrt_u _ hU
    have hsU0 : 0 ≤ Real.sqrt (C₂ * Kc α ^ α) := Real.sqrt_nonneg _
    have hsu0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
    have hT : 0 < 1 / Real.pi := by positivity
    have hEθ0 : 0 ≤ Efun β m * thetaN β B (plSpec α c N) m := by linarith
    have hK1 : 1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) ≤
        1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1 := by linarith
    have hK0 : 0 ≤ 1 / Real.pi * BA * Cθ * Real.sqrt (C₂ * Kc α ^ α) := by positivity
    have hK0' : 0 ≤ 1 / Real.pi * Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) := by positivity
    have hKB : 1 / Real.pi * BA * Cθ * Real.sqrt (C₂ * Kc α ^ α) ≤
        1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1 := by
      have : 1 / Real.pi * BA * Cθ * Real.sqrt (C₂ * Kc α ^ α) ≤
          1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) := by
        apply mul_le_mul_of_nonneg_right _ hsU0
        apply mul_le_mul_of_nonneg_right _ hCθ.le
        exact mul_le_mul_of_nonneg_left (le_max_left _ _) hT.le
      linarith
    have hKC : 1 / Real.pi * Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) ≤
        1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1 := by
      have : 1 / Real.pi * Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) ≤
          1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) := by
        apply mul_le_mul_of_nonneg_right _ hsU0
        apply mul_le_mul_of_nonneg_right _ hCθ.le
        exact mul_le_mul_of_nonneg_left (le_max_right _ _) hT.le
      linarith
    have hm2 : 0 ≤ m ^ ((α - 2) / 2) := (Real.rpow_pos_of_pos hm _).le
    have hm3 : 0 ≤ m ^ ((α - 1) / 2) := hmκ.le
    rcases le_total m 1 with hm1 | hm1
    · have hAb := hAsm hm1
      have hmm : m ^ (-(1 / 2 : ℝ)) * m ^ ((α - 1) / 2) = m ^ ((α - 2) / 2) := by
        rw [← Real.rpow_add hm]; congr 1; ring
      have hBAm : 0 ≤ BA * m ^ (-(1 / 2 : ℝ)) := by
        have := Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ)); positivity
      calc 1 / Real.pi * Aav β m * (Real.sqrt u * y * m ^ ((α - 1) / 2)) *
            (Efun β m * thetaN β B (plSpec α c N) m)
          ≤ 1 / Real.pi * (BA * m ^ (-(1 / 2 : ℝ))) *
              (Real.sqrt (C₂ * Kc α ^ α) * y * m ^ ((α - 1) / 2)) * Cθ :=
            pg6p6_mono4 hT.le hA0 hAb hsu0 hsU hy0.le hm3 (by linarith) hEθ2
        _ = (1 / Real.pi * BA * Cθ * Real.sqrt (C₂ * Kc α ^ α)) * y * (m ^ (-(1 / 2 : ℝ)) * m ^ ((α - 1) / 2)) := by
            ring
        _ = (1 / Real.pi * BA * Cθ * Real.sqrt (C₂ * Kc α ^ α)) * y * m ^ ((α - 2) / 2) := by rw [hmm]
        _ ≤ (1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1) * y *
              (m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2)) :=
            pg6p6_lift_p hKB hK0 hy0.le hm2 hm3
    · have hAb := (hAl m hm1).2
      calc 1 / Real.pi * Aav β m * (Real.sqrt u * y * m ^ ((α - 1) / 2)) *
            (Efun β m * thetaN β B (plSpec α c N) m)
          ≤ 1 / Real.pi * Ca * (Real.sqrt (C₂ * Kc α ^ α) * y * m ^ ((α - 1) / 2)) * Cθ :=
            pg6p6_mono4 hT.le hA0 hAb hsu0 hsU hy0.le hm3 (by linarith) hEθ2
        _ = (1 / Real.pi * Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α)) * y * m ^ ((α - 1) / 2) := by ring
        _ ≤ (1 / Real.pi * max BA Ca * Cθ * Real.sqrt (C₂ * Kc α ^ α) + 1) * y *
              (m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2)) :=
            pg6p6_lift_q hKC hK0' hy0.le hm2 hm3
  · rw [heq]
    refine (hshape _ rfl).2.trans ?_
    obtain ⟨hl, hup⟩ := hv2 N B c m hN hB hc hm hBm hmγ
    have hm1 : m ≤ 1 := by
      have : 1 / (B : ℝ) ≤ 1 := by rw [div_le_one hBr]; exact hB1
      linarith
    have hAb := hAsm hm1
    have hia : 0 < icCross α B ^ α := Real.rpow_pos_of_pos hic α
    have hsq : Real.sqrt u * m ^ ((α - 1) / 2) ≤ Real.sqrt (D₂ * ((B : ℝ) / icCross α B ^ α)) := by
      have e1 : Real.sqrt u * m ^ ((α - 1) / 2) = Real.sqrt (u * m ^ (α - 1)) := by
        rw [Real.sqrt_mul hu0.le, Real.sqrt_eq_rpow (m ^ (α - 1)), ← Real.rpow_mul hm.le]
        congr 2; ring
      rw [e1]
      apply Real.sqrt_le_sqrt
      have e2 : u * m ^ (α - 1) = c * lam / (m * icCross α B ^ α) := by
        rw [hu, Real.mul_rpow hm.le hic.le, Real.rpow_sub_one hm.ne']
        field_simp
      rw [e2, div_le_iff₀ (mul_pos hm hia)]
      calc c * lam ≤ D₂ * ((B : ℝ) * m) := hup
        _ = D₂ * ((B : ℝ) / icCross α B ^ α) * (m * icCross α B ^ α) := by
          field_simp
    have hsS0 : 0 ≤ Real.sqrt (D₂ * ((B : ℝ) / icCross α B ^ α)) := Real.sqrt_nonneg _
    have hT : 0 < 1 / Real.pi := by positivity
    have hEθ0 : 0 ≤ Efun β m * thetaN β B (plSpec α c N) m := by linarith
    have hBAm : 0 ≤ BA * m ^ (-(1 / 2 : ℝ)) := by
      have := Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ)); positivity
    have hre : 1 / Real.pi * Aav β m * (Real.sqrt u * y * m ^ ((α - 1) / 2)) *
          (Efun β m * thetaN β B (plSpec α c N) m) =
        1 / Real.pi * Aav β m * ((Real.sqrt u * m ^ ((α - 1) / 2)) * y * 1) *
          (Efun β m * thetaN β B (plSpec α c N) m) := by ring
    rw [hre]
    have hK2 : 0 ≤ 1 / Real.pi * BA * Cθ * Real.sqrt D₂ := by positivity
    calc 1 / Real.pi * Aav β m * ((Real.sqrt u * m ^ ((α - 1) / 2)) * y * 1) *
          (Efun β m * thetaN β B (plSpec α c N) m)
        ≤ 1 / Real.pi * (BA * m ^ (-(1 / 2 : ℝ))) *
            (Real.sqrt (D₂ * ((B : ℝ) / icCross α B ^ α)) * y * 1) * Cθ :=
          pg6p6_mono4 hT.le hA0 hAb (by positivity) hsq hy0.le zero_le_one (by linarith) hEθ2
      _ = (1 / Real.pi * BA * Cθ * Real.sqrt D₂) * y * Real.sqrt ((B : ℝ) / icCross α B ^ α) *
            m ^ (-(1 / 2 : ℝ)) := by
          rw [Real.sqrt_mul hD₂.le]; ring
      _ ≤ (1 / Real.pi * BA * Cθ * Real.sqrt D₂ + 1) * y * Real.sqrt ((B : ℝ) / icCross α B ^ α) *
            m ^ (-(1 / 2 : ℝ)) := by
          have h1 : 0 ≤ y * Real.sqrt ((B : ℝ) / icCross α B ^ α) * m ^ (-(1 / 2 : ℝ)) := by
            have := Real.rpow_pos_of_pos hm (-(1 / 2 : ℝ))
            positivity
          nlinarith

private lemma pg6p6_pointwise {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) {y : ℝ}
    (hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 y))
    {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n => 1 / (Real.pi * gammaOf (N n) (B n) * bN α (c n) (N n) (B n)) *
      (Aav β m * partBfun (B n) (plSpec α (c n) (N n)) (i n) m * Efun β m *
        thetaN β (B n) (plSpec α (c n) (N n)) m)) atTop
      (𝓝 (1 / Real.pi * (Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
        (1 + (α - 1) * Efun β m / m)))) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  have hBm : Tendsto (fun n => ((B n : ℕ) : ℝ) * (fun _ : ℕ => m) n) atTop atTop :=
    hreg.hB.atTop_mul_const hm
  have hmγ : Tendsto (fun n => (fun _ : ℕ => m) n / gammaOf (N n) (B n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hreg.hγ
  have hu := lem_app_pl_finite_inverse_iv_i hreg hα (fun _ => m) hBm hmγ
  have hw := lem_app_pl_finite_inverse_iv_ii hreg hα (fun _ => m) hBm hmγ
  have hpos : ∀ n, 0 < (((B n : ℕ) : ℝ) * m / Kc α) ^ α := fun n => by
    have : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    exact Real.rpow_pos_of_pos (by positivity) α
  have hu1 : Tendsto (fun n => c n * partLam (B n) (plSpec α (c n) (N n)) m /
      (m * icCross α (B n)) ^ α) atTop (𝓝 1) := by
    have h := (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun n => (hpos n).ne'))).1 hu
    refine h.congr (fun n => ?_)
    simp only [Pi.div_apply]
    congr 2
    unfold icCross
    ring
  have hγ1 : Tendsto (fun n => 1 - m / gammaOf (N n) (B n)) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub hmγ
    simpa using this
  have hsq1 : Tendsto (fun n => Real.sqrt (1 - m / gammaOf (N n) (B n))) atTop (𝓝 1) := by
    have := hγ1.sqrt
    simpa using this
  have hsq2 : Tendsto (fun n => Real.sqrt (c n * partLam (B n) (plSpec α (c n) (N n)) m /
      (m * icCross α (B n)) ^ α)) atTop (𝓝 1) := by
    have := hu1.sqrt
    simpa using this
  have hy0 : 0 ≤ y := ge_of_tendsto hy (Eventually.of_forall (fun n =>
    Real.rpow_nonneg (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)).le α))
  have hmκ : 0 < m ^ ((α - 1) / 2) := Real.rpow_pos_of_pos hm _
  have hmα : 0 < m ^ α := Real.rpow_pos_of_pos hm α
  have hnum : Tendsto (fun n => (Real.sqrt (1 - m / gammaOf (N n) (B n)) *
      Real.sqrt (c n * partLam (B n) (plSpec α (c n) (N n)) m / (m * icCross α (B n)) ^ α) *
      (icCross α (B n) / rowNum (i n)) ^ α * m ^ ((α - 1) / 2)) /
      (1 + c n * partLam (B n) (plSpec α (c n) (N n)) m / (m * icCross α (B n)) ^ α *
        (icCross α (B n) / rowNum (i n)) ^ α * m ^ α)) atTop
      (𝓝 ((1 * 1 * y * m ^ ((α - 1) / 2)) / (1 + 1 * y * m ^ α))) := by
    refine Tendsto.div (((hsq1.mul hsq2).mul hy).mul_const _)
      ((tendsto_const_nhds.add ((hu1.mul hy).mul_const _))) ?_
    have : 0 ≤ 1 * y * m ^ α := by positivity
    linarith
  -- the theta factor
  have hEpos := pg6p4_E_pos hreg.hβ0 hreg.hβ1 hm
  have hlam' : Tendsto (fun n => deriv (partLam (B n) (plSpec α (c n) (N n))) m /
      partLam (B n) (plSpec α (c n) (N n)) m) atTop (𝓝 (α / m)) := by
    have := hw.div_const m
    refine this.congr (fun n => ?_)
    show m * deriv (partLam (B n) (plSpec α (c n) (N n))) m / partLam (B n) (plSpec α (c n) (N n)) m / m = _
    rw [mul_div_assoc, mul_div_cancel_left₀ _ hm.ne']
  have hγm : Tendsto (fun n => gammaOf (N n) (B n) - m) atTop atTop := by
    have := tendsto_atTop_add_const_right atTop (-m) hreg.hγ
    exact this.congr (fun n => by simp [gammaOf, sub_eq_add_neg])
  have hinv : Tendsto (fun n => 1 / (gammaOf (N n) (B n) - m)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hγm
  have hθ : Tendsto (fun n => thetaN β (B n) (plSpec α (c n) (N n)) m) atTop
      (𝓝 (1 / Efun β m + α / m + 0 - 1 / m)) := by
    unfold thetaN
    exact (((tendsto_const_nhds.add hlam').add hinv).sub tendsto_const_nhds)
  have hEθ := hθ.const_mul (Efun β m)
  have hfull := (((tendsto_const_nhds (x := 1 / Real.pi * Aav β m)).mul hnum).mul hEθ)
  have hlimeq : 1 / Real.pi * Aav β m * (1 * 1 * y * m ^ ((α - 1) / 2) / (1 + 1 * y * m ^ α)) *
      (Efun β m * (1 / Efun β m + α / m + 0 - 1 / m)) =
      1 / Real.pi * (Aav β m * m ^ (-(α + 1) / 2) * (y * m ^ α / (1 + y * m ^ α)) *
        (1 + (α - 1) * Efun β m / m)) := by
    have e1 : m ^ ((α - 1) / 2) = m ^ (-(α + 1) / 2) * m ^ α := by
      rw [← Real.rpow_add hm]; congr 1; ring
    have hD : 0 < 1 + y * m ^ α := by positivity
    rw [e1]
    have := hEpos.ne'
    have := hm.ne'
    field_simp
    ring
  rw [← hlimeq]
  refine hfull.congr' ?_
  filter_upwards [hreg.hγ.eventually_gt_atTop m] with n hn
  have hmI : m ∈ Ioo 0 (gammaOf (N n) (B n)) := ⟨hm, hn⟩
  exact (pg6p6_Fn_eq (β := β) hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) hmI).symm

private lemma pg6p6_dct_head {M : ℝ} (hM : 0 < M) (F : ℕ → ℝ → ℝ) (Flim g : ℝ → ℝ) (t s : ℕ → ℝ)
    (hg : IntegrableOn g (Ioo 0 M)) (hg0 : ∀ m ∈ Ioo 0 M, 0 ≤ g m)
    (hmeas : ∀ᶠ n in atTop, AEStronglyMeasurable (F n) (volume.restrict (Ioo 0 M)))
    (hnn : ∀ᶠ n in atTop, ∀ m ∈ Ioo 0 M, 0 ≤ F n m)
    (ht0 : ∀ᶠ n in atTop, 0 < t n ∧ t n ≤ M) (hs0 : ∀ᶠ n in atTop, 0 ≤ s n)
    (hbig : ∀ᶠ n in atTop, ∀ m ∈ Ioo 0 M, t n < m → F n m ≤ g m)
    (hsmall : ∀ᶠ n in atTop, ∀ m ∈ Ioo 0 M, m ≤ t n → F n m ≤ s n * m ^ (-(1 / 2 : ℝ)))
    (hts : Tendsto (fun n => s n * (2 * t n ^ (1 / 2 : ℝ))) atTop (𝓝 0))
    (ht : Tendsto t atTop (𝓝 0))
    (hlim : ∀ m ∈ Ioo 0 M, Tendsto (fun n => F n m) atTop (𝓝 (Flim m))) :
    Tendsto (fun n => ∫ m in Ioo 0 M, F n m) atTop (𝓝 (∫ m in Ioo 0 M, Flim m)) := by
  have hr : IntegrableOn (fun m : ℝ => m ^ (-(1 / 2 : ℝ))) (Ioc 0 M) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M) (by norm_num : (-1 : ℝ) < -(1 / 2)) |>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1)
  have hroo : IntegrableOn (fun m : ℝ => m ^ (-(1 / 2 : ℝ))) (Ioo 0 M) :=
    hr.mono_set Ioo_subset_Ioc_self
  have hFint : ∀ᶠ n in atTop, IntegrableOn (F n) (Ioo 0 M) := by
    filter_upwards [hmeas, hnn, ht0, hs0, hbig, hsmall] with n h1 h2 h3 h4 h5 h6
    refine Integrable.mono' (hg.add (hroo.const_mul (s n))) h1 ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with m hm
    rw [Real.norm_eq_abs, abs_of_nonneg (h2 m hm)]
    rcases lt_or_ge (t n) m with h | h
    · have := h5 m hm h
      have : 0 ≤ s n * m ^ (-(1 / 2 : ℝ)) := mul_nonneg h4 (Real.rpow_nonneg hm.1.le _)
      simp only [Pi.add_apply]
      linarith
    · have := h6 m hm h
      have hg0 := hg0 m hm
      simp only [Pi.add_apply]
      linarith
  -- decomposition
  have hdecomp : ∀ᶠ n in atTop, ∫ m in Ioo 0 M, F n m =
      (∫ m in Ioo 0 M, (Ioi (t n)).indicator (F n) m) + ∫ m in Ioo 0 M, (Iic (t n)).indicator (F n) m := by
    filter_upwards [hFint] with n hint
    have hind1 : IntegrableOn ((Ioi (t n)).indicator (F n)) (Ioo 0 M) := hint.indicator measurableSet_Ioi
    have hind2 : IntegrableOn ((Iic (t n)).indicator (F n)) (Ioo 0 M) := hint.indicator measurableSet_Iic
    rw [← integral_add hind1 hind2]
    congr 1
    ext m
    have := Set.indicator_self_add_compl (Ioi (t n)) (F n)
    rw [Set.compl_Ioi] at this
    exact (congrFun this m).symm
  have hbigT : Tendsto (fun n => ∫ m in Ioo 0 M, (Ioi (t n)).indicator (F n) m) atTop
      (𝓝 (∫ m in Ioo 0 M, Flim m)) := by
    refine tendsto_integral_filter_of_dominated_convergence (bound := g) ?_ ?_ hg ?_
    · filter_upwards [hmeas] with n h
      exact h.indicator measurableSet_Ioi
    · filter_upwards [hbig, hnn] with n h5 h2
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with m hm
      by_cases hmt : t n < m
      · rw [Set.indicator_of_mem (show m ∈ Ioi (t n) from hmt), Real.norm_eq_abs,
          abs_of_nonneg (h2 m hm)]
        exact h5 m hm hmt
      · rw [Set.indicator_of_notMem (show m ∉ Ioi (t n) from hmt)]
        simpa using hg0 m hm
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with m hm
      refine (hlim m hm).congr' ?_
      filter_upwards [ht.eventually (gt_mem_nhds hm.1)] with n hn
      rw [Set.indicator_of_mem (show m ∈ Ioi (t n) from hn)]
  have hsmallT : Tendsto (fun n => ∫ m in Ioo 0 M, (Iic (t n)).indicator (F n) m) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hts
    · filter_upwards [hnn] with n h2
      refine setIntegral_nonneg measurableSet_Ioo (fun m hm => ?_)
      by_cases hmt : m ≤ t n
      · rw [Set.indicator_of_mem (show m ∈ Iic (t n) from hmt)]; exact h2 m hm
      · rw [Set.indicator_of_notMem (show m ∉ Iic (t n) from hmt)]
    · filter_upwards [hFint, ht0, hs0, hsmall] with n hint h3 h4 h6
      have hcI : IntegrableOn (fun m : ℝ => s n * m ^ (-(1 / 2 : ℝ))) (Ioo 0 M) := hroo.const_mul (s n)
      have hind1 : IntegrableOn ((Iic (t n)).indicator (F n)) (Ioo 0 M) := hint.indicator measurableSet_Iic
      have hind2 : IntegrableOn ((Iic (t n)).indicator (fun m : ℝ => s n * m ^ (-(1 / 2 : ℝ)))) (Ioo 0 M) :=
        hcI.indicator measurableSet_Iic
      have hmono : ∫ m in Ioo 0 M, (Iic (t n)).indicator (F n) m ≤
          ∫ m in Ioo 0 M, (Iic (t n)).indicator (fun m : ℝ => s n * m ^ (-(1 / 2 : ℝ))) m := by
        refine setIntegral_mono_on hind1 hind2 measurableSet_Ioo (fun m hm => ?_)
        by_cases hmt : m ≤ t n
        · rw [Set.indicator_of_mem (show m ∈ Iic (t n) from hmt),
            Set.indicator_of_mem (show m ∈ Iic (t n) from hmt)]
          exact h6 m hm hmt
        · rw [Set.indicator_of_notMem (show m ∉ Iic (t n) from hmt),
            Set.indicator_of_notMem (show m ∉ Iic (t n) from hmt)]
      refine hmono.trans ?_
      rw [setIntegral_indicator measurableSet_Iic]
      have hIoc : IntegrableOn (fun m : ℝ => s n * m ^ (-(1 / 2 : ℝ))) (Ioc 0 (t n)) :=
        (hr.mono_set (Ioc_subset_Ioc_right h3.2)).const_mul (s n)
      calc ∫ m in Ioo 0 M ∩ Iic (t n), s n * m ^ (-(1 / 2 : ℝ))
          ≤ ∫ m in Ioc 0 (t n), s n * m ^ (-(1 / 2 : ℝ)) := by
            refine setIntegral_mono_set hIoc ?_ ?_
            · filter_upwards [ae_restrict_mem measurableSet_Ioc] with m hm
              exact mul_nonneg h4 (Real.rpow_nonneg hm.1.le _)
            · refine Filter.Eventually.of_forall (fun m hm => ?_)
              exact ⟨hm.1.1, hm.2⟩
        _ = s n * (2 * t n ^ (1 / 2 : ℝ)) := by
            rw [← intervalIntegral.integral_of_le h3.1.le, intervalIntegral.integral_const_mul,
              integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2)))]
            rw [Real.zero_rpow (by norm_num)]
            congr 1
            norm_num
            ring
  have := hbigT.add hsmallT
  rw [add_zero] at this
  exact this.congr' (by filter_upwards [hdecomp] with n hn; exact hn.symm)

private lemma pg6p6_head_conv {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) {y : ℝ}
    (hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 y))
    {M : ℝ} (hM : 0 < M) :
    Tendsto (fun n => sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M /
      bN α (c n) (N n) (B n)) atTop
      (𝓝 (1 / Real.pi * ∫ m in Ioo 0 M, Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m))) := by
  have hα0 : 0 < α := by linarith
  have hK := pg6_Kc_pos hα
  obtain ⟨K1, K2, hK1, hK2, hbd⟩ := pg6p6_Fn_bound (α := α) hα hreg.hβ0 hreg.hβ1
  have hπ := Real.pi_pos
  set Y : ℝ := y + 1 with hY
  have hy0 : 0 ≤ y := ge_of_tendsto hy (Eventually.of_forall (fun n =>
    Real.rpow_nonneg (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)).le α))
  have hYpos : 0 < Y := by rw [hY]; linarith
  set Fn : ℕ → ℝ → ℝ := fun n m => 1 / (Real.pi * gammaOf (N n) (B n) * bN α (c n) (N n) (B n)) *
      (Aav β m * partBfun (B n) (plSpec α (c n) (N n)) (i n) m * Efun β m *
        thetaN β (B n) (plSpec α (c n) (N n)) m) with hFn
  set Flim : ℝ → ℝ := fun m => 1 / Real.pi * (Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m)) with hFlim
  have hconv : ∀ n, sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M /
      bN α (c n) (N n) (B n) = ∫ m in Ioo 0 M, Fn n m := by
    intro n
    have hbN := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
    have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    unfold sqrt2DPiece
    simp only [hFn]
    rw [integral_const_mul]
    field_simp
  have hint : (∫ m in Ioo 0 M, Flim m) = 1 / Real.pi * ∫ m in Ioo 0 M, Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m) := by
    simp only [hFlim]
    rw [integral_const_mul]
  simp_rw [hconv]
  rw [← hint]
  have hr1 : IntegrableOn (fun m : ℝ => m ^ ((α - 2) / 2)) (Ioc 0 M) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M) (by linarith : (-1 : ℝ) < (α - 2) / 2) |>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1)
  have hr2 : IntegrableOn (fun m : ℝ => m ^ ((α - 1) / 2)) (Ioc 0 M) :=
    (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := M) (by linarith : (-1 : ℝ) < (α - 1) / 2) |>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hM.le).1)
  have hgint : IntegrableOn (fun m : ℝ => K1 * Y * (m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2))) (Ioo 0 M) :=
    ((hr1.add hr2).mono_set Ioo_subset_Ioc_self).const_mul _
  have hγ2 : ∀ᶠ n in atTop, max 2 (2 * M) ≤ gammaOf (N n) (B n) := hreg.hγ.eventually_ge_atTop _
  have hyY : ∀ᶠ n in atTop, (icCross α (B n) / rowNum (i n)) ^ α ≤ Y :=
    hy.eventually (ge_mem_nhds (by rw [hY]; linarith))
  have hyn0 : ∀ n, 0 ≤ (icCross α (B n) / rowNum (i n)) ^ α := fun n =>
    Real.rpow_nonneg (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)).le α
  refine pg6p6_dct_head hM Fn Flim (fun m => K1 * Y * (m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2)))
    (fun n => 1 / (B n : ℝ)) (fun n => K2 * Y * Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α))
    hgint ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro m hm
    have := Real.rpow_pos_of_pos hm.1 ((α - 2) / 2)
    have := Real.rpow_pos_of_pos hm.1 ((α - 1) / 2)
    positivity
  · filter_upwards [hγ2] with n hn
    have hγM : M ≤ gammaOf (N n) (B n) := by
      have := (le_max_right 2 (2 * M)).trans hn; linarith
    have := pg6p2_f_int (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n) (hreg.hNpos n)
      (pg6_plSpec_anti hα0 (hreg.hcpos n)) (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n)
    exact (((this.mono_set (Ioo_subset_Ioo_right hγM)).const_mul
      (1 / (Real.pi * gammaOf (N n) (B n) * bN α (c n) (N n) (B n)))).aestronglyMeasurable)
  · filter_upwards [hγ2] with n hn m hm
    have h2 : 2 ≤ gammaOf (N n) (B n) := (le_max_left _ _).trans hn
    have h2M : 2 * M ≤ gammaOf (N n) (B n) := (le_max_right _ _).trans hn
    exact (hbd (N n) (B n) (c n) (hreg.hNpos n) (hreg.hBpos n) (hreg.hcpos n) h2 (i n) m hm.1
      (by linarith [hm.2])).1
  · filter_upwards [hreg.hB.eventually_ge_atTop (1 / M)] with n hn
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    refine ⟨by positivity, ?_⟩
    rw [div_le_iff₀ hBr]
    rw [div_le_iff₀ hM] at hn
    linarith
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · filter_upwards [hγ2, hyY] with n hn hyn m hm hmt
    have h2 : 2 ≤ gammaOf (N n) (B n) := (le_max_left _ _).trans hn
    have h2M : 2 * M ≤ gammaOf (N n) (B n) := (le_max_right _ _).trans hn
    refine (hbd (N n) (B n) (c n) (hreg.hNpos n) (hreg.hBpos n) (hreg.hcpos n) h2 (i n) m hm.1
      (by linarith [hm.2])).2.1 hmt.le |>.trans ?_
    have h1 := Real.rpow_pos_of_pos hm.1 ((α - 2) / 2)
    have h3 := Real.rpow_pos_of_pos hm.1 ((α - 1) / 2)
    have : 0 ≤ m ^ ((α - 2) / 2) + m ^ ((α - 1) / 2) := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hyn hK1.le) this
  · filter_upwards [hγ2, hyY] with n hn hyn m hm hmt
    have h2 : 2 ≤ gammaOf (N n) (B n) := (le_max_left _ _).trans hn
    have h2M : 2 * M ≤ gammaOf (N n) (B n) := (le_max_right _ _).trans hn
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    refine (hbd (N n) (B n) (c n) (hreg.hNpos n) (hreg.hBpos n) (hreg.hcpos n) h2 (i n) m hm.1
      (by linarith [hm.2])).2.2 hmt |>.trans ?_
    have h1 := Real.rpow_pos_of_pos hm.1 (-(1 / 2 : ℝ))
    have hs : 0 ≤ Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α) := Real.sqrt_nonneg _
    calc K2 * (icCross α (B n) / rowNum (i n)) ^ α * Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α) *
          m ^ (-(1 / 2 : ℝ))
        ≤ K2 * Y * Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α) * m ^ (-(1 / 2 : ℝ)) := by
          apply mul_le_mul_of_nonneg_right _ h1.le
          apply mul_le_mul_of_nonneg_right _ hs
          exact mul_le_mul_of_nonneg_left hyn hK2.le
      _ = _ := rfl
  · have hic : Tendsto (fun n => icCross α (B n)) atTop atTop := by
      have := hreg.hB.atTop_div_const hK
      exact this
    have hica : Tendsto (fun n => icCross α (B n) ^ α) atTop atTop :=
      (tendsto_rpow_atTop hα0).comp hic
    have h1 : Tendsto (fun n => 1 / icCross α (B n) ^ α) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hica
    have h2 := (h1.sqrt).const_mul (2 * K2 * Y)
    rw [Real.sqrt_zero, mul_zero] at h2
    refine h2.congr (fun n => ?_)
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    have hia : 0 < icCross α (B n) ^ α := Real.rpow_pos_of_pos (pg6_icCross_pos hα (hreg.hBpos n)) α
    show 2 * K2 * Y * Real.sqrt (1 / icCross α (B n) ^ α) =
      K2 * Y * Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α) * (2 * (1 / (B n : ℝ)) ^ (1 / 2 : ℝ))
    rw [← Real.sqrt_eq_rpow]
    have e : Real.sqrt ((B n : ℝ) / icCross α (B n) ^ α) * Real.sqrt (1 / (B n : ℝ)) =
        Real.sqrt (1 / icCross α (B n) ^ α) := by
      rw [← Real.sqrt_mul (by positivity)]
      congr 1
      field_simp
    linear_combination (-(2 * K2 * Y)) * e
  · exact tendsto_const_nhds.div_atTop hreg.hB
  · intro m hm
    exact pg6p6_pointwise hreg hα i hy hm.1

private lemma pg6p6_E3_real {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) {y : ℝ} (hy0 : 0 < y)
    (hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 y)) :
    Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
        bN α (c n) (N n) (B n)) atTop (𝓝 (profPhi α β y)) := by
  have hα0 : 0 < α := by linarith
  obtain ⟨C1, M0, hC1, hM0, htail⟩ := pg6p6_tail_bound hreg hα i
  have hκ : 0 < (α - 1) / 2 := by linarith
  refine pg6p6_abs_combine
    (fun M n => sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M / bN α (c n) (N n) (B n))
    (fun M n => sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) M (gammaOf (N n) (B n)) /
        bN α (c n) (N n) (B n))
    (fun M => 1 / Real.pi * ∫ m in Ioo 0 M, Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m))
    C1 M0 ((α - 1) / 2) hM0 hκ ?_ ?_ ?_ ?_
  · intro M hM
    have hM' : 0 < M := lt_of_lt_of_le hM0 hM
    filter_upwards [hreg.hγ.eventually_gt_atTop M] with n hn
    have hsplit := pg6_split (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n) (hreg.hNpos n)
      (pg6_plSpec_anti hα0 (hreg.hcpos n)) (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n) hM' hn
    rw [hsplit, add_div]
  · intro M hM
    exact pg6p6_head_conv hreg hα i hy (lt_of_lt_of_le hM0 hM)
  · have hint : IntegrableOn (fun m : ℝ => Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m)) (Ioi 0) :=
      pg6p4_m_integrable hα hreg.hβ0 hreg.hβ1 hy0
    have h1 := intervalIntegral_tendsto_integral_Ioi (0:ℝ) hint tendsto_id
    have h2 : Tendsto (fun M : ℝ => 1 / Real.pi * ∫ m in (0:ℝ)..M, Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m)) atTop
        (𝓝 (1 / Real.pi * ∫ m in Ioi (0:ℝ), Aav β m * m ^ (-(α + 1) / 2) *
        (y * m ^ α / (1 + y * m ^ α)) * (1 + (α - 1) * Efun β m / m))) := h1.const_mul _
    rw [← pg6p5_phi_eq hα hreg.hβ0 hreg.hβ1 hy0] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with M hM
    rw [intervalIntegral.integral_of_le hM.le, integral_Ioc_eq_integral_Ioo]
  · intro M hM
    filter_upwards [htail M hM] with n hn
    exact hn


private lemma pg6p6_case_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) {x : ℝ} (hx0 : 0 < x)
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 x)) :
    IsEquivalent atTop
      (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n))
      (fun n => profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 (x ^ (-α))) := by
    have h1 : Tendsto (fun n => (rowNum (i n) / icCross α (B n))⁻¹) atTop (𝓝 x⁻¹) :=
      h.inv₀ hx0.ne'
    have h2 := (Real.continuousAt_rpow_const x⁻¹ α (Or.inl (inv_ne_zero hx0.ne'))).tendsto.comp h1
    have h3 : x ^ (-α) = (x⁻¹) ^ α := by rw [Real.rpow_neg hx0.le, Real.inv_rpow hx0.le]
    rw [h3]
    refine h2.congr (fun n => ?_)
    simp [Function.comp, inv_div]
  have hE3 := pg6p6_E3_real hreg hα i (Real.rpow_pos_of_pos hx0 _) hy
  have hΦ : ContinuousAt (profPhi α β) (x ^ (-α)) := by
    have := (lem_app_pl_super_i hα hreg.hβ0 hreg.hβ1).1
    exact this.continuousAt (Ioi_mem_nhds (Real.rpow_pos_of_pos hx0 _))
  have hpos : 0 < profPhi α β (x ^ (-α)) :=
    ((lem_app_pl_super_i hα hreg.hβ0 hreg.hβ1).2 _ (Real.rpow_pos_of_pos hx0 _)).2
  refine isEquivalent_of_tendsto_one ?_
  have := hE3.div (hΦ.tendsto.comp hy) hpos.ne'
  rw [div_self hpos.ne'] at this
  exact this

private lemma pg6p6_case_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n))
      (fun n => profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
  have hE1 := pg6p6_E1 hreg hα i hx h
  have hpos : ∀ n, 0 < rowNum (i n) / icCross α (B n) := fun n =>
    div_pos (pg6_rowNum_pos _) (pg6_icCross_pos hα (hreg.hBpos n))
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop atTop := by
    have h1 : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall hpos⟩
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    have h3 := (tendsto_rpow_atTop (by linarith : 0 < α)).comp h2
    refine h3.congr (fun n => ?_)
    simp [Function.comp, inv_div]
  have hΦ := (lem_app_pl_super_ii hα hreg.hβ0 hreg.hβ1).comp_tendsto hy
  have hdiv := hE1.div (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n)))
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  refine (hdiv.congr_right ?_).trans hΦ.symm
  refine Eventually.of_forall (fun n => ?_)
  have hb := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
  have hm := pg6_bN_main hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) (sPow β 2) hs2
  simp only [Pi.div_apply]
  rw [← hm]
  field_simp
  rfl

private lemma pg6p6_case_inf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop
      (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n))
      (fun n => profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
  have hE2 := pg6p6_E2 hreg hα i hx h
  have hpos : ∀ n, 0 < icCross α (B n) / rowNum (i n) := fun n =>
    div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝[>] 0) := by
    have h1 : Tendsto (fun n => icCross α (B n) / rowNum (i n)) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp h
      refine this.congr (fun n => ?_)
      simp [Function.comp, inv_div]
    have h2 : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr (by linarith))).tendsto.comp h1
      rw [Real.zero_rpow (by linarith)] at this
      exact this
    exact tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall (fun n =>
      Real.rpow_pos_of_pos (hpos n) _)⟩
  have hΦ := (lem_app_pl_super_iii hα hreg.hβ0 hreg.hβ1).comp_tendsto hy
  have hT := (hE2.trans (pg6_psi_small hreg hα i hx))
  have hdiv := hT.div (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n)))
  refine (hdiv.congr_right ?_).trans hΦ.symm
  refine Eventually.of_forall (fun n => ?_)
  have hb := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
  have hR := pg6_R_alg hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)
  simp only [Pi.div_apply]
  rw [← hR]
  field_simp
  rfl

/-- `lem:app-pl-super`, part (iv), the joint row statement (snapshot `cr-2026-10-23`). LaTeX,
verbatim from `sections/06-power-law/section.tex`:

\begin{lemma}[The supercritical drift profile]\label{lem:app-pl-super}
Let $\alpha>1$ and $p_\alpha\defeq(\alpha-1)/(2\alpha)$. The function $\Phi_{\alpha,\bmom}$ of
\cref{eqn:app-pl-Phi} is finite, positive and continuous on $(0,\infty)$, and
\[
\Phi_{\alpha,\bmom}(y)\sim\sqrt{y/\sw2}\quad(y\to\infty),\qquad \Phi_{\alpha,\bmom}(y)\sim d_\alpha y^{p_\alpha}\quad(y\downarrow0).
\]
Under \cref{assum:app-pl-regime}, for every row sequence $i\to\infty$ with $i/N\to0$,
\[
\frac{\sqrt2\,\mathfrak d_i(0)}{b_N}\sim\Phi_{\alpha,\bmom}\big((i_{\mathrm c}/i)^\alpha\big).
\]
\end{lemma}
-/
theorem lem_app_pl_super_iv {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    IsEquivalent atTop
      (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n))
      (fun n => profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
  have hα0 : 0 < α := by linarith
  apply pg6_equiv_subseq
  · intro n
    exact ((lem_app_pl_super_i hα hreg.hβ0 hreg.hβ1).2 _
      (Real.rpow_pos_of_pos (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)) _)).2
  · intro φ hφ
    set r : ℕ → ℝ := fun n => rowNum (i (φ n)) / icCross α (B (φ n)) with hr
    have hr0 : ∀ n, 0 < r n := fun n =>
      div_pos (pg6_rowNum_pos _) (pg6_icCross_pos hα (hreg.hBpos _))
    by_cases hb : ∃ K : ℝ, ∃ᶠ n in atTop, r n ≤ K
    · obtain ⟨K, hK⟩ := hb
      obtain ⟨x, hxcl, ψ, hψ, hxψ⟩ := tendsto_subseq_of_frequently_bounded
        (Metric.isBounded_Icc (0:ℝ) K) (hK.mono (fun n hn => ⟨(hr0 n).le, hn⟩))
      have hx0 : 0 ≤ x := by
        rw [closure_Icc] at hxcl; exact hxcl.1
      refine ⟨ψ, hψ.tendsto_atTop, ?_⟩
      have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
      have hreg' := pg6_reg_comp hreg hθ
      have hx' : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) :=
        hx.comp hθ
      rcases hx0.eq_or_lt with h0 | hpos
      · have h' : Tendsto (fun n => rowNum (i (φ (ψ n))) / icCross α (B (φ (ψ n)))) atTop (𝓝 0) := by
          rw [h0]; exact hxψ
        exact pg6p6_case_zero hreg' hα (fun n => i (φ (ψ n))) hx' h'
      · exact pg6p6_case_pos hreg' hα (fun n => i (φ (ψ n))) hpos hxψ
    · have hb' : ∀ K : ℝ, ∀ᶠ n in atTop, K < r n := by
        intro K
        by_contra hcon
        exact hb ⟨K, (Filter.not_eventually.1 hcon).mono (fun n hn => not_lt.1 hn)⟩
      have hrinf : Tendsto r atTop atTop := tendsto_atTop.2 (fun K => (hb' K).mono (fun n hn => hn.le))
      refine ⟨fun n => n, tendsto_id, ?_⟩
      have hreg' := pg6_reg_comp hreg hφ
      have hx' : Tendsto (fun n => rowNum (i (φ n)) / (N (φ n) : ℝ)) atTop (𝓝 0) := hx.comp hφ
      exact pg6p6_case_inf hreg' hα (fun n => i (φ n)) hx' hrinf

private lemma pg6_ii_a {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
          bN α (c n) (N n) (B n)) atTop (𝓝 (profPhi α β (x ^ (-α)))) := by
  intro x hx h
  have hx0 : (0 : ℝ) < x := hx
  have hEq := lem_app_pl_super_iv hreg hα i hi (pg6_ii_rowN_zero hreg hα i h)
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 (x ^ (-α))) := by
    have h1 : Tendsto (fun n => (rowNum (i n) / icCross α (B n))⁻¹) atTop (𝓝 x⁻¹) :=
      h.inv₀ hx0.ne'
    have h2 := (Real.continuousAt_rpow_const x⁻¹ α (Or.inl (inv_ne_zero hx0.ne'))).tendsto.comp h1
    have h3 : x ^ (-α) = (x⁻¹) ^ α := by rw [Real.rpow_neg hx0.le, Real.inv_rpow hx0.le]
    rw [h3]
    refine h2.congr (fun n => ?_)
    simp [Function.comp, inv_div]
  have hΦ : ContinuousAt (profPhi α β) (x ^ (-α)) := by
    have := (lem_app_pl_super_i hα hreg.hβ0 hreg.hβ1).1
    exact this.continuousAt (Ioi_mem_nhds (Real.rpow_pos_of_pos hx0 _))
  exact hEq.symm.tendsto_nhds (hΦ.tendsto.comp hy)

private lemma pg6_ii_b {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0)) :
    IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) := by
  have hEq := lem_app_pl_super_iv hreg hα i hi (pg6_ii_rowN_zero hreg hα i h)
  have hpos : ∀ n, 0 < rowNum (i n) / icCross α (B n) := fun n =>
    div_pos (pg6_rowNum_pos _) (pg6_icCross_pos hα (hreg.hBpos n))
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop atTop := by
    have h1 : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨h, Eventually.of_forall hpos⟩
    have h2 := tendsto_inv_nhdsGT_zero.comp h1
    have h3 := (tendsto_rpow_atTop (by linarith : 0 < α)).comp h2
    refine h3.congr (fun n => ?_)
    simp [Function.comp, inv_div]
  have hΦ := (lem_app_pl_super_ii hα hreg.hβ0 hreg.hβ1).comp_tendsto hy
  have h4 : IsEquivalent atTop (fun n => bN α (c n) (N n) (B n) *
        (Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n)))
      (fun n => bN α (c n) (N n) (B n) *
        Real.sqrt ((icCross α (B n) / rowNum (i n)) ^ α / sPow β 2)) :=
    (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n))).mul (hEq.trans hΦ)
  refine (h4.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall (fun n => ?_)
    have hb : bN α (c n) (N n) (B n) ≠ 0 := by
      intro h0
      obtain ⟨-, h1⟩ := pg6_bN_sq hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
      rw [h0] at h1
      have hic := pg6_icCross_pos hα (hreg.hBpos n)
      have : (0 : ℝ) < (N n) := by exact_mod_cast hreg.hNpos n
      have : (0 : ℝ) < (B n) := by exact_mod_cast hreg.hBpos n
      have := hreg.hcpos n
      have : 0 < c n / ((N n : ℝ) / (B n : ℝ) * icCross α (B n) ^ α) := by positivity
      rw [← h1] at this
      norm_num at this
    simp only
    field_simp
  · refine Eventually.of_forall (fun n => ?_)
    exact pg6_bN_main hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n) _ (pg6_sPow_two_pos hreg.hβ0 hreg.hβ1)



private lemma pg6_ii_small {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
          rowNum (i n) ^ (-(α - 1) / 2)) := by
  have hEq := lem_app_pl_super_iv hreg hα i hi hx
  have hpos : ∀ n, 0 < icCross α (B n) / rowNum (i n) := fun n =>
    div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝[>] 0) := by
    have h1 : Tendsto (fun n => icCross α (B n) / rowNum (i n)) atTop (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp h
      refine this.congr (fun n => ?_)
      simp [Function.comp, inv_div]
    have h2 : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr (by linarith))).tendsto.comp h1
      rw [Real.zero_rpow (by linarith)] at this
      exact this
    exact tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall (fun n =>
      Real.rpow_pos_of_pos (hpos n) _)⟩
  have hΦ := (lem_app_pl_super_iii hα hreg.hβ0 hreg.hβ1).comp_tendsto hy
  have h4 : IsEquivalent atTop (fun n => bN α (c n) (N n) (B n) *
        (Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n)))
      (fun n => bN α (c n) (N n) (B n) *
        (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α)))) :=
    (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n))).mul (hEq.trans hΦ)
  refine (h4.congr_left ?_).congr_right ?_
  · refine Eventually.of_forall (fun n => ?_)
    have hb : bN α (c n) (N n) (B n) ≠ 0 := by
      intro h0
      obtain ⟨-, h1⟩ := pg6_bN_sq hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
      rw [h0] at h1
      have hic := pg6_icCross_pos hα (hreg.hBpos n)
      have : (0 : ℝ) < (N n) := by exact_mod_cast hreg.hNpos n
      have : (0 : ℝ) < (B n) := by exact_mod_cast hreg.hBpos n
      have := hreg.hcpos n
      have : 0 < c n / ((N n : ℝ) / (B n : ℝ) * icCross α (B n) ^ α) := by positivity
      rw [← h1] at this
      norm_num at this
    simp only
    field_simp
  · exact Eventually.of_forall (fun n =>
      pg6_R_alg hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n))


private lemma pg6_ii_c1 {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (h : Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) := by
  have hxu : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Icc (0 : ℝ) 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨(div_pos (pg6_rowNum_pos _) this).le, (div_le_one this).2 (pg6_rowNum_le _)⟩
  apply pg6_equiv_subseq
  · intro n
    exact mul_pos (pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n))
      (lem_app_pl_Psi_i_pos hreg.hα _ ⟨div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n),
        (hxu n).2⟩)
  intro φ hφ
  obtain ⟨x0, hx0, ψ, hψ, hxψ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => rowNum (i (φ n)) / (N (φ n) : ℝ)) (fun n => hxu (φ n))
  have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ.tendsto_atTop, ?_⟩
  have hreg' := pg6_reg_comp hreg hθ
  have hi' : Tendsto (fun n => rowNum (i (φ (ψ n)))) atTop atTop := hi.comp hθ
  have h' : Tendsto (fun n => rowNum (i (φ (ψ n))) / icCross α (B (φ (ψ n)))) atTop atTop :=
    h.comp hθ
  rcases hx0.1.eq_or_lt with h0 | h0
  · -- x0 = 0
    have hx : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) := by
      rw [h0]; exact hxψ
    exact (pg6_ii_small hreg' hα (fun n => i (φ (ψ n))) hi' hx h').trans
      (pg6_psi_small hreg' hα (fun n => i (φ (ψ n))) hx).symm
  · refine (pg6_bulk hreg' (fun n => i (φ (ψ n))) (x0 := x0 / 2) (by linarith) ?_).1
    exact hxψ.eventually (eventually_ge_nhds (show x0 / 2 < x0 by linarith))


/-! #### The participation at `1/μ_i` (hypothesis of `lem_app_pl_head_ii`) -/

private lemma pg6_term_eq {α c : ℝ} (hc : 0 < c) {N : ℕ} (i j : Fin N) :
    (1 / plSpec α c N i) * plSpec α c N j / (1 + (1 / plSpec α c N i) * plSpec α c N j) =
      (rowNum i / rowNum j) ^ α / (1 + (rowNum i / rowNum j) ^ α) := by
  have hi := pg6_rowNum_pos i
  have hj := pg6_rowNum_pos j
  have e : (1 / plSpec α c N i) * plSpec α c N j = (rowNum i / rowNum j) ^ α := by
    rw [pg6_plSpec_eq, pg6_plSpec_eq, Real.div_rpow hi.le hj.le, Real.rpow_neg hi.le,
      Real.rpow_neg hj.le]
    have : 0 < rowNum i ^ α := Real.rpow_pos_of_pos hi _
    have : 0 < rowNum j ^ α := Real.rpow_pos_of_pos hj _
    field_simp
  rw [e]

private lemma pg6_sum_range_fin {N : ℕ} (g : ℕ → ℝ) :
    ∑ j : Fin N, g (j : ℕ) = ∑ j ∈ Finset.range N, g j :=
  Fin.sum_univ_eq_sum_range g N

private lemma pg6_mN_lt {α c : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hc : 0 < c) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    partMN B (plSpec α c N) (1 / plSpec α c N i) ≤
      (1 / (1 - α)) * (gammaOf N B * (rowNum i / (N : ℝ)) ^ α) := by
  have hi := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have h1a : 0 < 1 - α := by linarith
  unfold partMN
  have hterm : ∀ j : Fin N, (1 / plSpec α c N i) * plSpec α c N j /
      (1 + (1 / plSpec α c N i) * plSpec α c N j) ≤ rowNum i ^ α * ((j : ℕ) + 1 : ℝ) ^ (-α) := by
    intro j
    rw [pg6_term_eq hc]
    have hj := pg6_rowNum_pos j
    have hX : 0 ≤ (rowNum i / rowNum j) ^ α := Real.rpow_nonneg (by positivity) _
    calc (rowNum i / rowNum j) ^ α / (1 + (rowNum i / rowNum j) ^ α) ≤ (rowNum i / rowNum j) ^ α := by
          rw [div_le_iff₀ (by linarith)]; nlinarith
      _ = rowNum i ^ α * ((j : ℕ) + 1 : ℝ) ^ (-α) := by
          change _ = rowNum i ^ α * rowNum j ^ (-α)
          rw [Real.div_rpow hi.le hj.le, Real.rpow_neg hj.le, div_eq_mul_inv]
  have hsum : ∑ j : Fin N, (1 / plSpec α c N i) * plSpec α c N j /
      (1 + (1 / plSpec α c N i) * plSpec α c N j) ≤
      rowNum i ^ α * ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (-α) := by
    calc _ ≤ ∑ j : Fin N, rowNum i ^ α * ((j : ℕ) + 1 : ℝ) ^ (-α) :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = rowNum i ^ α * ∑ j : Fin N, ((j : ℕ) + 1 : ℝ) ^ (-α) := by rw [Finset.mul_sum]
      _ = _ := by rw [pg6_sum_range_fin (fun j : ℕ => ((j : ℝ) + 1) ^ (-α))]
  have hint : ∑ j ∈ Finset.range N, ((j : ℝ) + 1) ^ (-α) ≤ (N : ℝ) ^ (1 - α) / (1 - α) := by
    have hanti : AntitoneOn (fun t : ℝ => t ^ (-α)) (Ioc 0 (0 + (N : ℝ))) := by
      intro a ha b hb hab
      simp only
      rw [Real.rpow_neg ha.1.le, Real.rpow_neg hb.1.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos ha.1 _) (Real.rpow_le_rpow ha.1.le hab hα0.le)
    have hii : IntegrableOn (fun t : ℝ => t ^ (-α)) (Icc 0 (0 + (N : ℝ))) := by
      rw [zero_add]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hNr.le).1
        (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := (N : ℝ)) (by linarith : -1 < -α))
    have := hanti.sum_le_integral_of_integrableOn hii
    simp only [zero_add] at this
    rw [integral_rpow (Or.inl (by linarith))] at this
    have e : (-α + 1) = 1 - α := by ring
    rw [e, Real.zero_rpow (by linarith), sub_zero] at this
    push_cast at this
    exact this
  have hmul : (B : ℝ)⁻¹ * ∑ j : Fin N, (1 / plSpec α c N i) * plSpec α c N j /
      (1 + (1 / plSpec α c N i) * plSpec α c N j) ≤
      (B : ℝ)⁻¹ * (rowNum i ^ α * ((N : ℝ) ^ (1 - α) / (1 - α))) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left hint (Real.rpow_nonneg hi.le _)
  refine hmul.trans (le_of_eq ?_)
  unfold gammaOf
  rw [Real.div_rpow hi.le hNr.le, Real.rpow_sub hNr, Real.rpow_one]
  have : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
  field_simp


private lemma pg6_mN_one {c : ℝ} (hc : 0 < c) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    partMN B (plSpec 1 c N) (1 / plSpec 1 c N i) ≤
      gammaOf N B * (rowNum i / (N : ℝ)) * (1 + Real.log ((N : ℝ) / rowNum i)) := by
  have hi := pg6_rowNum_pos i
  have hiN := pg6_rowNum_le i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  unfold partMN
  have hterm : ∀ j : Fin N, (1 / plSpec 1 c N i) * plSpec 1 c N j /
      (1 + (1 / plSpec 1 c N i) * plSpec 1 c N j) ≤ rowNum i * (rowNum i + ((j : ℕ) + 1 : ℝ))⁻¹ := by
    intro j
    rw [pg6_term_eq hc, Real.rpow_one]
    have hj := pg6_rowNum_pos j
    change rowNum i / rowNum j / (1 + rowNum i / rowNum j) ≤ rowNum i * (rowNum i + rowNum j)⁻¹
    apply le_of_eq
    field_simp
    ring
  have hsum : ∑ j : Fin N, (1 / plSpec 1 c N i) * plSpec 1 c N j /
      (1 + (1 / plSpec 1 c N i) * plSpec 1 c N j) ≤
      rowNum i * ∑ j ∈ Finset.range N, (rowNum i + ((j : ℝ) + 1))⁻¹ := by
    calc _ ≤ ∑ j : Fin N, rowNum i * (rowNum i + ((j : ℕ) + 1 : ℝ))⁻¹ :=
          Finset.sum_le_sum (fun j _ => hterm j)
      _ = rowNum i * ∑ j : Fin N, (rowNum i + ((j : ℕ) + 1 : ℝ))⁻¹ := by rw [Finset.mul_sum]
      _ = _ := by rw [pg6_sum_range_fin (fun j : ℕ => (rowNum i + ((j : ℝ) + 1))⁻¹)]
  have hint : ∑ j ∈ Finset.range N, (rowNum i + ((j : ℝ) + 1))⁻¹ ≤
      Real.log (((N : ℝ) + rowNum i) / rowNum i) := by
    have hanti : AntitoneOn (fun t : ℝ => (rowNum i + t)⁻¹) (Ioc 0 (0 + (N : ℝ))) := by
      intro a ha b hb hab
      simp only
      exact inv_anti₀ (by linarith [ha.1]) (by linarith)
    have hii : IntegrableOn (fun t : ℝ => (rowNum i + t)⁻¹) (Icc 0 (0 + (N : ℝ))) := by
      rw [zero_add]
      apply ContinuousOn.integrableOn_Icc
      apply ContinuousOn.inv₀ (continuousOn_const.add continuousOn_id)
      intro t ht
      have := ht.1
      exact (by linarith : 0 < rowNum i + t).ne'
    have := hanti.sum_le_integral_of_integrableOn hii
    simp only [zero_add] at this
    have hI : ∫ x in (0 : ℝ)..(N : ℝ), (rowNum i + x)⁻¹ = Real.log (((N : ℝ) + rowNum i) / rowNum i) := by
      have := intervalIntegral.integral_comp_add_left (fun x : ℝ => x⁻¹) (a := 0) (b := (N : ℝ))
        (rowNum i)
      simp only [add_zero] at this
      rw [this, integral_inv_of_pos hi (by linarith)]
      rw [add_comm]
    rw [hI] at this
    push_cast at this
    exact this
  have hlog : Real.log (((N : ℝ) + rowNum i) / rowNum i) ≤ 1 + Real.log ((N : ℝ) / rowNum i) := by
    have h1 : 1 ≤ (N : ℝ) / rowNum i := (one_le_div hi).2 hiN
    have h2 : ((N : ℝ) + rowNum i) / rowNum i ≤ 2 * ((N : ℝ) / rowNum i) := by
      rw [add_div, two_mul]
      have : rowNum i / rowNum i = 1 := div_self hi.ne'
      linarith
    have h3 : 0 < ((N : ℝ) + rowNum i) / rowNum i := by positivity
    calc _ ≤ Real.log (2 * ((N : ℝ) / rowNum i)) := Real.log_le_log h3 h2
      _ = Real.log 2 + Real.log ((N : ℝ) / rowNum i) := Real.log_mul (by norm_num) (by linarith)
      _ ≤ 1 + _ := by
          have := Real.log_two_lt_d9
          linarith
  have hmul : (B : ℝ)⁻¹ * ∑ j : Fin N, (1 / plSpec 1 c N i) * plSpec 1 c N j /
      (1 + (1 / plSpec 1 c N i) * plSpec 1 c N j) ≤
      (B : ℝ)⁻¹ * (rowNum i * (1 + Real.log ((N : ℝ) / rowNum i))) := by
    refine mul_le_mul_of_nonneg_left (hsum.trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_left (hint.trans hlog) hi.le
  refine hmul.trans (le_of_eq ?_)
  unfold gammaOf
  field_simp


private lemma pg6_cutW_sq {α β c : ℝ} (hc : 0 < c) (hβ0 : 0 < β) (hβ1 : β < 1) {N B : ℕ}
    (hN : 0 < N) (hB : 0 < B) (i : Fin N) :
    0 ≤ cutW β α c N B i ∧
    cutW β α c N B i ^ 2 = (rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * sPow β 2) := by
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have ha := pg6_aN_pos (α := α) hc hN
  have hγ := pg6_gamma_pos hB hN
  have hx : 0 < rowNum i / (N : ℝ) := div_pos (pg6_rowNum_pos i) (by exact_mod_cast hN)
  have e : cutW β α c N B i = Real.sqrt ((rowNum i / (N : ℝ)) ^ (-α) / (gammaOf N B * sPow β 2)) := by
    unfold cutW
    rw [pg6_H_eq hc hN hB i _ hs2]
    field_simp
  rw [e]
  refine ⟨Real.sqrt_nonneg _, Real.sq_sqrt ?_⟩
  have := Real.rpow_pos_of_pos hx (-α)
  positivity

private lemma pg6_mN_nonneg {α c : ℝ} (hc : 0 < c) {N B : ℕ} (hB : 0 < B) (i : Fin N) :
    0 ≤ partMN B (plSpec α c N) (1 / plSpec α c N i) := by
  unfold partMN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  refine mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => ?_))
  have := pg6_plSpec_pos (α := α) hc i
  have := pg6_plSpec_pos (α := α) hc j
  positivity

/-- `m_N(1/μ_i) → 0` for `α < 1` when `W → ∞`. -/
private lemma pg6_hrow_lt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α < 1) (i : (n : ℕ) → Fin (N n))
    (hW : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n)) atTop atTop) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      atTop (𝓝 0) := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have h1a : 0 < 1 - α := by linarith
  have hU : Tendsto (fun n => (1 / (1 - α)) * (1 / (sPow β 2 * cutW β α (c n) (N n) (B n) (i n) ^ 2)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hW
    have h2 : Tendsto (fun n => sPow β 2 * cutW β α (c n) (N n) (B n) (i n) ^ 2) atTop atTop :=
      h1.const_mul_atTop hs2
    have h3 := (tendsto_const_nhds (x := (1:ℝ))).div_atTop h2
    simpa using h3.const_mul (1 / (1 - α))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hU
    (fun n => pg6_mN_nonneg (hreg.hcpos n) (hreg.hBpos n) (i n)) (fun n => ?_)
  refine (pg6_mN_lt hreg.hα hα1 (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)).trans ?_
  obtain ⟨-, hsq⟩ := pg6_cutW_sq (α := α) (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n)
    (hreg.hBpos n) (i n)
  have hx : 0 < rowNum (i n) / (N n : ℝ) :=
    div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n)
  have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
  apply le_of_eq
  rw [hsq, Real.rpow_neg hx.le]
  have : 0 < (rowNum (i n) / (N n : ℝ)) ^ α := Real.rpow_pos_of_pos hx _
  field_simp


/-- `m_N(1/μ_i) → 0` for `α = 1` when `W ≥ κ (log γ)^{3/2}`. -/
private lemma pg6_hrow_one {β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime 1 β N B c) (i : (n : ℕ) → Fin (N n))
    {κ : ℝ} (hκ : 0 < κ)
    (hW : ∀ᶠ n in atTop, κ * Real.log (gammaOf (N n) (B n)) ^ ((3 : ℝ) / 2) ≤
      cutW β 1 (c n) (N n) (B n) (i n)) :
    Tendsto (fun n => partMN (B n) (plSpec 1 (c n) (N n)) (1 / plSpec 1 (c n) (N n) (i n)))
      atTop (𝓝 0) := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have hLg : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hreg.hγ
  set C : ℝ := |Real.log (sPow β 2)| with hC
  have hC0 : 0 ≤ C := abs_nonneg _
  have hLg3 : Tendsto (fun n => κ * Real.log (gammaOf (N n) (B n)) ^ ((3 : ℝ) / 2)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 3 / 2)).comp hLg).const_mul_atTop hκ
  have hWtop : Tendsto (fun n => cutW β 1 (c n) (N n) (B n) (i n)) atTop atTop :=
    tendsto_atTop_mono' _ hW hLg3
  have hV : Tendsto (fun n => 2 / (sPow β 2 * κ ^ 2 * Real.log (gammaOf (N n) (B n)) ^ 2) +
      2 / (sPow β 2 * cutW β 1 (c n) (N n) (B n) (i n))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => sPow β 2 * κ ^ 2 * Real.log (gammaOf (N n) (B n)) ^ 2) atTop atTop :=
      ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hLg).const_mul_atTop (by positivity)
    have h2 : Tendsto (fun n => sPow β 2 * cutW β 1 (c n) (N n) (B n) (i n)) atTop atTop :=
      hWtop.const_mul_atTop hs2
    have := ((tendsto_const_nhds (x := (2:ℝ))).div_atTop h1).add
      ((tendsto_const_nhds (x := (2:ℝ))).div_atTop h2)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hV
    (Eventually.of_forall (fun n => pg6_mN_nonneg (hreg.hcpos n) (hreg.hBpos n) (i n))) ?_
  filter_upwards [hW, hLg.eventually_ge_atTop (2 + C), hWtop.eventually_ge_atTop 1] with n h1 h2 h3
  refine (pg6_mN_one (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n)).trans ?_
  obtain ⟨hW0, hsq⟩ := pg6_cutW_sq (α := 1) (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n)
    (hreg.hBpos n) (i n)
  set W := cutW β 1 (c n) (N n) (B n) (i n) with hWdef
  set Lg := Real.log (gammaOf (N n) (B n)) with hLgdef
  have hx : 0 < rowNum (i n) / (N n : ℝ) :=
    div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n)
  have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
  have hWpos : 0 < W := by linarith
  rw [Real.rpow_neg_one] at hsq
  -- x⁻¹ = γ s2 W²
  have hxinv : (rowNum (i n) / (N n : ℝ))⁻¹ = gammaOf (N n) (B n) * sPow β 2 * W ^ 2 := by
    rw [hsq]; field_simp
  have hNr : (N n : ℝ) / rowNum (i n) = gammaOf (N n) (B n) * sPow β 2 * W ^ 2 := by
    rw [← hxinv, inv_div]
  have hγx : gammaOf (N n) (B n) * (rowNum (i n) / (N n : ℝ)) = 1 / (sPow β 2 * W ^ 2) := by
    have : rowNum (i n) / (N n : ℝ) = (gammaOf (N n) (B n) * sPow β 2 * W ^ 2)⁻¹ := by
      rw [← hxinv, inv_inv]
    rw [this]; field_simp
  rw [hγx, hNr]
  have hlog : Real.log (gammaOf (N n) (B n) * sPow β 2 * W ^ 2) =
      Lg + Real.log (sPow β 2) + 2 * Real.log W := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul hγ.ne' hs2.ne',
      Real.log_pow]
    push_cast; ring
  rw [hlog]
  have hlW : Real.log W ≤ W := (Real.log_le_sub_one_of_pos hWpos).trans (by linarith)
  have hlC : Real.log (sPow β 2) ≤ C := le_abs_self _
  have hWsq : κ ^ 2 * Lg ^ 3 ≤ W ^ 2 := by
    have h0 : 0 ≤ κ * Lg ^ ((3 : ℝ) / 2) := by
      have : 0 ≤ Lg := by linarith
      positivity
    have := pow_le_pow_left₀ h0 h1 2
    have e0 : (Lg ^ ((3 : ℝ) / 2)) ^ 2 = Lg ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
      norm_num
    have e : (κ * Lg ^ ((3 : ℝ) / 2)) ^ 2 = κ ^ 2 * Lg ^ 3 := by
      rw [mul_pow, e0]
    rwa [e] at this
  have hs2W : 0 < sPow β 2 * W ^ 2 := by positivity
  -- 1/(s2 W²) * (1 + (Lg + log s2 + 2 log W)) ≤ 2/(s2 κ² Lg²) + 2/(s2 W)
  have hLgpos : 0 < Lg := by linarith
  have key : 1 / (sPow β 2 * W ^ 2) * (1 + (Lg + Real.log (sPow β 2) + 2 * Real.log W)) ≤
      (1 + Lg + C) / (sPow β 2 * W ^ 2) + 2 / (sPow β 2 * W) := by
    have : 1 + (Lg + Real.log (sPow β 2) + 2 * Real.log W) ≤ (1 + Lg + C) + 2 * W := by linarith
    calc 1 / (sPow β 2 * W ^ 2) * (1 + (Lg + Real.log (sPow β 2) + 2 * Real.log W))
        ≤ 1 / (sPow β 2 * W ^ 2) * ((1 + Lg + C) + 2 * W) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = (1 + Lg + C) / (sPow β 2 * W ^ 2) + 2 / (sPow β 2 * W) := by
          field_simp
  refine key.trans ?_
  have h4 : (1 + Lg + C) / (sPow β 2 * W ^ 2) ≤ 2 / (sPow β 2 * κ ^ 2 * Lg ^ 2) := by
    rw [div_le_div_iff₀ hs2W (by positivity)]
    have h5 : 1 + Lg + C ≤ 2 * Lg := by linarith
    have h6 : sPow β 2 * (κ ^ 2 * Lg ^ 3) ≤ sPow β 2 * W ^ 2 :=
      mul_le_mul_of_nonneg_left hWsq hs2.le
    nlinarith [mul_pos hs2 (pow_pos hκ 2), pow_pos hLgpos 2, pow_pos hLgpos 3]
  linarith


/-! #### Inputs for `pg6_combine` -/

/-- Head negligible against `T`. -/
private lemma pg6_hhead_small {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (H T : ℕ → ℝ) (hHdef : ∀ n, H n = Real.sqrt (plSpec α (c n) (N n) (i n) /
      (gammaOf (N n) (B n) * sPow β 2))) (hH : ∀ n, 0 < H n) (hT : ∀ n, 0 ≤ T n)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop, H n ≤ δ * T n) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M - H n| ≤ ε * (H n + T n) := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  intro M hM ε hε
  obtain ⟨Ch, hCh⟩ := lem_app_pl_head_i (α := α) (β := β) M hM
  set K : ℝ := |Ch| * Real.sqrt (sPow β 2) + 1 with hK
  have hKpos : 0 < K := by positivity
  filter_upwards [hCh N B c hreg, hsmall (ε / K) (by positivity), hreg.hγ.eventually_ge_atTop M]
    with n h1 h2 h3
  have hpn := pg6_piece_nonneg (plSpec α (c n) (N n)) hreg.hβ0 hreg.hβ1 (hreg.hBpos n)
    (hreg.hNpos n) (pg6_plSpec_anti hreg.hα (hreg.hcpos n))
    (fun j => pg6_plSpec_pos (hreg.hcpos n) j) (i n) (le_refl (0:ℝ)) h3
  have h1' := h1 (i n)
  have hsq : Real.sqrt (plSpec α (c n) (N n) (i n) / gammaOf (N n) (B n)) =
      Real.sqrt (sPow β 2) * H n := by
    rw [hHdef n, ← Real.sqrt_mul hs2.le]
    congr 1
    field_simp
  rw [hsq] at h1'
  have hHn := hH n
  have hTn := hT n
  have hbound : sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M ≤
      |Ch| * Real.sqrt (sPow β 2) * H n := by
    calc _ ≤ Ch * (Real.sqrt (sPow β 2) * H n) := h1'
      _ ≤ |Ch| * (Real.sqrt (sPow β 2) * H n) :=
          mul_le_mul_of_nonneg_right (le_abs_self Ch) (by positivity)
      _ = _ := by ring
  have hKH : K * H n ≤ ε * T n := by
    calc K * H n ≤ K * (ε / K * T n) := mul_le_mul_of_nonneg_left h2 hKpos.le
      _ = ε * T n := by field_simp
  rw [abs_le]
  constructor
  · nlinarith [mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2)), hHn, hT n,
      mul_nonneg (mul_nonneg (abs_nonneg Ch) (Real.sqrt_nonneg (sPow β 2))) hHn.le]
  · nlinarith

/-- Head asymptotic to `H`. -/
private lemma pg6_hhead_exact {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (H T : ℕ → ℝ) (hHdef : ∀ n, H n = Real.sqrt (plSpec α (c n) (N n) (i n) /
      (gammaOf (N n) (B n) * sPow β 2))) (hH : ∀ n, 0 < H n) (hT : ∀ n, 0 ≤ T n)
    (hrow : Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n))
      (1 / plSpec α (c n) (N n) (i n))) atTop (𝓝 0)) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M - H n| ≤ ε * (H n + T n) := by
  intro M hM ε hε
  have h := lem_app_pl_head_ii hreg M hM i hrow
  have h' := h.isLittleO
  rw [isLittleO_iff] at h'
  filter_upwards [h' hε] with n hn
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hn
  rw [← hHdef n] at hn
  rw [abs_of_pos (hH n)] at hn
  nlinarith [hT n, hH n]

/-- Tail: `psiRes ∼ Ψ`. -/
private lemma pg6_hA_exact {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (H T : ℕ → ℝ) (hH : ∀ n, 0 < H n)
    (hTdef : ∀ n, T n = aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
    (hΨ : ∀ n, 0 < profPsi α (rowNum (i n) / (N n : ℝ)))
    (hequiv : ∀ M : ℝ, 0 < M → IsEquivalent atTop
      (fun n => psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)))
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) - T n|
        ≤ ε * (H n + T n) := by
  intro M hM ε hε
  have h' := (hequiv M hM).isLittleO
  rw [isLittleO_iff] at h'
  filter_upwards [h' hε] with n hn
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hn
  rw [abs_of_pos (hΨ n)] at hn
  have ha := pg6_aN_pos (α := α) (hreg.hcpos n) (hreg.hNpos n)
  have e : aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) - T n =
      aN α (c n) (N n) * (psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
        profPsi α (rowNum (i n) / (N n : ℝ))) := by rw [hTdef n]; ring
  rw [e, abs_mul, abs_of_pos ha]
  have hT := hTdef n
  have hHn := hH n
  have : aN α (c n) (N n) * (ε * profPsi α (rowNum (i n) / (N n : ℝ))) = ε * T n := by
    rw [hT]; ring
  calc _ ≤ aN α (c n) (N n) * (ε * profPsi α (rowNum (i n) / (N n : ℝ))) :=
        mul_le_mul_of_nonneg_left hn ha.le
    _ = ε * T n := this
    _ ≤ ε * (H n + T n) := by
        have : 0 ≤ T n := by rw [hT]; exact mul_nonneg ha.le (hΨ n).le
        nlinarith


private lemma pg6_psiRes_nonneg {α : ℝ} (hα : 0 < α) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1) {x : ℝ}
    (hx : 0 < x) : 0 ≤ psiRes α η x := by
  unfold psiRes
  have hc0 : 0 ≤ c0 := by unfold c0; positivity
  refine mul_nonneg hc0 (intervalIntegral.integral_nonneg hη1 (fun p hp => ?_))
  rcases hp.2.eq_or_lt with h | h
  · simp only [h, sub_self, zero_div, Real.sqrt_zero, zero_mul, le_refl]
  · have hV := pg6_contV_pos hα ⟨lt_of_lt_of_le hη0 hp.1, h⟩
    simp only [profF]
    have : 0 < x ^ α := Real.rpow_pos_of_pos hx _
    positivity

/-- Tail negligible against the head `H = a_N W`. -/
private lemma pg6_hA_small {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (H T : ℕ → ℝ) (W : ℕ → ℝ) (hH : ∀ n, 0 < H n) (hHW : ∀ n, H n = aN α (c n) (N n) * W n)
    (hTdef : ∀ n, T n = aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
    (hΨ : ∀ n, 0 < profPsi α (rowNum (i n) / (N n : ℝ)))
    (hlo : ∀ M : ℝ, 0 < M → IsLittleO atTop
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) +
        psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ))) W) :
    ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) - T n|
        ≤ ε * (H n + T n) := by
  intro M hM ε hε
  have h' := (hlo M hM)
  rw [isLittleO_iff] at h'
  filter_upwards [h' hε, hreg.hγ.eventually_ge_atTop M, hreg.hγ.eventually_gt_atTop 0] with n hn h3 h4
  have ha := pg6_aN_pos (α := α) (hreg.hcpos n) (hreg.hNpos n)
  have hx : 0 < rowNum (i n) / (N n : ℝ) :=
    div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n)
  have hγ : 0 < gammaOf (N n) (B n) := h4
  have hη0 : 0 < M / gammaOf (N n) (B n) := by positivity
  have hη1 : M / gammaOf (N n) (B n) ≤ 1 := by
    rw [div_le_one hγ]; exact h3
  have hψ := pg6_psiRes_nonneg hreg.hα hη0 hη1 hx
  have hΨn := hΨ n
  have hHn := hH n
  have hHW' := hHW n
  have hT := hTdef n
  have hWpos : 0 < W n := by
    rcases (lt_or_ge 0 (W n)) with h | h
    · exact h
    · exfalso
      have : H n ≤ 0 := by rw [hHW']; exact mul_nonpos_of_nonneg_of_nonpos ha.le h
      linarith
  simp only [Real.norm_eq_abs] at hn
  rw [abs_of_pos (add_pos_of_pos_of_nonneg hΨn hψ), abs_of_pos hWpos] at hn
  have e : aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) - T n =
      aN α (c n) (N n) * (psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
        profPsi α (rowNum (i n) / (N n : ℝ))) := by rw [hT]; ring
  rw [e, abs_mul, abs_of_pos ha]
  have h5 : |psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
      profPsi α (rowNum (i n) / (N n : ℝ))| ≤ ε * W n := by
    rw [abs_le]; constructor <;> nlinarith
  have hT0 : 0 ≤ T n := by rw [hT]; exact mul_nonneg ha.le hΨn.le
  calc _ ≤ aN α (c n) (N n) * (ε * W n) := mul_le_mul_of_nonneg_left h5 ha.le
    _ = ε * H n := by rw [hHW']; ring
    _ ≤ ε * (H n + T n) := by nlinarith


private lemma pg6_hrow {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    {κ : ℝ} (hκ : 0 < κ)
    (hW : ∀ᶠ n in atTop, κ * Real.log (gammaOf (N n) (B n)) ^ cutNu α ≤
      cutW β α (c n) (N n) (B n) (i n)) :
    Tendsto (fun n => partMN (B n) (plSpec α (c n) (N n)) (1 / plSpec α (c n) (N n) (i n)))
      atTop (𝓝 0) := by
  have hLg : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hreg.hγ
  rcases hα.lt_or_eq with hlt | heq
  · apply pg6_hrow_lt hreg hlt
    have hν : cutNu α = 1 := by unfold cutNu; rw [if_pos hlt]
    rw [hν] at hW
    have : Tendsto (fun n => κ * Real.log (gammaOf (N n) (B n)) ^ (1 : ℝ)) atTop atTop := by
      simp only [Real.rpow_one]
      exact hLg.const_mul_atTop hκ
    exact tendsto_atTop_mono' _ hW this
  · subst heq
    have hν : cutNu 1 = 3 / 2 := by unfold cutNu; rw [if_neg (lt_irrefl _)]
    rw [hν] at hW
    exact pg6_hrow_one hreg i hκ hW

/-- The regime with the amplitude set to one. -/
private lemma pg6_reg_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) :
    assum_app_pl_regime α β N B (fun _ => 1) :=
  ⟨hreg.hα, hreg.hβ0, hreg.hβ1, hreg.hNpos, hreg.hBpos, fun _ => one_pos, hreg.hN, hreg.hB,
    hreg.hγ⟩

private lemma pg6_cutW_c_indep {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n)) (n : ℕ) :
    cutW β α 1 (N n) (B n) (i n) = cutW β α (c n) (N n) (B n) (i n) := by
  rw [pg6_cutW_eq one_pos hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n),
    pg6_cutW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)]

/-- Assembly of `pg6_combine` for `H = a_N W`, `T = a_N Ψ`. -/
private lemma pg6_core_of {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n))
    (hhead : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |sqrt2DPiece β (B n) (plSpec α (c n) (N n)) (i n) 0 M -
        aN α (c n) (N n) * cutW β α (c n) (N n) (B n) (i n)| ≤
        ε * (aN α (c n) (N n) * cutW β α (c n) (N n) (B n) (i n) +
          aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))))
    (hA : ∀ M : ℝ, 0 < M → ∀ ε > 0, ∀ᶠ n in atTop,
      |aN α (c n) (N n) * psiRes α (M / gammaOf (N n) (B n)) (rowNum (i n) / (N n : ℝ)) -
        aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))| ≤
        ε * (aN α (c n) (N n) * cutW β α (c n) (N n) (B n) (i n) +
          aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  have hΨ : ∀ n, 0 < profPsi α (rowNum (i n) / (N n : ℝ)) := fun n =>
    lem_app_pl_Psi_i_pos hreg.hα _ ⟨div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n),
      (div_le_one (by exact_mod_cast hreg.hNpos n)).2 (pg6_rowNum_le _)⟩
  have han : ∀ n, 0 < aN α (c n) (N n) := fun n => pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n)
  have hcomb := pg6_combine hreg i (fun n => aN α (c n) (N n) * cutW β α (c n) (N n) (B n) (i n))
    (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
    (fun n => mul_pos (han n) (pg6_cutW_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n)
      (hreg.hBpos n) (i n)))
    (fun n => (mul_pos (han n) (hΨ n)).le) hhead hA
  exact hcomb.congr_right (Eventually.of_forall (fun n => by ring))


/-! #### The regimes `x → 0` for `α ≤ 1` -/

private lemma pg6_pos_facts {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n)) :
    (∀ n, 0 < profPsi α (rowNum (i n) / (N n : ℝ))) ∧ (∀ n, 0 < aN α (c n) (N n)) ∧
    (∀ n, 0 < cutW β α (c n) (N n) (B n) (i n)) := by
  refine ⟨fun n => lem_app_pl_Psi_i_pos hreg.hα _ ⟨div_pos (pg6_rowNum_pos _)
    (by exact_mod_cast hreg.hNpos n),
      (div_le_one (by exact_mod_cast hreg.hNpos n)).2 (pg6_rowNum_le _)⟩,
    fun n => pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n),
    fun n => pg6_cutW_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)⟩

private lemma pg6_core_Z0 {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hreg1 := pg6_reg_one hreg
  have h1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 0) :=
    h.congr (fun n => by simp only [pg6_cutW_c_indep hreg i n])
  obtain ⟨⟨C1, hC1⟩, hlo⟩ := (lem_app_pl_cutoff_iii hreg1 hα1 (fun _ => rfl) i hi hx).2 h1
  have hA1 := (lem_app_pl_cutoff_iii hreg1 hα1 (fun _ => rfl) i hi hx).1
  have hlo' : IsLittleO atTop (fun n => cutW β α (c n) (N n) (B n) (i n))
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ))) :=
    hlo.congr (fun n => pg6_cutW_c_indep hreg i n) (fun n => rfl)
  have hsmall : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      aN α (c n) (N n) * cutW β α (c n) (N n) (B n) (i n) ≤
        δ * (aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) := by
    intro δ hδ
    rw [isLittleO_iff] at hlo'
    filter_upwards [hlo' hδ] with n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (hWp n), abs_of_pos (hΨ n)] at hn
    nlinarith [han n]
  apply pg6_core_of hreg i
  · exact pg6_hhead_small hreg i _ _ (fun n => (pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1
      (hreg.hNpos n) (hreg.hBpos n) (i n))) (fun n => mul_pos (han n) (hWp n))
      (fun n => (mul_pos (han n) (hΨ n)).le) hsmall
  · exact pg6_hA_exact hreg i _ _ (fun n => mul_pos (han n) (hWp n)) (fun n => rfl) hΨ
      (fun M hM => hA1 M hM C1 hC1)


private lemma pg6_Lgnu_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) :
    ∀ᶠ n in atTop, 0 < Real.log (gammaOf (N n) (B n)) ^ cutNu α := by
  have hLg : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hreg.hγ
  filter_upwards [hLg.eventually_gt_atTop 0] with n hn
  exact Real.rpow_pos_of_pos hn _

private lemma pg6_core_Zpos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) {z : ℝ} (hz : 0 < z)
    (h : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 z)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hreg1 := pg6_reg_one hreg
  have h1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 z) :=
    h.congr (fun n => by simp only [pg6_cutW_c_indep hreg i n])
  have hWge : ∀ᶠ n in atTop, (z / 2) * Real.log (gammaOf (N n) (B n)) ^ cutNu α ≤
      cutW β α (c n) (N n) (B n) (i n) := by
    filter_upwards [h.eventually (eventually_ge_nhds (show z / 2 < z by linarith)),
      pg6_Lgnu_pos hreg] with n hn hL
    rw [le_div_iff₀ hL] at hn
    exact hn
  have hrow := pg6_hrow hreg hα1 i (by linarith : 0 < z / 2) hWge
  apply pg6_core_of hreg i
  · exact pg6_hhead_exact hreg i _ _ (fun n => (pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1
      (hreg.hNpos n) (hreg.hBpos n) (i n))) (fun n => mul_pos (han n) (hWp n))
      (fun n => (mul_pos (han n) (hΨ n)).le) hrow
  · exact pg6_hA_exact hreg i _ _ (fun n => mul_pos (han n) (hWp n)) (fun n => rfl) hΨ
      (fun M hM => ((lem_app_pl_cutoff_i hreg1 hα1 (fun _ => rfl) i hi hx M hM z hz h1).1).trans
        ((lem_app_pl_cutoff_i hreg1 hα1 (fun _ => rfl) i hi hx M hM z hz h1).2).symm)

private lemma pg6_core_Zinf {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hreg1 := pg6_reg_one hreg
  have h1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop :=
    h.congr (fun n => by simp only [pg6_cutW_c_indep hreg i n])
  have hWge : ∀ᶠ n in atTop, 1 * Real.log (gammaOf (N n) (B n)) ^ cutNu α ≤
      cutW β α (c n) (N n) (B n) (i n) := by
    filter_upwards [h.eventually_ge_atTop 1, pg6_Lgnu_pos hreg] with n hn hL
    rw [le_div_iff₀ hL] at hn
    exact hn
  have hrow := pg6_hrow hreg hα1 i one_pos hWge
  apply pg6_core_of hreg i
  · exact pg6_hhead_exact hreg i _ _ (fun n => (pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1
      (hreg.hNpos n) (hreg.hBpos n) (i n))) (fun n => mul_pos (han n) (hWp n))
      (fun n => (mul_pos (han n) (hΨ n)).le) hrow
  · exact pg6_hA_small hreg i _ _ _ (fun n => mul_pos (han n) (hWp n)) (fun n => rfl) (fun n => rfl) hΨ
      (fun M hM => (lem_app_pl_cutoff_ii hreg1 hα1 (fun _ => rfl) i hi hx M hM h1).congr
        (fun n => rfl) (fun n => pg6_cutW_c_indep hreg i n))


private lemma pg6_trichotomy (r : ℕ → ℝ) (hr : ∀ n, 0 ≤ r n) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧ (Tendsto (fun n => r (ψ n)) atTop (𝓝 0) ∨
      (∃ z : ℝ, 0 < z ∧ Tendsto (fun n => r (ψ n)) atTop (𝓝 z)) ∨
      Tendsto (fun n => r (ψ n)) atTop atTop) := by
  obtain ⟨a, ψ, hψ, ha⟩ := CompactSpace.tendsto_subseq (fun n => ENNReal.ofReal (r n))
  refine ⟨ψ, hψ, ?_⟩
  by_cases htop : a = ⊤
  · right; right
    rw [tendsto_atTop]
    intro b
    have h1 : ENNReal.ofReal (max b 0) < a := by rw [htop]; exact ENNReal.ofReal_lt_top
    filter_upwards [ha.eventually (lt_mem_nhds h1)] with n hn
    have := (ENNReal.ofReal_lt_ofReal_iff' ).1 hn
    exact (le_max_left b 0).trans this.1.le
  · have h1 : Tendsto (fun n => r (ψ n)) atTop (𝓝 a.toReal) := by
      have := (ENNReal.tendsto_toReal htop).comp ha
      refine this.congr (fun n => ?_)
      simp [Function.comp, ENNReal.toReal_ofReal (hr _)]
    rcases (ENNReal.toReal_nonneg (a := a)).eq_or_lt with h0 | h0
    · left; rw [← h0] at h1; exact h1
    · right; left; exact ⟨a.toReal, h0, h1⟩


private lemma pg6_core_small {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  apply pg6_equiv_subseq
  · intro n; exact mul_pos (han n) (add_pos (hWp n) (hΨ n))
  intro φ hφ
  set r : ℕ → ℝ := fun n => cutW β α (c n) (N n) (B n) (i n) /
    Real.log (gammaOf (N n) (B n)) ^ cutNu α with hr
  have hrev : ∀ᶠ m in atTop, 0 ≤ r m := by
    filter_upwards [pg6_Lgnu_pos hreg] with m hm
    exact div_nonneg (hWp m).le hm.le
  obtain ⟨ψ, hψ, hcases⟩ := pg6_trichotomy (fun n => max (r (φ n)) 0) (fun n => le_max_right _ _)
  have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ.tendsto_atTop, ?_⟩
  have hreg' := pg6_reg_comp hreg hθ
  have hi' : Tendsto (fun n => rowNum (i (φ (ψ n)))) atTop atTop := hi.comp hθ
  have hx' : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) := hx.comp hθ
  have hev : ∀ᶠ n in atTop, max (r (φ (ψ n))) 0 = r (φ (ψ n)) := by
    filter_upwards [hθ.eventually hrev] with n hn
    exact max_eq_left hn
  rcases hcases with h | ⟨z, hz, h⟩ | h
  · exact pg6_core_Z0 hreg' hα1 _ hi' hx' (h.congr' hev)
  · exact pg6_core_Zpos hreg' hα1 _ hi' hx' hz (h.congr' hev)
  · exact pg6_core_Zinf hreg' hα1 _ hi' hx' (h.congr' hev)

private lemma pg6_core_le {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
        profPsi α (rowNum (i n) / (N n : ℝ)))) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hxu : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Icc (0 : ℝ) 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨(div_pos (pg6_rowNum_pos _) this).le, (div_le_one this).2 (pg6_rowNum_le _)⟩
  apply pg6_equiv_subseq
  · intro n; exact mul_pos (han n) (add_pos (hWp n) (hΨ n))
  intro φ hφ
  obtain ⟨x0, hx0, ψ, hψ, hxψ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => rowNum (i (φ n)) / (N (φ n) : ℝ)) (fun n => hxu (φ n))
  have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ.tendsto_atTop, ?_⟩
  have hreg' := pg6_reg_comp hreg hθ
  have hi' : Tendsto (fun n => rowNum (i (φ (ψ n)))) atTop atTop := hi.comp hθ
  rcases hx0.1.eq_or_lt with h0 | h0
  · have hx : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) := by
      rw [h0]; exact hxψ
    exact pg6_core_small hreg' hα1 (fun n => i (φ (ψ n))) hi' hx
  · exact (pg6_bulk hreg' (fun n => i (φ (ψ n))) (x0 := x0 / 2) (by linarith)
      (hxψ.eventually (eventually_ge_nhds (show x0 / 2 < x0 by linarith)))).2


/-! #### The uniform statement from a sequential one -/

/-- If every row sequence tending to infinity has `D ∼ v` with `v` the approximant, then the
ratio tends to one uniformly over `i ≥ n_N`. -/
private lemma pg6_uniform {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (nN : ℕ → ℕ)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop)
    (Dn Vn : (n : ℕ) → Fin (N n) → ℝ)
    (hseq : ∀ {φ : ℕ → ℕ}, Tendsto φ atTop atTop →
      ∀ i : (n : ℕ) → Fin (N (φ n)),
        Tendsto (fun n => rowNum (i n)) atTop atTop →
        IsEquivalent atTop (fun n => Dn (φ n) (i n)) (fun n => Vn (φ n) (i n)))
    (hV : ∀ n i, 0 < Vn n i) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |Dn n i / Vn n i - 1| ≤ ε := by
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  have hfreq : ∃ᶠ n in atTop, ∃ i : Fin (N n), (nN n : ℝ) ≤ rowNum i ∧ ε < |Dn n i / Vn n i - 1| := by
    refine hcon.mono (fun n hn => ?_)
    push Not at hn
    obtain ⟨i, hi1, hi2⟩ := hn
    exact ⟨i, hi1, hi2⟩
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_of_frequently_atTop hfreq
  choose i hi1 hi2 using hP
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hrow : Tendsto (fun k => rowNum (i k)) atTop atTop :=
    tendsto_atTop_mono (fun k => hi1 k) (hn.comp hφt)
  have hE := hseq hφt i hrow
  have hlim := (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun k => (hV _ _).ne'))).1 hE
  have := hlim.eventually (Metric.closedBall_mem_nhds (1 : ℝ) hε)
  obtain ⟨k, hk⟩ := this.exists
  have h1 := hi2 k
  rw [Real.dist_eq] at hk
  simp only [Pi.div_apply] at hk
  linarith


private theorem pg6_triple_le {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (nN : ℕ → ℕ)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have hVdef : ∀ n (i : Fin (N n)), dHatSqrt2 α β (c n) (N n) (B n) i =
      aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) i + profPsi α (rowNum i / (N n : ℝ))) := by
    intro n i
    unfold dHatSqrt2
    rw [if_pos hα, mul_add, pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n)
      (hreg.hBpos n) i]
  have hVpos : ∀ n (i : Fin (N n)), 0 < dHatSqrt2 α β (c n) (N n) (B n) i := by
    intro n i
    rw [hVdef]
    exact mul_pos (pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n))
      (add_pos (pg6_cutW_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) i)
        (lem_app_pl_Psi_i_pos hreg.hα _ ⟨div_pos (pg6_rowNum_pos _)
          (by exact_mod_cast hreg.hNpos n),
          (div_le_one (by exact_mod_cast hreg.hNpos n)).2 (pg6_rowNum_le _)⟩))
  have key := pg6_uniform hreg nN hn
    (fun n i => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) i)
    (fun n i => dHatSqrt2 α β (c n) (N n) (B n) i) ?_ hVpos
  · intro ε hε
    filter_upwards [key ε hε] with n hn' i hi
    have h2 : 0 < Real.sqrt 2 := by positivity
    have e : dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i =
        Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) i /
          dHatSqrt2 α β (c n) (N n) (B n) i := by
      unfold dHatDrift
      field_simp
    rw [e]
    exact hn' i hi
  · intro φ hφ i hi
    have hreg' := pg6_reg_comp hreg hφ
    refine (pg6_core_le hreg' hα i hi).congr_right (Eventually.of_forall (fun k => ?_))
    exact (hVdef (φ k) (i k)).symm


/-! #### The case `α > 1` of the triple -/

private lemma pg6_den_pos {α : ℝ} (hα : 1 < α) {x : ℝ} (hx : 0 < x) :
    0 < dAl α * Real.sqrt (Kc α) * x ^ (-(α - 1) / 2) := by
  have := pg6_dAl_pos hα
  have := pg6_Kc_pos hα
  have : 0 < x ^ (-(α - 1) / 2) := Real.rpow_pos_of_pos hx _
  positivity


/-! ### P-G.6.P2 helpers (begin) -/

private lemma pg6p2_Phi_lower {α β : ℝ} (hα : 1 < α) (hβ0 : 0 < β) (hβ1 : β < 1) :
    ∃ g0 : ℝ, 0 < g0 ∧ ∀ y : ℝ, 0 < y → g0 * y ^ ((α - 1) / (2 * α)) ≤ profPhi α β y := by
  have hα0 : 0 < α := by linarith
  set p : ℝ := (α - 1) / (2 * α) with hp
  have hp0 : 0 < p := by rw [hp]; apply div_pos <;> linarith
  have hp1 : p ≤ 1 / 2 := by
    rw [hp, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  obtain ⟨hcont, hint⟩ := lem_app_pl_super_i hα hβ0 hβ1
  have hpos : ∀ y : ℝ, 0 < y → 0 < profPhi α β y := fun y hy => (hint y hy).2
  have hd := pg6_dAl_pos hα
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  -- small y
  have h3 := (lem_app_pl_super_iii hα hβ0 hβ1).isLittleO.def (show (0:ℝ) < 1 / 2 by norm_num)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 h3
  have hu0 : 0 < u := hu
  have hsmall : ∀ y ∈ Ioo (0:ℝ) u, dAl α / 2 * y ^ p ≤ profPhi α β y := by
    intro y hy
    have h := hsub hy
    simp only [mem_setOf_eq, Real.norm_eq_abs] at h
    have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy.1 _
    rw [abs_of_pos (mul_pos hd hyp)] at h
    have := (abs_le.1 (show |profPhi α β y - dAl α * y ^ p| ≤ 1 / 2 * (dAl α * y ^ p) from h)).1
    linarith
  -- large y
  have h2 := (lem_app_pl_super_ii hα hβ0 hβ1).isLittleO.def (show (0:ℝ) < 1 / 2 by norm_num)
  obtain ⟨R, hR⟩ := eventually_atTop.1 h2
  set R' : ℝ := max R 1 with hR'
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := by linarith
  have hlarge : ∀ y : ℝ, R' ≤ y → 1 / (2 * Real.sqrt (sPow β 2)) * y ^ p ≤ profPhi α β y := by
    intro y hy
    have hy1 : 1 ≤ y := hR'1.trans hy
    have hy0 : 0 < y := by linarith
    have h := hR y ((le_max_left _ _).trans hy)
    simp only [Real.norm_eq_abs, Pi.sub_apply] at h
    have hsq : 0 < Real.sqrt (y / sPow β 2) := Real.sqrt_pos.2 (by positivity)
    rw [abs_of_pos hsq] at h
    have h' := (abs_le.1 h).1
    have e : Real.sqrt (y / sPow β 2) = Real.sqrt y / Real.sqrt (sPow β 2) := Real.sqrt_div hy0.le _
    have e2 : y ^ p ≤ Real.sqrt y := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hy1 hp1
    have hss : 0 < Real.sqrt (sPow β 2) := Real.sqrt_pos.2 hs2
    have : 1 / (2 * Real.sqrt (sPow β 2)) * y ^ p ≤ 1 / 2 * (Real.sqrt y / Real.sqrt (sPow β 2)) := by
      rw [div_mul_eq_mul_div, one_mul, show 1 / 2 * (Real.sqrt y / Real.sqrt (sPow β 2)) =
        Real.sqrt y / (2 * Real.sqrt (sPow β 2)) by field_simp]
      exact div_le_div_of_nonneg_right e2 (by positivity)
    rw [e] at h'
    linarith
  -- middle
  obtain ⟨m, hm0, hm⟩ := pg6p2_min_pos (f := profPhi α β) (a := u / 2) (b := R')
    (hcont.mono (fun y hy => lt_of_lt_of_le (by linarith) hy.1))
    (fun y hy => hpos y (lt_of_lt_of_le (by linarith) hy.1))
  have hRp : 0 < R' ^ p := Real.rpow_pos_of_pos hR'0 _
  refine ⟨min (dAl α / 2) (min (1 / (2 * Real.sqrt (sPow β 2))) (m / R' ^ p)),
    lt_min (by positivity) (lt_min (by have := Real.sqrt_pos.2 hs2; positivity) (by positivity)),
    fun y hy => ?_⟩
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy _
  have hm1 := min_le_left (dAl α / 2) (min (1 / (2 * Real.sqrt (sPow β 2))) (m / R' ^ p))
  have hm2 := (min_le_right (dAl α / 2) (min (1 / (2 * Real.sqrt (sPow β 2))) (m / R' ^ p))).trans
    (min_le_left _ _)
  have hm3 := (min_le_right (dAl α / 2) (min (1 / (2 * Real.sqrt (sPow β 2))) (m / R' ^ p))).trans
    (min_le_right _ _)
  by_cases h1 : y < u
  · exact (mul_le_mul_of_nonneg_right hm1 hyp.le).trans (hsmall y ⟨hy, h1⟩)
  by_cases h2' : R' ≤ y
  · exact (mul_le_mul_of_nonneg_right hm2 hyp.le).trans (hlarge y h2')
  · push_neg at h1 h2'
    have hmy := hm y ⟨by linarith, h2'.le⟩
    have hyR : y ^ p ≤ R' ^ p := Real.rpow_le_rpow hy.le h2'.le hp0.le
    calc _ ≤ m / R' ^ p * y ^ p := mul_le_mul_of_nonneg_right hm3 hyp.le
      _ ≤ m / R' ^ p * R' ^ p := mul_le_mul_of_nonneg_left hyR (by positivity)
      _ = m := by field_simp
      _ ≤ _ := hmy


/-- The approximants are bounded below by $c\,a_N$, uniformly in the row: for
$\alpha\le1$ because $\Psi_\alpha\ge c$, and for $\alpha>1$ because $\Phi_{\alpha,\bmom}(y)/y^{p_\alpha}$ is
positive and continuous on $(0,\infty)$ with limits $d_\alpha$ at $0$ and $\infty$ at
$\infty$, so that $\sqrt2\,\widehat{\mathfrak d}_i\ge c\,b_Ny^{p_\alpha}\Psi_\alpha(x)/(d_\alpha\sqrt{K_\alpha}x^{-(\alpha-1)/2})=c\,a_N\Psi_\alpha(x)/d_\alpha$. -/
theorem approx_drift_lower {α β : ℝ} :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N B : ℕ → ℕ) (c : ℕ → ℝ), assum_app_pl_regime α β N B c →
      ∀ᶠ n in atTop, ∀ i : Fin (N n),
        κ * aN α (c n) (N n) ≤ dHatSqrt2 α β (c n) (N n) (B n) i := by
  by_cases hα1 : α ≤ 1
  · by_cases hα0 : 0 < α
    · obtain ⟨κ, hκ, hκle⟩ := lem_app_pl_Psi_i_lower hα0
      refine ⟨κ, hκ, fun N B c hreg => Eventually.of_forall (fun n i => ?_)⟩
      have han : 0 < aN α (c n) (N n) := pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n)
      have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
      unfold dHatSqrt2
      rw [if_pos hα1]
      have := hκle (rowNum i / (N n : ℝ)) ⟨div_pos (pg6_rowNum_pos _) hNr,
        (div_le_one hNr).2 (pg6_rowNum_le _)⟩
      nlinarith [Real.sqrt_nonneg (plSpec α (c n) (N n) i / (gammaOf (N n) (B n) * sPow β 2))]
    · refine ⟨1, one_pos, fun N B c hreg => absurd hreg.hα hα0⟩
  · push_neg at hα1
    have hα0 : 0 < α := by linarith
    obtain ⟨κ, hκ, hκle⟩ := lem_app_pl_Psi_i_lower hα0
    by_cases hβ : 0 < β ∧ β < 1
    · obtain ⟨g0, hg0, hg⟩ := pg6p2_Phi_lower hα1 hβ.1 hβ.2
      have hd := pg6_dAl_pos hα1
      refine ⟨g0 * κ / dAl α, by positivity, fun N B c hreg => Eventually.of_forall (fun n i => ?_)⟩
      have han : 0 < aN α (c n) (N n) := pg6_aN_pos (hreg.hcpos n) (hreg.hNpos n)
      have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
      have hr := pg6_rowNum_pos i
      have hic := pg6_icCross_pos hα1 (hreg.hBpos n)
      have hK := pg6_Kc_pos hα1
      have hx := hκle (rowNum i / (N n : ℝ)) ⟨div_pos hr hNr, (div_le_one hNr).2 (pg6_rowNum_le _)⟩
      have hy0 : 0 < (icCross α (B n) / rowNum i) ^ α := Real.rpow_pos_of_pos (div_pos hic hr) _
      have hΦ := hg _ hy0
      have hR := pg6_R_alg hα1 (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) i
      have hP := pg6_psiR_alg (α := α) (hreg.hcpos n) (hreg.hNpos n) i
      have hbN := (pg6_bN_pos hα1 (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n))
      have hX : 0 < (rowNum i / (N n : ℝ)) ^ (-(α - 1) / 2) :=
        Real.rpow_pos_of_pos (div_pos hr hNr) _
      have hsK := Real.sqrt_pos.2 hK
      unfold dHatSqrt2
      rw [if_neg (not_le.2 hα1)]
      set D := dAl α * Real.sqrt (Kc α) * (rowNum i / (N n : ℝ)) ^ (-(α - 1) / 2) with hD
      have hDpos : 0 < D := by positivity
      have hkey : bN α (c n) (N n) (B n) * ((icCross α (B n) / rowNum i) ^ α) ^ ((α - 1) / (2 * α))
          = aN α (c n) (N n) * D / dAl α := by
        rw [eq_div_iff hd.ne', hD]
        calc _ = bN α (c n) (N n) (B n) * (dAl α * ((icCross α (B n) / rowNum i) ^ α) ^ ((α - 1) / (2 * α))) := by ring
          _ = _ := by rw [hR, ← hP]
          _ = _ := by ring
      rw [le_div_iff₀ hDpos]
      have h1 : bN α (c n) (N n) (B n) * (g0 * ((icCross α (B n) / rowNum i) ^ α) ^ ((α - 1) / (2 * α)))
          ≤ bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum i) ^ α) :=
        mul_le_mul_of_nonneg_left hΦ hbN.le
      have h2 : bN α (c n) (N n) (B n) * (g0 * ((icCross α (B n) / rowNum i) ^ α) ^ ((α - 1) / (2 * α)))
          = g0 * (aN α (c n) (N n) * D / dAl α) := by rw [← hkey]; ring
      rw [h2] at h1
      have h3 : 0 ≤ g0 * (aN α (c n) (N n) * D / dAl α) := by positivity
      calc g0 * κ / dAl α * aN α (c n) (N n) * D = g0 * (aN α (c n) (N n) * D / dAl α) * κ := by
            field_simp
        _ ≤ bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum i) ^ α) *
            profPsi α (rowNum i / (N n : ℝ)) :=
          mul_le_mul h1 hx hκ.le (h3.trans h1)
    · exact ⟨1, one_pos, fun N B c hreg => absurd ⟨hreg.hβ0, hreg.hβ1⟩ hβ⟩


private lemma pg6_core_gt_zero {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => dHatSqrt2 α β (c n) (N n) (B n) (i n)) := by
  have hEq := lem_app_pl_super_iv hreg hα i hi hx
  have hx' : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hx, Eventually.of_forall (fun n =>
      div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n))⟩
  have hΨ := (lem_app_pl_Psi_ii_gt hα).comp_tendsto hx'
  have hΨ1 : Tendsto (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
      (dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2))) atTop (𝓝 1) := by
    have := (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun n =>
      (pg6_den_pos hα (div_pos (pg6_rowNum_pos (i n))
        (by exact_mod_cast hreg.hNpos n))).ne'))).1 hΨ
    exact this
  have hΨ2 : IsEquivalent atTop (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
      (dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2)))
      (fun _ => (1 : ℝ)) := (isEquivalent_const_iff_tendsto one_ne_zero).2 hΨ1
  have hbΦ : IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
    have h4 : IsEquivalent atTop (fun n => bN α (c n) (N n) (B n) *
        (Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) / bN α (c n) (N n) (B n)))
        (fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) :=
      (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n))).mul hEq
    refine h4.congr_left (Eventually.of_forall (fun n => ?_))
    have := (pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)).ne'
    simp only
    field_simp
  have hv : IsEquivalent atTop (fun n => dHatSqrt2 α β (c n) (N n) (B n) (i n))
      (fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) := by
    have h5 : IsEquivalent atTop
        ((fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) *
          (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
            (dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2))))
        ((fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) *
          (fun _ => (1 : ℝ))) :=
      (IsEquivalent.refl).mul hΨ2
    refine (h5.congr_left (Eventually.of_forall (fun n => ?_))).congr_right
      (Eventually.of_forall (fun n => ?_))
    · simp only [Pi.mul_apply]
      unfold dHatSqrt2
      rw [if_neg (not_le.2 hα)]
      ring
    · simp
  exact hbΦ.trans hv.symm


private lemma pg6_core_gt_pos {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) {x0 : ℝ} (hx0 : 0 < x0)
    (hxl : ∀ᶠ n in atTop, x0 ≤ rowNum (i n) / (N n : ℝ)) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => dHatSqrt2 α β (c n) (N n) (B n) (i n)) := by
  have hK := pg6_Kc_pos hα
  have hbulk := (pg6_bulk hreg i hx0 hxl).1
  -- y → 0+
  have hq : Tendsto (fun n => icCross α (B n) / rowNum (i n)) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => 1 / (Kc α * x0 * gammaOf (N n) (B n))) atTop (𝓝 0) := by
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop
        (hreg.hγ.const_mul_atTop (show 0 < Kc α * x0 by positivity))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall (fun n => div_nonneg (pg6_icCross_pos hα (hreg.hBpos n)).le
        (pg6_rowNum_pos _).le)) ?_
    filter_upwards [hxl] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    have hr := pg6_rowNum_pos (i n)
    rw [le_div_iff₀ hNr] at hn
    have h1 : icCross α (B n) / rowNum (i n) ≤ icCross α (B n) / (x0 * N n) :=
      div_le_div_of_nonneg_left (pg6_icCross_pos hα (hreg.hBpos n)).le (by positivity) hn
    refine h1.trans (le_of_eq ?_)
    unfold icCross gammaOf
    field_simp
  have hy : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝[>] 0) := by
    have h2 : Tendsto (fun n => (icCross α (B n) / rowNum (i n)) ^ α) atTop (𝓝 0) := by
      have := (Real.continuousAt_rpow_const 0 α (Or.inr (by linarith))).tendsto.comp hq
      rw [Real.zero_rpow (by linarith)] at this
      exact this
    exact tendsto_nhdsWithin_iff.2 ⟨h2, Eventually.of_forall (fun n =>
      Real.rpow_pos_of_pos (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)) _)⟩
  have hΦ := (lem_app_pl_super_iii hα hreg.hβ0 hreg.hβ1).comp_tendsto hy
  have hbΦ : IsEquivalent atTop (fun n => bN α (c n) (N n) (B n) *
      profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α))
      (fun n => bN α (c n) (N n) (B n) *
        (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α)))) :=
    (IsEquivalent.refl (u := fun n => bN α (c n) (N n) (B n))).mul hΦ
  have hden : ∀ n, 0 < dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2) :=
    fun n => pg6_den_pos hα (div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n))
  have h5 : IsEquivalent atTop
      ((fun n => bN α (c n) (N n) (B n) * profPhi α β ((icCross α (B n) / rowNum (i n)) ^ α)) *
        (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
          (dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2))))
      ((fun n => bN α (c n) (N n) (B n) *
        (dAl α * ((icCross α (B n) / rowNum (i n)) ^ α) ^ ((α - 1) / (2 * α)))) *
        (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
          (dAl α * Real.sqrt (Kc α) * (rowNum (i n) / (N n : ℝ)) ^ (-(α - 1) / 2)))) :=
    hbΦ.mul IsEquivalent.refl
  have hv : IsEquivalent atTop (fun n => dHatSqrt2 α β (c n) (N n) (B n) (i n))
      (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) := by
    refine (h5.congr_left (Eventually.of_forall (fun n => ?_))).congr_right
      (Eventually.of_forall (fun n => ?_))
    · simp only [Pi.mul_apply]
      unfold dHatSqrt2
      rw [if_neg (not_le.2 hα)]
      ring
    · simp only [Pi.mul_apply]
      rw [pg6_R_alg hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n) (i n),
        ← pg6_psiR_alg (hreg.hcpos n) (hreg.hNpos n) (i n)]
      have e : ∀ a d p : ℝ, d ≠ 0 → a * d * (p / d) = a * p := by
        intro a d p hd; field_simp
      exact e _ _ _ (hden n).ne'
  exact hbulk.trans hv.symm

private lemma pg6_dHat_pos_gt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (n : ℕ) (i : Fin (N n)) :
    0 < dHatSqrt2 α β (c n) (N n) (B n) i := by
  unfold dHatSqrt2
  rw [if_neg (not_le.2 hα)]
  have hx : 0 < rowNum i / (N n : ℝ) := div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n)
  have hy : 0 < (icCross α (B n) / rowNum i) ^ α :=
    Real.rpow_pos_of_pos (div_pos (pg6_icCross_pos hα (hreg.hBpos n)) (pg6_rowNum_pos _)) _
  have hΦ := (lem_app_pl_super_i hα hreg.hβ0 hreg.hβ1).2 _ hy
  have hΨ := lem_app_pl_Psi_i_pos hreg.hα _ ⟨hx, (div_le_one (by exact_mod_cast hreg.hNpos n)).2
    (pg6_rowNum_le _)⟩
  have := pg6_bN_pos hα (hreg.hcpos n) (hreg.hNpos n) (hreg.hBpos n)
  have := pg6_den_pos hα hx
  exact div_pos (mul_pos (mul_pos ‹_› hΦ.2) hΨ) ‹_›

private theorem pg6_core_gt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    IsEquivalent atTop (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
      (fun n => dHatSqrt2 α β (c n) (N n) (B n) (i n)) := by
  have hxu : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Icc (0 : ℝ) 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨(div_pos (pg6_rowNum_pos _) this).le, (div_le_one this).2 (pg6_rowNum_le _)⟩
  have hVpos : ∀ n, 0 < dHatSqrt2 α β (c n) (N n) (B n) (i n) := fun n =>
    pg6_dHat_pos_gt hreg hα n (i n)
  apply pg6_equiv_subseq hVpos
  intro φ hφ
  obtain ⟨x0, hx0, ψ, hψ, hxψ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => rowNum (i (φ n)) / (N (φ n) : ℝ)) (fun n => hxu (φ n))
  have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, hψ.tendsto_atTop, ?_⟩
  have hreg' := pg6_reg_comp hreg hθ
  have hi' : Tendsto (fun n => rowNum (i (φ (ψ n)))) atTop atTop := hi.comp hθ
  rcases hx0.1.eq_or_lt with h0 | h0
  · have hx : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) := by
      rw [h0]; exact hxψ
    exact pg6_core_gt_zero hreg' hα (fun n => i (φ (ψ n))) hi' hx
  · exact pg6_core_gt_pos hreg' hα (fun n => i (φ (ψ n))) hi' (x0 := x0 / 2) (by linarith)
      (hxψ.eventually (eventually_ge_nhds (show x0 / 2 < x0 by linarith)))

private theorem pg6_triple_gt {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (nN : ℕ → ℕ)
    (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε := by
  have key := pg6_uniform hreg nN hn
    (fun n i => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) i)
    (fun n i => dHatSqrt2 α β (c n) (N n) (B n) i) ?_ (fun n i => pg6_dHat_pos_gt hreg hα n i)
  · intro ε hε
    filter_upwards [key ε hε] with n hn' i hi
    have h2 : 0 < Real.sqrt 2 := by positivity
    have e : dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i =
        Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) i /
          dHatSqrt2 α β (c n) (N n) (B n) i := by
      unfold dHatDrift
      field_simp
    rw [e]
    exact hn' i hi
  · intro φ hφ i hi
    exact pg6_core_gt (pg6_reg_comp hreg hφ) hα i hi


/-! #### The crossover index `i_{c,d}` for `α ≤ 1` -/

private lemma pg6_icdD_pos {α : ℝ} (hα1 : α ≤ 1) : 0 < icdD α := by
  unfold icdD c0
  split_ifs with h
  · have : 0 < 1 - α := by linarith
    positivity
  · positivity

private lemma pg6_icdIdx_pos {α β : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (hLg : 0 < Real.log (gammaOf N B)) :
    0 < icdIdx β α N B := by
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hd := pg6_icdD_pos hα1
  have : (0 : ℝ) < N := by exact_mod_cast hN
  have : (0 : ℝ) < B := by exact_mod_cast hB
  unfold icdIdx
  split_ifs with h
  · positivity
  · positivity

/-- `W / (log γ)^ν = d (i / i_{c,d})^{-α/2}`. -/
private lemma pg6_W_icd {α β c : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hc : 0 < c) (hβ0 : 0 < β)
    (hβ1 : β < 1) {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (hLg : 0 < Real.log (gammaOf N B))
    (i : Fin N) :
    cutW β α c N B i / Real.log (gammaOf N B) ^ cutNu α =
      icdD α * (rowNum i / icdIdx β α N B) ^ (-α / 2) := by
  have hs2 := pg6_sPow_two_pos hβ0 hβ1
  have hd := pg6_icdD_pos hα1
  have hicd := pg6_icdIdx_pos hα0 hα1 hβ0 hβ1 hN hB hLg
  have hr := pg6_rowNum_pos i
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ := pg6_gamma_pos hB hN
  have hLν : 0 < Real.log (gammaOf N B) ^ cutNu α := Real.rpow_pos_of_pos hLg _
  have hq : 0 < rowNum i / icdIdx β α N B := div_pos hr hicd
  have hW0 := (pg6_cutW_sq (α := α) hc hβ0 hβ1 hN hB i)
  have hL : 0 ≤ cutW β α c N B i / Real.log (gammaOf N B) ^ cutNu α :=
    div_nonneg hW0.1 hLν.le
  have hR : 0 ≤ icdD α * (rowNum i / icdIdx β α N B) ^ (-α / 2) :=
    mul_nonneg hd.le (Real.rpow_nonneg hq.le _)
  rw [← sq_eq_sq₀ hL hR, div_pow, hW0.2, mul_pow]
  have e : ((rowNum i / icdIdx β α N B) ^ (-α / 2)) ^ 2 = (rowNum i / icdIdx β α N B) ^ (-α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]; congr 1; push_cast; ring
  rw [e]
  have hx : 0 < rowNum i / (N : ℝ) := div_pos hr hNr
  have e2 : (rowNum i / (N : ℝ)) ^ (-α) = (N : ℝ) ^ α * rowNum i ^ (-α) := by
    rw [Real.div_rpow hr.le hNr.le, Real.rpow_neg hNr.le, Real.rpow_neg hr.le]
    field_simp
  have e3 : (rowNum i / icdIdx β α N B) ^ (-α) = icdIdx β α N B ^ α * rowNum i ^ (-α) := by
    rw [Real.div_rpow hr.le hicd.le, Real.rpow_neg hicd.le, Real.rpow_neg hr.le]
    field_simp
  rw [e2, e3]
  have hrα : 0 < rowNum i ^ (-α) := Real.rpow_pos_of_pos hr _
  have hNα : 0 < (N : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
  have hLsq : (Real.log (gammaOf N B) ^ cutNu α) ^ 2 =
      Real.log (gammaOf N B) ^ (2 * cutNu α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLg.le]; congr 1; push_cast; ring
  rcases hα1.lt_or_eq with hlt | heq
  · have hν : cutNu α = 1 := by unfold cutNu; rw [if_pos hlt]
    rw [hν] at hLsq ⊢
    have hI : icdIdx β α N B ^ α = (B : ℝ) * (N : ℝ) ^ (α - 1) /
        (sPow β 2 * icdD α ^ 2 * Real.log (gammaOf N B) ^ 2) := by
      unfold icdIdx
      rw [if_pos hlt, ← Real.rpow_mul (by positivity)]
      rw [show 1 / α * α = 1 by field_simp, Real.rpow_one]
    rw [hI, Real.rpow_sub hNr, Real.rpow_one]
    rw [Real.rpow_one] at hLsq
    unfold gammaOf
    have hLsq' : Real.log ((N : ℝ) / B) ^ 2 = Real.log ((N : ℝ) / B) ^ (2 : ℝ) := by
      rw [Real.rpow_two]
    have hL2 : 0 < Real.log ((N : ℝ) / B) ^ 2 := by positivity
    simp only [Real.rpow_one]
    field_simp
  · subst heq
    have hν : cutNu 1 = 3 / 2 := by unfold cutNu; rw [if_neg (lt_irrefl _)]
    rw [hν] at hLsq ⊢
    have hI : icdIdx β 1 N B = (B : ℝ) / (sPow β 2 * icdD 1 ^ 2 * Real.log (gammaOf N B) ^ 3) := by
      unfold icdIdx; rw [if_neg (lt_irrefl _)]
    have e4 : Real.log (gammaOf N B) ^ (2 * ((3 : ℝ) / 2)) = Real.log (gammaOf N B) ^ 3 := by
      rw [show 2 * ((3 : ℝ) / 2) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [e4] at hLsq
    rw [hLsq, Real.rpow_one, hI]
    have hL3 : 0 < Real.log (gammaOf N B) ^ 3 := by positivity
    unfold gammaOf
    simp only [Real.rpow_one]
    field_simp


private lemma pg6_icd_over_N {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) :
    Tendsto (fun n => icdIdx β α (N n) (B n) / (N n : ℝ)) atTop (𝓝 0) := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have hd := pg6_icdD_pos hα1
  have hLg : Tendsto (fun n => Real.log (gammaOf (N n) (B n))) atTop atTop :=
    Real.tendsto_log_atTop.comp hreg.hγ
  have hκ : 0 < sPow β 2 * icdD α ^ 2 := by positivity
  have hα0 := hreg.hα
  rcases hα1.lt_or_eq with hlt | heq
  · -- α < 1
    have hg : Tendsto (fun n => 1 / (gammaOf (N n) (B n) * (sPow β 2 * icdD α ^ 2 *
        Real.log (gammaOf (N n) (B n)) ^ 2))) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => sPow β 2 * icdD α ^ 2 * Real.log (gammaOf (N n) (B n)) ^ 2)
          atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : (2:ℕ) ≠ 0)).comp hLg).const_mul_atTop hκ
      have h2 := Tendsto.atTop_mul_atTop₀ hreg.hγ h1
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop h2
    have h3 := (Real.continuousAt_rpow_const 0 (1 / α) (Or.inr (by positivity))).tendsto.comp hg
    rw [Real.zero_rpow (by positivity)] at h3
    refine h3.congr' ?_
    filter_upwards [hLg.eventually_gt_atTop 0] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
    simp only [Function.comp]
    unfold icdIdx
    rw [if_pos hlt, eq_div_iff hNr.ne']
    have e : (N n : ℝ) = ((N n : ℝ) ^ α) ^ (1 / α) := by
      rw [← Real.rpow_mul hNr.le, mul_one_div_cancel hreg.hα.ne', Real.rpow_one]
    have hNα : 0 < (N n : ℝ) ^ α := Real.rpow_pos_of_pos hNr _
    have hgpos : 0 < 1 / (gammaOf (N n) (B n) * (sPow β 2 * icdD α ^ 2 *
        Real.log (gammaOf (N n) (B n)) ^ 2)) := by
      have := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
      positivity
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
      have h1 : Tendsto (fun n => sPow β 2 * icdD 1 ^ 2 * Real.log (gammaOf (N n) (B n)) ^ 3)
          atTop atTop :=
        ((tendsto_pow_atTop (by norm_num : (3:ℕ) ≠ 0)).comp hLg).const_mul_atTop hκ
      have h2 := Tendsto.atTop_mul_atTop₀ hreg.hγ h1
      exact (tendsto_const_nhds (x := (1:ℝ))).div_atTop h2
    refine hg.congr' ?_
    filter_upwards [hLg.eventually_gt_atTop 0] with n hn
    have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    have hBr : (0 : ℝ) < B n := by exact_mod_cast hreg.hBpos n
    unfold icdIdx gammaOf
    rw [if_neg (lt_irrefl _)]
    have : Real.log ((N n : ℝ) / B n) ≠ 0 := hn.ne'
    field_simp


/-! #### `W` against `Ψ` -/

private lemma pg6_psi_o_W {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0))
    (h : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop) :
    IsLittleO atTop (fun n => profPsi α (rowNum (i n) / (N n : ℝ)))
      (fun n => cutW β α (c n) (N n) (B n) (i n)) := by
  have hreg1 := pg6_reg_one hreg
  have h1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop :=
    h.congr (fun n => by simp only [pg6_cutW_c_indep hreg i n])
  have hlo := (lem_app_pl_cutoff_ii hreg1 hα1 (fun _ => rfl) i hi hx 1 one_pos h1).congr
    (fun n => rfl) (fun n => pg6_cutW_c_indep hreg i n)
  rw [isLittleO_iff] at hlo ⊢
  intro ε hε
  filter_upwards [hlo hε, hreg.hγ.eventually_ge_atTop 1, hreg.hγ.eventually_gt_atTop 0] with n hn h3 h4
  have hx' : 0 < rowNum (i n) / (N n : ℝ) :=
    div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos n)
  have hγ : 0 < gammaOf (N n) (B n) := h4
  have hψ := pg6_psiRes_nonneg hreg.hα (η := 1 / gammaOf (N n) (B n)) (by positivity)
    (by rw [div_le_one hγ]; exact h3) hx'
  have hΨ := lem_app_pl_Psi_i_pos hreg.hα _ ⟨hx', (div_le_one (by exact_mod_cast hreg.hNpos n)).2
    (pg6_rowNum_le _)⟩
  have hWp := pg6_cutW_pos (α := α) (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (add_pos_of_pos_of_nonneg hΨ hψ),
    abs_of_pos hWp] at hn
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hΨ, abs_of_pos hWp]
  linarith


private lemma pg6_W_bulk_tendsto {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (i : (n : ℕ) → Fin (N n)) {x0 : ℝ} (hx0 : 0 < x0)
    (hxl : ∀ᶠ n in atTop, x0 ≤ rowNum (i n) / (N n : ℝ)) :
    Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n)) atTop (𝓝 0) := by
  have hs2 := pg6_sPow_two_pos hreg.hβ0 hreg.hβ1
  have h1 : Tendsto (fun n => x0 ^ (-α) / (gammaOf (N n) (B n) * sPow β 2)) atTop (𝓝 0) :=
    (tendsto_const_nhds (x := x0 ^ (-α))).div_atTop (hreg.hγ.atTop_mul_const hs2)
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  rw [Real.sqrt_zero] at h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall (fun n => (pg6_cutW_pos (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n)
      (hreg.hBpos n) (i n)).le)) ?_
  filter_upwards [hxl] with n hn
  rw [pg6_cutW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)]
  simp only [Function.comp]
  refine Real.sqrt_le_sqrt ?_
  have hγ := pg6_gamma_pos (hreg.hBpos n) (hreg.hNpos n)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hx0 hn (by have := hreg.hα; linarith)

private lemma pg6_W_o_psi {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop)
    (h : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 0)) :
    Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      profPsi α (rowNum (i n) / (N n : ℝ))) atTop (𝓝 0) := by
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hxu : ∀ n, rowNum (i n) / (N n : ℝ) ∈ Icc (0 : ℝ) 1 := fun n => by
    have : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
    exact ⟨(div_pos (pg6_rowNum_pos _) this).le, (div_le_one this).2 (pg6_rowNum_le _)⟩
  obtain ⟨κ, hκ, hκle⟩ := lem_app_pl_Psi_i_lower hreg.hα
  apply tendsto_of_subseq_tendsto
  intro φ hφ
  obtain ⟨x0, hx0, ψ, hψ, hxψ⟩ := isCompact_Icc.tendsto_subseq
    (x := fun n => rowNum (i (φ n)) / (N (φ n) : ℝ)) (fun n => hxu (φ n))
  have hθ : Tendsto (fun n => φ (ψ n)) atTop atTop := hφ.comp hψ.tendsto_atTop
  refine ⟨ψ, ?_⟩
  have hreg' := pg6_reg_comp hreg hθ
  rcases hx0.1.eq_or_lt with h0 | h0
  · have hx : Tendsto (fun n => rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ)) atTop (𝓝 0) := by
      rw [h0]; exact hxψ
    have hi' : Tendsto (fun n => rowNum (i (φ (ψ n)))) atTop atTop := hi.comp hθ
    have hreg1 := pg6_reg_one hreg'
    have h1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N (φ (ψ n))) (B (φ (ψ n)))
        (i (φ (ψ n))) / Real.log (gammaOf (N (φ (ψ n))) (B (φ (ψ n)))) ^ cutNu α) atTop (𝓝 0) :=
      (h.comp hθ).congr (fun n => by
        simp only [Function.comp, pg6_cutW_c_indep hreg (i) (φ (ψ n))])
    obtain ⟨-, hlo⟩ := (lem_app_pl_cutoff_iii hreg1 hα1 (fun _ => rfl) (fun n => i (φ (ψ n))) hi'
      hx).2 h1
    have hlo' := hlo.congr (fun n => pg6_cutW_c_indep hreg i (φ (ψ n))) (fun n => rfl)
    exact hlo'.tendsto_div_nhds_zero
  · have hW := pg6_W_bulk_tendsto hreg' (fun n => i (φ (ψ n))) (x0 := x0 / 2) (by linarith)
      (hxψ.eventually (eventually_ge_nhds (show x0 / 2 < x0 by linarith)))
    have hκ' := hW.div_const κ
    rw [zero_div] at hκ'
    change Tendsto (fun n => cutW β α (c (φ (ψ n))) (N (φ (ψ n))) (B (φ (ψ n))) (i (φ (ψ n))) /
      profPsi α (rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ))) atTop (𝓝 0)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hκ'
      (Eventually.of_forall (fun n => div_nonneg (hWp _).le (hΨ _).le)) ?_
    refine Eventually.of_forall (fun n => ?_)
    have hxn : 0 < rowNum (i (φ (ψ n))) / (N (φ (ψ n)) : ℝ) :=
      div_pos (pg6_rowNum_pos _) (by exact_mod_cast hreg.hNpos _)
    exact div_le_div_of_nonneg_left (hWp _).le hκ (hκle _ ⟨hxn, (hxu _).2⟩)


/-! #### Assembly of `thm_app_pl_drift_i` -/

private lemma pg6_icdA_eq {α c : ℝ} (hα1 : α ≤ 1) (N B : ℕ) :
    icdA α c N B = icdD α * aN α c N * Real.log (gammaOf N B) ^ cutNu α := by
  unfold icdA cutNu
  rcases hα1.lt_or_eq with hlt | heq
  · rw [if_pos hlt, if_pos hlt, Real.rpow_one]
  · subst heq
    rw [if_neg (lt_irrefl _), if_neg (lt_irrefl _)]

private lemma pg6_i_hx {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n)) {l : ℝ}
    (h : Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 l)) :
    Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) := by
  have h2 := h.mul (pg6_icd_over_N hreg hα1)
  rw [mul_zero] at h2
  refine h2.congr' ?_
  filter_upwards [(Real.tendsto_log_atTop.comp hreg.hγ).eventually_gt_atTop 0] with n hn
  have hicd := pg6_icdIdx_pos hreg.hα hα1 hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) hn
  have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
  field_simp

private lemma pg6_i_ratio {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n)) :
    ∀ᶠ n in atTop, cutW β α (c n) (N n) (B n) (i n) / Real.log (gammaOf (N n) (B n)) ^ cutNu α =
      icdD α * (rowNum (i n) / icdIdx β α (N n) (B n)) ^ (-α / 2) := by
  filter_upwards [(Real.tendsto_log_atTop.comp hreg.hγ).eventually_gt_atTop 0] with n hn
  exact pg6_W_icd hreg.hα hα1 (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) hn (i n)

private lemma pg6_i_a {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    ∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
          icdA α (c n) (N n) (B n)) atTop (𝓝 (1 + x ^ (-α / 2))) := by
  intro x hx0 hX
  have hx0' : (0 : ℝ) < x := hx0
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hd := pg6_icdD_pos hα1
  have hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) := pg6_i_hx hreg hα1 i hX
  have hz : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 (icdD α * x ^ (-α / 2))) := by
    have h1 : Tendsto (fun n => (rowNum (i n) / icdIdx β α (N n) (B n)) ^ (-α / 2)) atTop
        (𝓝 (x ^ (-α / 2))) :=
      (Real.continuousAt_rpow_const x _ (Or.inl hx0'.ne')).tendsto.comp hX
    exact (h1.const_mul (icdD α)).congr' ((pg6_i_ratio hreg hα1 i).mono (fun n hn => hn.symm))
  have hz0 : 0 < icdD α * x ^ (-α / 2) := by
    have := Real.rpow_pos_of_pos hx0' (-α / 2)
    positivity
  have hreg1 := pg6_reg_one hreg
  have hz1 : Tendsto (fun n => cutW β α ((fun _ => (1 : ℝ)) n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 (icdD α * x ^ (-α / 2))) :=
    hz.congr (fun n => by simp only [pg6_cutW_c_indep hreg i n])
  have hΨeq := (lem_app_pl_cutoff_i hreg1 hα1 (fun _ => rfl) i hi hx 1 one_pos _ hz0 hz1).2
  have hcore := pg6_core_le hreg hα1 i hi
  have hvpos : ∀ n, 0 < aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
      profPsi α (rowNum (i n) / (N n : ℝ))) := fun n => mul_pos (han n) (add_pos (hWp n) (hΨ n))
  have h1 := (isEquivalent_iff_tendsto_one (Eventually.of_forall (fun n => (hvpos n).ne'))).1 hcore
  have hLgev := (Real.tendsto_log_atTop.comp hreg.hγ).eventually_gt_atTop 0
  have hl1 : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α / icdD α) atTop (𝓝 (x ^ (-α / 2))) := by
    have := hz.div_const (icdD α)
    rwa [mul_div_cancel_left₀ _ hd.ne'] at this
  have hl2 : Tendsto (fun n => profPsi α (rowNum (i n) / (N n : ℝ)) /
      (icdD α * Real.log (gammaOf (N n) (B n)) ^ cutNu α)) atTop (𝓝 1) := by
    have := (isEquivalent_iff_tendsto_one (hLgev.mono (fun n hn => (mul_pos hd
      (Real.rpow_pos_of_pos hn _)).ne'))).1 hΨeq
    exact this
  have h2 : Tendsto (fun n => aN α (c n) (N n) * (cutW β α (c n) (N n) (B n) (i n) +
      profPsi α (rowNum (i n) / (N n : ℝ))) / icdA α (c n) (N n) (B n)) atTop
      (𝓝 (1 + x ^ (-α / 2))) := by
    have := hl2.add hl1
    rw [show (1 : ℝ) + x ^ (-α / 2) = 1 + x ^ (-α / 2) from rfl] at this
    refine this.congr' ?_
    filter_upwards [hLgev] with n hn
    rw [pg6_icdA_eq hα1]
    have hL := Real.rpow_pos_of_pos hn (cutNu α)
    have := han n
    field_simp
    ring
  have := h1.mul h2
  rw [one_mul] at this
  refine this.congr' (Eventually.of_forall (fun n => ?_))
  simp only [Pi.div_apply]
  have e : ∀ a b c : ℝ, b ≠ 0 → a / b * (b / c) = a / c := fun a b c hb => by
    rcases eq_or_ne c 0 with h | h
    · simp [h]
    · field_simp
  exact e _ _ _ (hvpos n).ne'


private lemma pg6_equiv_add_small (a W P D : ℕ → ℝ)
    (ha : ∀ n, 0 < a n) (hP : ∀ n, 0 < P n) (hW : ∀ n, 0 < W n)
    (hD : IsEquivalent atTop D (fun n => a n * (W n + P n)))
    (hlo : IsLittleO atTop W P) : IsEquivalent atTop D (fun n => a n * P n) := by
  refine hD.trans ?_
  rw [IsEquivalent]
  have h1 : IsLittleO atTop (fun n => a n * W n) (fun n => a n * P n) :=
    (isBigO_refl a atTop).mul_isLittleO hlo
  refine h1.congr (fun n => ?_) (fun n => rfl)
  simp only [Pi.sub_apply]
  ring

private lemma pg6_equiv_add_big (a W P D : ℕ → ℝ)
    (hD : IsEquivalent atTop D (fun n => a n * (W n + P n)))
    (hlo : IsLittleO atTop P W) : IsEquivalent atTop D (fun n => a n * W n) := by
  refine hD.trans ?_
  rw [IsEquivalent]
  have h1 : IsLittleO atTop (fun n => a n * P n) (fun n => a n * W n) :=
    (isBigO_refl a atTop).mul_isLittleO hlo
  refine h1.congr (fun n => ?_) (fun n => rfl)
  simp only [Pi.sub_apply]
  ring

private lemma pg6_i_b {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2))) := by
  intro hX
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hd := pg6_icdD_pos hα1
  have hx : Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) := pg6_i_hx hreg hα1 i hX
  have hLgev := (Real.tendsto_log_atTop.comp hreg.hγ).eventually_gt_atTop 0
  have hXpos : ∀ᶠ n in atTop, 0 < rowNum (i n) / icdIdx β α (N n) (B n) := by
    filter_upwards [hLgev] with n hn
    exact div_pos (pg6_rowNum_pos _) (pg6_icdIdx_pos hreg.hα hα1 hreg.hβ0 hreg.hβ1
      (hreg.hNpos n) (hreg.hBpos n) hn)
  have hXinv : Tendsto (fun n => (rowNum (i n) / icdIdx β α (N n) (B n))⁻¹) atTop atTop :=
    tendsto_inv_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.2 ⟨hX, hXpos⟩)
  have hinf : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop atTop := by
    have h1 : Tendsto (fun n => ((rowNum (i n) / icdIdx β α (N n) (B n))⁻¹) ^ (α / 2)) atTop atTop :=
      (tendsto_rpow_atTop (by have := hreg.hα; positivity)).comp hXinv
    have h2 := h1.const_mul_atTop hd
    refine h2.congr' ?_
    filter_upwards [pg6_i_ratio hreg hα1 i, hXpos] with n hn hp
    rw [hn, Real.inv_rpow hp.le, show -α / 2 = -(α / 2) by ring, Real.rpow_neg hp.le]
  have hΨW := pg6_psi_o_W hreg hα1 i hi hx hinf
  have hcore := pg6_core_le hreg hα1 i hi
  have := pg6_equiv_add_big (fun n => aN α (c n) (N n)) _ _ _ hcore hΨW
  exact this.congr_right (Eventually.of_forall (fun n =>
    pg6_aW_eq (hreg.hcpos n) hreg.hβ0 hreg.hβ1 (hreg.hNpos n) (hreg.hBpos n) (i n)))


private lemma pg6_i_c {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα1 : α ≤ 1) (i : (n : ℕ) → Fin (N n))
    (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
      (Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) →
        IsEquivalent atTop
          (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => icdD α * aN α (c n) (N n) *
            (if α < 1 then Real.log (((N n : ℝ) / rowNum (i n)) ^ α)
              else Real.log ((N n : ℝ) / rowNum (i n)) ^ ((3 : ℝ) / 2)))) := by
  intro hX
  obtain ⟨hΨ, han, hWp⟩ := pg6_pos_facts hreg i
  have hd := pg6_icdD_pos hα1
  have hz0 : Tendsto (fun n => cutW β α (c n) (N n) (B n) (i n) /
      Real.log (gammaOf (N n) (B n)) ^ cutNu α) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => (rowNum (i n) / icdIdx β α (N n) (B n)) ^ (-(α / 2))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by have := hreg.hα; positivity)).comp hX
    have h2 := h1.const_mul (icdD α)
    rw [mul_zero] at h2
    refine h2.congr' ?_
    filter_upwards [pg6_i_ratio hreg hα1 i] with n hn
    rw [hn, show -α / 2 = -(α / 2) by ring]
  have hlo : IsLittleO atTop (fun n => cutW β α (c n) (N n) (B n) (i n))
      (fun n => profPsi α (rowNum (i n) / (N n : ℝ))) :=
    (isLittleO_iff_tendsto' (Eventually.of_forall (fun n h => absurd h (hΨ n).ne'))).2
      (pg6_W_o_psi hreg hα1 i hi hz0)
  have hcore := pg6_core_le hreg hα1 i hi
  have h1 := pg6_equiv_add_small (fun n => aN α (c n) (N n)) _ _ _ han hΨ hWp hcore hlo
  refine ⟨h1, fun hx => ?_⟩
  have hreg1 := pg6_reg_one hreg
  have hpre := lem_app_pl_cutoff_pre hreg1 hα1 (fun _ => rfl) i hi hx
  have h2 : IsEquivalent atTop (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ)))
      (fun n => aN α (c n) (N n) * (icdD α * cutT α (rowNum (i n) / (N n : ℝ)) ^ cutNu α)) :=
    (IsEquivalent.refl (u := fun n => aN α (c n) (N n))).mul hpre
  refine (h1.trans h2).congr_right (Eventually.of_forall (fun n => ?_))
  have hr := pg6_rowNum_pos (i n)
  have hNr : (0 : ℝ) < N n := by exact_mod_cast hreg.hNpos n
  unfold cutT cutNu
  beta_reduce
  rcases hα1.lt_or_eq with hlt | heq
  · simp only [hlt, if_true, Real.rpow_one]
    have : (rowNum (i n) / (N n : ℝ)) ^ (-α) = ((N n : ℝ) / rowNum (i n)) ^ α := by
      rw [Real.rpow_neg (div_pos hr hNr).le, ← Real.inv_rpow (div_pos hr hNr).le, inv_div]
    rw [this]; ring
  · subst heq
    simp only [lt_irrefl, if_false, one_div_div]
    ring

/-! ### P-G.6.P1 helpers (end) -/

/-- Helper of `thm:app-pl-triple` (drift half, α ≤ 1), statement from `section.tex`:

\begin{theorem}[The coefficient pair]\label{thm:app-pl-triple}
Under \cref{assum:app-pl-regime}, for every sequence of integers $1\le n_N\le N$
with $n_N\to\infty$,
\begin{equation}\label{eqn:app-pl-triple}
\sup_{n_N\le i\le N}\max\Big\{\Big|\frac{\mathfrak d_i(0)}{\widehat{\mathfrak d}_i}-1\Big|,\ \Big|\frac{\mathfrak v_i(0)}{\widehat{\mathfrak v}_i}-1\Big|\Big\}\longrightarrow0 .
\end{equation}
\end{theorem}
-/
theorem triple_drift_le_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1) (nN : ℕ → ℕ)
    (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n) (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε := by
  exact pg6_triple_le hreg hα nN hn

/-- Helper of `thm:app-pl-triple` (drift half, α > 1), statement from `section.tex`:

\begin{theorem}[The coefficient pair]\label{thm:app-pl-triple}
Under \cref{assum:app-pl-regime}, for every sequence of integers $1\le n_N\le N$
with $n_N\to\infty$,
\begin{equation}\label{eqn:app-pl-triple}
\sup_{n_N\le i\le N}\max\Big\{\Big|\frac{\mathfrak d_i(0)}{\widehat{\mathfrak d}_i}-1\Big|,\ \Big|\frac{\mathfrak v_i(0)}{\widehat{\mathfrak v}_i}-1\Big|\Big\}\longrightarrow0 .
\end{equation}
\end{theorem}
-/
theorem triple_drift_gt_one {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α) (nN : ℕ → ℕ)
    (hnN : ∀ n, 1 ≤ nN n ∧ nN n ≤ N n) (hn : Tendsto (fun n => (nN n : ℝ)) atTop atTop) :
    ∀ ε > 0, ∀ᶠ n in atTop, ∀ i : Fin (N n), (nN n : ℝ) ≤ rowNum i →
      |dZero β (B n) (plSpec α (c n) (N n)) i / dHatDrift α β (c n) (N n) (B n) i - 1| ≤ ε := by
  exact pg6_triple_gt hreg hα nN hn


/-- `thm:app-pl-drift`, part (i) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{theorem}[Drift crossover]\label{thm:app-pl-drift}
Assume \cref{assum:app-pl-regime} and let $i=i_N\to\infty$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item Let $0<\alpha\le1$ and put
\begin{equation}\label{eqn:app-pl-icd}
\begin{gathered}
d\defeq\frac{c_0}{\sqrt{1-\alpha}},\quad i_{\mathrm c,\mathfrak d}\defeq\Big[\frac{BN^{\alpha-1}}{\sw2d^2\log^2\gamma}\Big]^{1/\alpha},\quad
a_{\mathfrak d}\defeq d\,a_N\log\gamma\quad(\alpha<1);\\
d\defeq\frac23c_0,\quad i_{\mathrm c,\mathfrak d}\defeq\frac{B}{\sw2d^2\log^3\gamma},\quad
a_{\mathfrak d}\defeq d\,a_N(\log\gamma)^{3/2}\quad(\alpha=1).
\end{gathered}
\end{equation}
If $i/i_{\mathrm c,\mathfrak d}\to x\in(0,\infty)$, then
$\sqrt2\,\mathfrak d_i(0)/a_{\mathfrak d}\to1+x^{-\alpha/2}$. If $i/i_{\mathrm c,\mathfrak d}\to0$,
then $\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_i/(\gamma\sw2)}$. If $i/i_{\mathrm c,\mathfrak d}\to\infty$,
then $\sqrt2\,\mathfrak d_i(0)\sim a_N\Psi_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\sqrt2\,\mathfrak d_i(0)\sim d\,a_N\log\big((N/i)^\alpha\big)\ \ (\alpha<1),\qquad
\sqrt2\,\mathfrak d_i(0)\sim d\,a_N\big[\log(N/i)\big]^{3/2}\ \ (\alpha=1).
\]
\item Let $\alpha>1$. If $i/i_{\mathrm c}\to x\in(0,\infty)$, then
$\sqrt2\,\mathfrak d_i(0)/b_N\to\Phi_{\alpha,\bmom}(x^{-\alpha})$. If $i/i_{\mathrm c}\to0$, then
$\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_i/(\gamma\sw2)}$. If $i/i_{\mathrm c}\to\infty$, then
$\sqrt2\,\mathfrak d_i(0)\sim a_N\Psi_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\sqrt2\,\mathfrak d_i(0)\sim d_\alpha\sqrt{c_NK_\alpha}\,N^{-1/2}\,i^{-(\alpha-1)/2}.
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_drift_i {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : α ≤ 1)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    (∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
          icdA α (c n) (N n) (B n)) atTop (𝓝 (1 + x ^ (-α / 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icdIdx β α (N n) (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
      (Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) →
        IsEquivalent atTop
          (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => icdD α * aN α (c n) (N n) *
            (if α < 1 then Real.log (((N n : ℝ) / rowNum (i n)) ^ α)
              else Real.log ((N n : ℝ) / rowNum (i n)) ^ ((3 : ℝ) / 2))))) := by
  exact ⟨pg6_i_a hreg hα i hi, pg6_i_b hreg hα i hi, pg6_i_c hreg hα i hi⟩

/-- `thm:app-pl-drift`, part (ii) (snapshot `cr-2026-10-23`). LaTeX, verbatim from
`sections/06-power-law/section.tex`:

\begin{theorem}[Drift crossover]\label{thm:app-pl-drift}
Assume \cref{assum:app-pl-regime} and let $i=i_N\to\infty$ be a row sequence.
\begin{enumerate}[label=(\roman*)]
\item Let $0<\alpha\le1$ and put
\begin{equation}\label{eqn:app-pl-icd}
\begin{gathered}
d\defeq\frac{c_0}{\sqrt{1-\alpha}},\quad i_{\mathrm c,\mathfrak d}\defeq\Big[\frac{BN^{\alpha-1}}{\sw2d^2\log^2\gamma}\Big]^{1/\alpha},\quad
a_{\mathfrak d}\defeq d\,a_N\log\gamma\quad(\alpha<1);\\
d\defeq\frac23c_0,\quad i_{\mathrm c,\mathfrak d}\defeq\frac{B}{\sw2d^2\log^3\gamma},\quad
a_{\mathfrak d}\defeq d\,a_N(\log\gamma)^{3/2}\quad(\alpha=1).
\end{gathered}
\end{equation}
If $i/i_{\mathrm c,\mathfrak d}\to x\in(0,\infty)$, then
$\sqrt2\,\mathfrak d_i(0)/a_{\mathfrak d}\to1+x^{-\alpha/2}$. If $i/i_{\mathrm c,\mathfrak d}\to0$,
then $\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_i/(\gamma\sw2)}$. If $i/i_{\mathrm c,\mathfrak d}\to\infty$,
then $\sqrt2\,\mathfrak d_i(0)\sim a_N\Psi_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\sqrt2\,\mathfrak d_i(0)\sim d\,a_N\log\big((N/i)^\alpha\big)\ \ (\alpha<1),\qquad
\sqrt2\,\mathfrak d_i(0)\sim d\,a_N\big[\log(N/i)\big]^{3/2}\ \ (\alpha=1).
\]
\item Let $\alpha>1$. If $i/i_{\mathrm c}\to x\in(0,\infty)$, then
$\sqrt2\,\mathfrak d_i(0)/b_N\to\Phi_{\alpha,\bmom}(x^{-\alpha})$. If $i/i_{\mathrm c}\to0$, then
$\sqrt2\,\mathfrak d_i(0)\sim\sqrt{\mu_i/(\gamma\sw2)}$. If $i/i_{\mathrm c}\to\infty$, then
$\sqrt2\,\mathfrak d_i(0)\sim a_N\Psi_\alpha(i/N)$, and if moreover $i/N\to0$,
\[
\sqrt2\,\mathfrak d_i(0)\sim d_\alpha\sqrt{c_NK_\alpha}\,N^{-1/2}\,i^{-(\alpha-1)/2}.
\]
\end{enumerate}
\end{theorem}
-/
theorem thm_app_pl_drift_ii {α β : ℝ} {N B : ℕ → ℕ} {c : ℕ → ℝ}
    (hreg : assum_app_pl_regime α β N B c) (hα : 1 < α)
    (i : (n : ℕ) → Fin (N n)) (hi : Tendsto (fun n => rowNum (i n)) atTop atTop) :
    (∀ x ∈ Ioi (0 : ℝ),
      Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 x) →
        Tendsto (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n) /
          bN α (c n) (N n) (B n)) atTop (𝓝 (profPhi α β (x ^ (-α))))) ∧
    (Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop (𝓝 0) →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => Real.sqrt (plSpec α (c n) (N n) (i n) / (gammaOf (N n) (B n) * sPow β 2)))) ∧
    (Tendsto (fun n => rowNum (i n) / icCross α (B n)) atTop atTop →
      IsEquivalent atTop
        (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
        (fun n => aN α (c n) (N n) * profPsi α (rowNum (i n) / (N n : ℝ))) ∧
      (Tendsto (fun n => rowNum (i n) / (N n : ℝ)) atTop (𝓝 0) →
        IsEquivalent atTop
          (fun n => Real.sqrt 2 * dZero β (B n) (plSpec α (c n) (N n)) (i n))
          (fun n => dAl α * Real.sqrt (c n * Kc α) * (N n : ℝ) ^ (-(1 : ℝ) / 2) *
            rowNum (i n) ^ (-(α - 1) / 2)))) := by
  exact ⟨pg6_ii_a hreg hα i hi, fun h => pg6_ii_b hreg hα i hi h,
    fun h => ⟨pg6_ii_c1 hreg hα i hi h, fun hx => pg6_ii_small hreg hα i hi hx h⟩⟩

end Muon.PowerLaw
