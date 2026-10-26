import Mathlib
import Muon.Phase.PhaseTheorems

/-!
# Appendix H: fixed-dimension asymptotics and the winners (task L-H.9)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`:
`thm:app-phase-fixed` (l.1339–1346), `cor:app-phase-fixed` (l.1348–1356),
`prop:app-phase-winners` (l.1386–1440), `prop:app-phase-cutoff` (l.1442–1451).
Card: `sections/07-phase-comparison/CARD.md` §2, §3, §5 (L-H.9), §6.1, §6.6.

Encoding decisions (statements only; proofs are `sorry`):
* The fixed-dimension theorems take a finite-index model `m` whose coefficient arrays are
  fixed. The matched models `mE ε` (at each `ε > 0`) share those arrays and carry step
  `η = 2√ε/𝒮` through `IsMatchedModel`, so no structure update of `RowModel` is used.
* Hitting times are `stepHit` (in `ℝ≥0∞`); `IsEquivalent` and limits use the `toReal` values, as
  in `PhaseTheorems`. An `∞` hitting time is excluded by the window Props, which assert
  attainment, or by the `IsEquivalent` form itself.
* The ratio `𝖱 = t^{s-SGD}_{Tε}/t^{s-SVD}_{Tε}` is `phaseR`. The windows enter only through the
  named Props `PhaseAWindowHolds`, `PhaseBWindowHolds`, `PhaseWinA`, `PhaseWinB`,
  `PhaseLowWindow` of `PhaseTheorems` (constants are never re-quantified).
* Sequence statements quantify over dependent families as in `PhaseTheorems`. The standing
  assumptions `N_n → ∞`, `ε_n ↓ 0`, `1 ≤ N_n ≤ B_n` and matched Volterra models are packaged in
  `MatchedSeq`. Families given by an explicit formula (`N^{-ω}`, `(log N)^{-ω}`, `N^{-r}(log N)^b`,
  `1/log N`) hold as equalities eventually (`∀ᶠ`), except `N^{-ω}`, which holds for every `N ≥ 1`.
* `prop_app_phase_winners` is split into declarations `_i` (the `≍` display, with the
  window constants of `PhaseAWindowHolds`), `_i_zero`, `_i_alpha1`, `_i_mid`, `_i_two`,
  `_i_gt2` (the limit claims of part (i)), `_ii`, `_iii`, `_iv`, `_tauc` (the "so that"
  identities of (v)), `_v_a`, `_v_b_pow`, `_v_b_log`, `_v_c_pow`, `_v_c_log`.
* The `≍` in part (i) is stated with the explicit five-case table `winnersRateI` (no reduction to
  `phaseDN · phaseRatioRate`). Its existential constants `dLo, dHi` come after the window hypothesis
  and before all `(N, B, ε)`, so they depend only on the window data.
* `prop_app_phase_winners_iv` (`≍`/`O` with unstated constants in the source, card §6.6) takes one
  constant `C` before all sequences, with dependence on `α, ς, T` only.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped ENNReal NNReal

set_option linter.style.longLine false

noncomputable section

namespace Muon.Phase

/-! ## Transcription helpers

These name objects of the section; they add no mathematical content. -/

/-- The step-hitting ratio `𝖱 = t^{s-SGD}_{Tε}/t^{s-SVD}_{Tε}` of `prop:app-phase-winners`, on
the `toReal` values of the two matched models (`ℝ≥0∞` hitting times of `stepHit`). -/
def phaseR {N : ℕ} (T ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ) : ℝ :=
  (stepHit mG QG T ε).toReal / (stepHit mS QS T ε).toReal

/-- The standing sequence hypotheses of the sequence statements of `prop:app-phase-winners`,
`prop:app-phase-cutoff`: `N_n → ∞`, `ε_n ↓ 0`, `ε_n > 0`, `1 ≤ N_n ≤ B_n`, and for each `n` the
matched SignSVD and SignSGD models at level `ε_n` with Volterra solutions (`def:app-phase-arrays`,
`thm:app-phase-hitting`). -/
def MatchedSeq (α ς : ℝ) (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ)
    (mS mG : ∀ n : ℕ, RowModel (Fin (Nseq n))) (QS QG : ℕ → ℝ → ℝ) : Prop :=
  Tendsto (fun n => (Nseq n : ℝ)) atTop atTop ∧ Tendsto εs atTop (𝓝 0) ∧ (∀ n, 0 < εs n) ∧
    (∀ n, 1 ≤ Nseq n) ∧ (∀ n, Nseq n ≤ Bseq n) ∧
    (∀ n, IsMatchedModel (svdArrays α ς (Nseq n) (Bseq n)) (mS n) (εs n)) ∧
    (∀ n, IsVolterraSol (mS n) (QS n)) ∧
    (∀ n, IsMatchedModel (sgdArrays α ς (Nseq n) (Bseq n)) (mG n) (εs n)) ∧
    (∀ n, IsVolterraSol (mG n) (QG n))

/-- The accuracy `ε_N = N^{-ω}` (`prop:app-phase-cutoff`, `prop:app-phase-winners`(i), (v)). -/
def powerEps (ω : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-ω)

/-- The accuracy `ε_N = N^{-r} (log N)^b` of `prop:app-phase-winners`(i) with `α = 1`. -/
def logPowEps (r b : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (-r) * Real.log (N : ℝ) ^ b

/-- The accuracy `ε_N = (log N)^{-ω}` of `prop:app-phase-winners`(i) with `α = 2`. -/
def logEps (ω : ℝ) (N : ℕ) : ℝ := Real.log (N : ℝ) ^ (-ω)

/-- The accuracy `ε_N = 1/log N` of `prop:app-phase-winners`(v)(b), (c). -/
def invLogEps (N : ℕ) : ℝ := 1 / Real.log (N : ℝ)

/-- The table of `prop:app-phase-winners`(i) for `𝖱` in the range `ς < 1`, with
`p = α + ς`, `r = r_{s-SVD} = (p-1)/α`, `Ξ = εN^{p-1}`. The last branch (`α > 2`) is `ε^{-1/(2r)}`. -/
def winnersRateI (α ς : ℝ) (N : ℕ) (ε : ℝ) : ℝ :=
  let r := (α + ς - 1) / α
  let Xi := ε * (N : ℝ) ^ (α + ς - 1)
  if α < 1 then Xi ^ (-(1 / (2 * r)))
  else if α = 1 then Real.log (N : ℝ) * Xi ^ (-(1 / (2 * r)))
  else if α < 2 then (N : ℝ) ^ (α - 1) * Xi ^ (-(1 / (2 * r)))
  else if α = 2 then (N : ℝ) / Real.log (N : ℝ) * Xi ^ (-(1 / (2 * r)))
  else ε ^ (-(1 / (2 * r)))

/-- The threshold `τ_c(α) = (α² - 2α + 3)/(3 - α)` of `prop:app-phase-winners`(v). -/
def winnersTauC (α : ℝ) : ℝ := (α ^ 2 - 2 * α + 3) / (3 - α)

/-- The threshold `ω_c = (2-α)(p-1)/(α+1-ς)` of `prop:app-phase-winners`(v)(b). -/
def winnersOmegaC (α ς : ℝ) : ℝ := (2 - α) * (α + ς - 1) / (α + 1 - ς)

/-- The limit `π ζ(α) J(p,α) / (ζ(α/2) J(p,α/2))` of `prop:app-phase-winners`(ii), with
`ζ` the real series `zetaR` and `p = α + ς`. -/
def winnersLimitII (α ς : ℝ) : ℝ :=
  Real.pi * zetaR α * Jpq (α + ς) α / (zetaR (α / 2) * Jpq (α + ς) (α / 2))

/-! ## Fixed dimension -/

/-- Private (P-H.9.P1): the hitting-time sandwich of the fixed-arrays model, via the mixture
representation of `lem_app_phase_mixture`. -/
lemma aux_fixed_hit {ι : Type*} [Finite ι] (m m' : RowModel ι) (T ε bmin : ℝ)
    (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < m.F0 / T) (hbmin : 0 < bmin)
    (hb : ∀ i, bmin ≤ 2 * m.d i)
    (hμ : m'.μ = m.μ) (hd : m'.d = m.d) (hv : m'.v = m.v) (hQ0 : m'.Q0 = m.Q0)
    (hη : m'.η = 2 * Real.sqrt ε / m.S) (hS : 0 < m.S)
    (Y : ℝ → ℝ) (hY : IsVolterraSol m' Y) :
    0 < (∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s)) ∧
    ∃ û : ℝ, 0 < û ∧
      stepHit m' Y T ε = ENNReal.ofReal ((1 / m'.η) * ∫ u in (0:ℝ)..û, Real.sqrt (Y u)) ∧
      0 ≤ ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ∧
      (∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s)) - 2 * Real.sqrt (T * ε) / bmin
        ≤ ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ∧
      ∫ u in (0:ℝ)..û, Real.sqrt (Y u) ≤ (∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s))
        + 2 * Real.sqrt (Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε))
            * ∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s))
        + Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hm'F : ∀ s, m'.forcing s = m.forcing s := by
    intro s; unfold RowModel.forcing; rw [hμ, hd, hQ0]
  have hSm : m'.S = m.S := by unfold RowModel.S; rw [hμ, hv, hd]
  obtain ⟨a, ha⟩ : ∃ a : Fin (Fintype.card ι) → ℝ,
      ∀ i, a i = (1/2:ℝ) * (m.μ (e.symm i) * m.Q0 (e.symm i)) := ⟨_, fun _ => rfl⟩
  obtain ⟨b, hbe⟩ : ∃ b : Fin (Fintype.card ι) → ℝ,
      ∀ i, b i = 2 * m.d (e.symm i) := ⟨_, fun _ => rfl⟩
  obtain ⟨w, hwe⟩ : ∃ w : Fin (Fintype.card ι) → ℝ,
      ∀ l, w l = m.μ (e.symm l) * m.v (e.symm l) / (2 * m.d (e.symm l) * m.S) :=
    ⟨_, fun _ => rfl⟩
  obtain ⟨c, hce⟩ : ∃ c : Fin (Fintype.card ι) → ℝ,
      ∀ l, c l = 2 * m.d (e.symm l) := ⟨_, fun _ => rfl⟩
  have hFmix : ∀ u, mixF a b u = m.forcing u := by
    intro u
    unfold mixF RowModel.forcing
    rw [tsum_fintype, Finset.mul_sum]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm
      (fun j => (1/2:ℝ) * (m.μ j * m.Q0 j * Real.exp (-(2 * m.d j * u)))))
    exact Finset.sum_congr rfl fun i _ => by simp only [ha, hbe]; ring
  have hF0eq : m.F0 = ∑ i, a i := by
    unfold RowModel.F0
    rw [tsum_fintype, Finset.mul_sum]
    refine (Equiv.sum_comp e.symm (fun j => (1/2:ℝ) * (m.μ j * m.Q0 j))).symm.trans ?_
    exact Finset.sum_congr rfl fun i _ => by simp only [ha]
  have hkern : ∀ s, m'.kernel s = Real.sqrt ε * mixG w c s := by
    intro s
    have hsum_rhs : Real.sqrt ε * (∑ l, w l * c l * Real.exp (-(c l * s)))
        = ∑ j, (Real.sqrt ε / m.S) * (m.μ j * m.v j * Real.exp (-(2 * m.d j * s))) := by
      rw [Finset.mul_sum]
      refine Eq.trans ?_ (Equiv.sum_comp e.symm
        (fun j => (Real.sqrt ε / m.S) * (m.μ j * m.v j * Real.exp (-(2 * m.d j * s)))))
      refine Finset.sum_congr rfl fun l _ => ?_
      have hd0 : m.d (e.symm l) ≠ 0 := (m.d_pos (e.symm l)).ne'
      simp only [hwe, hce]
      field_simp
    unfold RowModel.kernel mixG
    rw [hη, hμ, hv, hd, tsum_fintype, hsum_rhs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hYpos : ∀ u ∈ Ici (0:ℝ), 0 < Y u := by
    intro u hu
    have h1 := thm_app_phase_volterra_iii m' Y hY u hu
    have h2 : 0 < m'.forcing u := h1.1
    exact lt_of_lt_of_le h2 h1.2.1
  have hYeq : ∀ u ∈ Ici (0:ℝ), Y u = mixF a b u
      + Real.sqrt ε * Muon.Foundations.oneSidedConv (fun v => Real.sqrt (Y v)) (mixG w c) u := by
    intro u hu
    rw [hY.2.2 u hu, hm'F, hFmix]
    congr 1
    unfold Muon.Foundations.oneSidedConv
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hkern]
    ring
  have hwsum : ∑ l, w l = 1 := by
    have hSsum : m.S = ∑ l, m.μ (e.symm l) * m.v (e.symm l) / (2 * m.d (e.symm l)) := by
      unfold RowModel.S
      rw [tsum_fintype]
      exact (Equiv.sum_comp e.symm (fun j => m.μ j * m.v j / (2 * m.d j))).symm
    have hx : ∑ l, w l = (∑ l, m.μ (e.symm l) * m.v (e.symm l) / (2 * m.d (e.symm l))) / m.S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun l _ => by rw [hwe l]; ring
    rw [hx, ← hSsum, div_self hS.ne']
  have hwnn : ∀ l, 0 ≤ w l := fun l => by
    rw [hwe l]
    exact div_nonneg (mul_nonneg (m.μ_pos _).le (m.v_nonneg _))
      (mul_nonneg (mul_nonneg (by norm_num) (m.d_pos _).le) hS.le)
  have hcnn : ∀ l, 0 < c l := fun l => by
    rw [hce l]; exact mul_pos two_pos (m.d_pos _)
  have hann : ∀ i, 0 ≤ a i := fun i => by
    rw [ha i]; exact mul_nonneg (by norm_num) (mul_nonneg (m.μ_pos _).le (m.Q0_nonneg _))
  have hbc : ∀ i, bmin ≤ b i := fun i => by rw [hbe i]; exact hb _
  have hcb : ∀ l, bmin ≤ c l := fun l => by rw [hce l]; exact hb _
  have hF0 : 0 < ∑ i, a i := by rw [← hF0eq]; exact m.F0_pos
  have hεF' : ε < (∑ i, a i) / T := by rw [← hF0eq]; exact hεF
  obtain ⟨hJ0, -, û, hfh, hû0, -, -, hlow, hup⟩ := lem_app_phase_mixture a b w c bmin hbmin
    hann hF0 hbc hwnn hwsum hcb hT hε hεF' (H := (2 / bmin) * Real.log ((∑ i, a i) / ε))
    (d := Real.sqrt ε * ((2 / bmin) * Real.log ((∑ i, a i) / ε))) rfl rfl hY.1 hYpos hYeq
  have hJeq : mixJ a b = ∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s) := by
    unfold mixJ; simp only [hFmix]
  rw [hJeq] at hJ0 hlow hup
  rw [← hF0eq] at hup
  have hSpos' : 0 < m'.S := by rw [hSm]; exact hS
  have hη' : m'.η = 2 * Real.sqrt ε / m'.S := by rw [hSm]; exact hη
  have hfin : firstHit Y (T * ε) ≠ ⊤ := by rw [hfh]; exact ENNReal.ofReal_ne_top
  have hclk := (thm_app_phase_hitting_i m' Y hY hSpos' ε hε hη' (T * ε)
    (mul_pos (by linarith) hε)).2.2 hfin
  rw [hfh, ENNReal.toReal_ofReal hû0.le] at hclk
  have hstep : stepHit m' Y T ε
      = ENNReal.ofReal ((1 / m'.η) * ∫ u in (0:ℝ)..û, Real.sqrt (Y u)) := by
    unfold stepHit
    rw [hclk]
    rfl
  have hI0 : 0 ≤ ∫ u in (0:ℝ)..û, Real.sqrt (Y u) :=
    intervalIntegral.integral_nonneg hû0.le (fun u _ => Real.sqrt_nonneg _)
  refine ⟨hJ0, û, hû0, hstep, hI0, ?_, ?_⟩
  · exact hlow
  · exact hup

/-- Label `thm:app-phase-fixed`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1339–1346):

```latex
\begin{theorem}[Fixed arrays]\label{thm:app-phase-fixed}
Assume (M1) with a finite index set and $\mathcal S>0$, take
$\lr=2\sqrt\epsilon/\mathcal S$, and fix $T\ge4$. As $\epsilon\downarrow0$ with all
other data fixed,
\[
t_{T\epsilon}\sim\frac{\mathcal S}{2\sqrt\epsilon}\int_0^\infty\sqrt{F(s)}\,\dif s,\qquad 0<\int_0^\infty\sqrt{F(s)}\,\dif s<\infty .
\]
\end{theorem}
```

Encoding: `m` fixes the arrays `μ, 𝔡, 𝔳, 𝔔(0)`; the matched models `mE ε` share them and carry
`η = 2√ε/𝒮` (`IsMatchedModel`); `Q ε` is a Volterra solution. The conjunct
`0 < ∫√F < ∞` is stated as positivity plus integrability (a Lean `∫` of a non-integrable
function is `0`). -/
theorem thm_app_phase_fixed {ι : Type*} [Finite ι] (m : RowModel ι) (hS : 0 < m.S)
    (T : ℝ) (hT : 4 ≤ T) (mE : ℝ → RowModel ι) (Q : ℝ → ℝ → ℝ)
    (hmE : ∀ ε : ℝ, 0 < ε → IsMatchedModel (PhaseArrays.mk m.μ m.d m.v m.Q0) (mE ε) ε)
    (hQ : ∀ ε : ℝ, 0 < ε → IsVolterraSol (mE ε) (Q ε)) :
    (0 < ∫ s in Ioi (0 : ℝ), Real.sqrt (m.forcing s) ∧
        IntegrableOn (fun s => Real.sqrt (m.forcing s)) (Ioi (0 : ℝ))) ∧
      IsEquivalent (𝓝[>] (0 : ℝ))
        (fun ε => (stepHit (mE ε) (Q ε) T ε).toReal)
        (fun ε => m.S / (2 * Real.sqrt ε) * ∫ s in Ioi (0 : ℝ), Real.sqrt (m.forcing s)) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  have hne : Nonempty ι := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 := m.F0_pos
    rw [tsum_empty, mul_zero] at h0
    exact lt_irrefl _ h0
  have : Nonempty ι := hne
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_min_image Finset.univ (fun i => 2 * m.d i) Finset.univ_nonempty
  obtain ⟨bmin, hbmin_def⟩ : ∃ bmin : ℝ, bmin = 2 * m.d i0 := ⟨_, rfl⟩
  have hbmin : 0 < bmin := by rw [hbmin_def]; exact mul_pos two_pos (m.d_pos i0)
  have hb : ∀ i, bmin ≤ 2 * m.d i := fun i => by
    rw [hbmin_def]; exact hi0 i (Finset.mem_univ i)
  have hF0pos : 0 < m.F0 := m.F0_pos
  have hT0 : 0 < T := by linarith
  have hev : Ioo (0:ℝ) (m.F0 / T) ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT (div_pos hF0pos hT0)
  obtain ⟨ε1, hε1⟩ := Filter.nonempty_of_mem hev
  have hJall := aux_fixed_hit m (mE ε1) T ε1 bmin hT hε1.1 hε1.2 hbmin hb
    (hmE ε1 hε1.1).1 (hmE ε1 hε1.1).2.1 (hmE ε1 hε1.1).2.2.1 (hmE ε1 hε1.1).2.2.2.1
    (hmE ε1 hε1.1).2.2.2.2 hS (Q ε1) (hQ ε1 hε1.1)
  have hJpos : 0 < ∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s) := hJall.1
  have hJint : IntegrableOn (fun s => Real.sqrt (m.forcing s)) (Ioi (0:ℝ)) := by
    by_contra hcon
    have h0 := integral_undef hcon
    linarith
  refine ⟨⟨hJpos, hJint⟩, ?_⟩
  obtain ⟨J, hJdef⟩ : ∃ J : ℝ, ∫ s in Ioi (0:ℝ), Real.sqrt (m.forcing s) = J := ⟨_, rfl⟩
  rw [hJdef] at hJpos ⊢
  have hJne : J ≠ 0 := hJpos.ne'
  have hsq : Tendsto (fun ε : ℝ => Real.sqrt (T * ε)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => Real.sqrt (T * ε)) (𝓝 0) (𝓝 0) := by
      have := (by fun_prop : Continuous fun ε : ℝ => Real.sqrt (T * ε)).tendsto 0
      simpa using this
    exact h.mono_left nhdsWithin_le_nhds
  have hsqrtε : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0)
    exact h.mono_left nhdsWithin_le_nhds
  have hψ : Tendsto (fun ε : ℝ => Real.log ε * ε ^ (1/2:ℝ)) (𝓝[>] (0:ℝ)) (𝓝 0) :=
    tendsto_log_mul_rpow_nhdsGT_zero (by norm_num)
  have hD : Tendsto (fun ε : ℝ => Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε)))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have hE : Tendsto (fun ε : ℝ => (2 / bmin) *
        (Real.sqrt ε * Real.log m.F0 - Real.log ε * ε ^ (1/2:ℝ))) (𝓝[>] (0:ℝ)) (𝓝 0) := by
      have := (((hsqrtε.mul_const (Real.log m.F0)).sub hψ).const_mul (2 / bmin))
      simpa using this
    refine Tendsto.congr' ?_ hE
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hεpos : 0 < ε := hε
    rw [Real.log_div hF0pos.ne' hεpos.ne', Real.sqrt_eq_rpow]
    ring
  have hsqDJ : Tendsto (fun ε : ℝ => Real.sqrt (Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε)) * J))
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h3 := (Real.continuous_sqrt.tendsto (0 * J)).comp (hD.mul_const J)
    rw [zero_mul, Real.sqrt_zero] at h3
    exact h3
  have hLlim : Tendsto (fun ε : ℝ => (J - 2 * Real.sqrt (T * ε) / bmin) / J)
      (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have := ((tendsto_const_nhds (x := J)).sub ((hsq.const_mul 2).div_const bmin)).div_const J
    simpa [hJne] using this
  have hUlim : Tendsto (fun ε : ℝ => (J + 2 * Real.sqrt (Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε)) * J)
      + Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε))) / J) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have := (((tendsto_const_nhds (x := J)).add (hsqDJ.const_mul 2)).add hD).div_const J
    simpa [hJne] using this
  have hbounds : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      (J - 2 * Real.sqrt (T * ε) / bmin) / J ≤
        (stepHit (mE ε) (Q ε) T ε).toReal / (m.S / (2 * Real.sqrt ε) * J) ∧
      (stepHit (mE ε) (Q ε) T ε).toReal / (m.S / (2 * Real.sqrt ε) * J) ≤
        (J + 2 * Real.sqrt (Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε)) * J)
          + Real.sqrt ε * (2 / bmin * Real.log (m.F0 / ε))) / J := by
    filter_upwards [hev] with ε hε
    have hεpos : 0 < ε := hε.1
    have hεF : ε < m.F0 / T := hε.2
    obtain ⟨-, û, hû0, hstep, hI0, hlow, hup⟩ := aux_fixed_hit m (mE ε) T ε bmin hT hεpos hεF
      hbmin hb (hmE ε hεpos).1 (hmE ε hεpos).2.1 (hmE ε hεpos).2.2.1 (hmE ε hεpos).2.2.2.1
      (hmE ε hεpos).2.2.2.2 hS (Q ε) (hQ ε hεpos)
    rw [hJdef] at hlow hup
    have hηε : (mE ε).η = 2 * Real.sqrt ε / m.S := (hmE ε hεpos).2.2.2.2
    have hfε : (stepHit (mE ε) (Q ε) T ε).toReal = (1 / (mE ε).η) * ∫ u in (0:ℝ)..û, Real.sqrt (Q ε u) := by
      rw [hstep, ENNReal.toReal_ofReal (mul_nonneg (one_div_pos.2 (mE ε).η_pos).le hI0)]
    have hSne : m.S / (2 * Real.sqrt ε) ≠ 0 :=
      div_ne_zero hS.ne' (mul_ne_zero two_ne_zero (Real.sqrt_pos.2 hεpos).ne')
    have key : (stepHit (mE ε) (Q ε) T ε).toReal / (m.S / (2 * Real.sqrt ε) * J)
        = (∫ u in (0:ℝ)..û, Real.sqrt (Q ε u)) / J := by
      rw [hfε, hηε, one_div_div, mul_div_mul_left _ _ hSne]
    rw [key]
    exact ⟨div_le_div_of_nonneg_right hlow hJpos.le, div_le_div_of_nonneg_right hup hJpos.le⟩
  refine isEquivalent_of_tendsto_one ?_
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hLlim hUlim
    (hbounds.mono fun ε hε => hε.1) (hbounds.mono fun ε hε => hε.2)

/-! ### Proof helpers for `cor:app-phase-fixed` (P-H.9.P2) -/

lemma wh_Hsum_pos (a : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < Hsum a N := by
  unfold Hsum
  apply Finset.sum_pos
  · intro i hi
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hi).1
    exact Real.rpow_pos_of_pos (by linarith) _
  · exact ⟨1, Finset.mem_Icc.2 ⟨le_rfl, hN⟩⟩

lemma wh_Hsum_ge_one (a : ℝ) {N : ℕ} (hN : 1 ≤ N) : 1 ≤ Hsum a N := by
  unfold Hsum
  have h := Finset.single_le_sum (f := fun i : ℕ => (i : ℝ) ^ (-a)) (s := Finset.Icc 1 N)
    (fun i _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) (a := 1)
    (Finset.mem_Icc.2 ⟨le_rfl, hN⟩)
  simpa using h

lemma wh_muBar_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < muBarOf α N := by
  unfold muBarOf
  exact div_pos (wh_Hsum_pos α hN) (by exact_mod_cast (show 0 < N by omega))

lemma wh_fixed_arrays {ι : Type*} (A : PhaseArrays ι) (m : RowModel ι)
    (hm : IsMatchedModel A m 1) : PhaseArrays.mk m.μ m.d m.v m.Q0 = A := by
  unfold IsMatchedModel at hm
  obtain ⟨h1, h2, h3, h4, -⟩ := hm
  cases A
  simp only [PhaseArrays.mk.injEq]
  exact ⟨h1, h2, h3, h4⟩

lemma wh_Lsum_term_summable (N : ℕ∞) (p q u : ℝ) (hp : 1 < p) (hu : 0 ≤ u) :
    Summable (fun i : ℕ => if 0 < i ∧ ((i : ℕ∞) ≤ N) then
      (i : ℝ) ^ (-p) * Real.exp (-(2 * u) * (i : ℝ) ^ (-q)) else 0) := by
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_)
    (Real.summable_nat_rpow.2 (by linarith : -p < -1))
  · split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
    · exact le_rfl
  · split_ifs
    · apply mul_le_of_le_one_right (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (i : ℝ) ^ (-q) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma wh_fNq_mono (N : ℕ∞) (p q1 q2 u : ℝ) (hp : 1 < p) (hu : 0 ≤ u) (hq : q2 ≤ q1) :
    fNq N p q2 u ≤ fNq N p q1 u := by
  unfold fNq Lsum
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  refine Summable.tsum_le_tsum (fun i => ?_) (wh_Lsum_term_summable N p q2 u hp hu)
    (wh_Lsum_term_summable N p q1 u hp hu)
  split_ifs with h
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    apply Real.exp_le_exp.2
    have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast h.1
    have h1 : (i : ℝ) ^ (-q1) ≤ (i : ℝ) ^ (-q2) :=
      Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
    have := mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * u)
    nlinarith
  · exact le_rfl

lemma wh_JN_mono (N : ℕ) (p α : ℝ) (hp : 1 < p) (hα : 0 < α)
    (hI1 : IntegrableOn (fun u => Real.sqrt (fNq (N : ℕ∞) p (α / 2) u)) (Ioi (0 : ℝ)))
    (hI2 : IntegrableOn (fun u => Real.sqrt (fNq (N : ℕ∞) p α u)) (Ioi (0 : ℝ))) :
    JN N p (α / 2) ≤ JN N p α := by
  unfold JN
  apply setIntegral_mono_on hI1 hI2 measurableSet_Ioi
  intro u hu
  exact Real.sqrt_le_sqrt (wh_fNq_mono N p α (α / 2) u hp (le_of_lt (Set.mem_Ioi.1 hu))
    (by linarith))

lemma wh_forcing_int (N : ℕ) (p q T0 : ℝ) (hT0 : 0 < T0) (F : ℝ → ℝ)
    (hF : ∀ u, 0 ≤ u → F (T0 * u) = fNq (N : ℕ∞) p q u) :
    ∫ s in Ioi (0 : ℝ), Real.sqrt (F s) = T0 * JN N p q := by
  have h := integral_comp_mul_left_Ioi (fun s => Real.sqrt (F s)) 0 hT0
  simp only [mul_zero] at h
  have h2 : ∫ x in Ioi (0 : ℝ), Real.sqrt (F (T0 * x)) = JN N p q := by
    unfold JN
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    simp only [hF x (le_of_lt (Set.mem_Ioi.1 hx))]
  calc ∫ s in Ioi (0 : ℝ), Real.sqrt (F s)
      = T0 * (T0⁻¹ • ∫ s in Ioi (0 : ℝ), Real.sqrt (F s)) := by
        rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hT0.ne', one_mul]
    _ = T0 * ∫ x in Ioi (0 : ℝ), Real.sqrt (F (T0 * x)) := by rw [h]
    _ = T0 * JN N p q := by rw [h2]

lemma wh_JN_integrable (N : ℕ) (p q T0 : ℝ) (hT0 : 0 < T0) (F : ℝ → ℝ)
    (hF : ∀ u, 0 ≤ u → F (T0 * u) = fNq (N : ℕ∞) p q u)
    (hint : IntegrableOn (fun s => Real.sqrt (F s)) (Ioi (0 : ℝ))) :
    IntegrableOn (fun u => Real.sqrt (fNq (N : ℕ∞) p q u)) (Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn (fun u => Real.sqrt (F (T0 * u))) (Ioi (0 : ℝ)) := by
    rw [integrableOn_Ioi_comp_mul_left_iff (fun s => Real.sqrt (F s)) 0 hT0]
    simpa using hint
  refine h1.congr_fun (fun u hu => ?_) measurableSet_Ioi
  show Real.sqrt (F (T0 * u)) = Real.sqrt (fNq (N : ℕ∞) p q u)
  rw [hF u (le_of_lt (Set.mem_Ioi.1 hu))]

lemma wh_phaseDN_nonneg (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ phaseDN α N :=
  div_nonneg (mul_nonneg Real.pi_pos.le (wh_Hsum_pos α hN).le) (wh_Hsum_pos (α / 2) hN).le

/-- Label `cor:app-phase-fixed`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1348–1356):

```latex
\begin{corollary}[Fixed dimension]\label{cor:app-phase-fixed}
For the arrays of \cref{def:app-phase-arrays} at fixed $N$, $B$, $\alpha$,
$\texp$ and $T\ge4$, as $\epsilon\downarrow0$,
\[
t^j_{T\epsilon}\sim\frac{\mathcal S_jT_0^j\,J_N(p,q_j)}{2\sqrt\epsilon},\qquad
\frac{t^{\text{s-SGD}}_{T\epsilon}}{t^{\text{s-SVD}}_{T\epsilon}}\longrightarrow D_N\,\frac{J_N(p,\alpha)}{J_N(p,\alpha/2)}\ge D_N .
\]
If $\alpha\ge4$, this limit exceeds $\pi/2$ for every $N$.
\end{corollary}
```

The `α ≥ 4` clause is the `√2`-sensitive clause of card §6.1 and is stated as written.
The `≥ D_N` clause is stated as written. -/
theorem cor_app_phase_fixed (α ς T : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς)
    (hN : 1 ≤ N) (hNB : N ≤ B) (hT : 4 ≤ T)
    (mS mG : ℝ → RowModel (Fin N)) (QS QG : ℝ → ℝ → ℝ)
    (hSv : ∀ ε : ℝ, 0 < ε → IsMatchedModel (svdArrays α ς N B) (mS ε) ε ∧
      IsVolterraSol (mS ε) (QS ε))
    (hSg : ∀ ε : ℝ, 0 < ε → IsMatchedModel (sgdArrays α ς N B) (mG ε) ε ∧
      IsVolterraSol (mG ε) (QG ε)) :
    IsEquivalent (𝓝[>] (0 : ℝ)) (fun ε => (stepHit (mS ε) (QS ε) T ε).toReal)
        (fun ε => (svdArrays α ς N B).S * svdT0 N B * JN N (α + ς) (α / 2) / (2 * Real.sqrt ε)) ∧
      IsEquivalent (𝓝[>] (0 : ℝ)) (fun ε => (stepHit (mG ε) (QG ε) T ε).toReal)
        (fun ε => (sgdArrays α ς N B).S * sgdT0 α N B * JN N (α + ς) α / (2 * Real.sqrt ε)) ∧
      Tendsto (fun ε => phaseR T ε (mS ε) (mG ε) (QS ε) (QG ε)) (𝓝[>] (0 : ℝ))
        (𝓝 (phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2))) ∧
      phaseDN α N ≤ phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2) ∧
      (4 ≤ α → Real.pi / 2 < phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hγ : 0 < gammaRat N B := div_pos hN0 hB0
  obtain ⟨hmS1, hQS1⟩ := hSv 1 one_pos
  obtain ⟨hmG1, hQG1⟩ := hSg 1 one_pos
  have hmEs : ∀ ε : ℝ, 0 < ε → IsMatchedModel
      (PhaseArrays.mk (mS 1).μ (mS 1).d (mS 1).v (mS 1).Q0) (mS ε) ε := fun ε hε => by
    rw [wh_fixed_arrays _ _ hmS1]; exact (hSv ε hε).1
  have hmGs : ∀ ε : ℝ, 0 < ε → IsMatchedModel
      (PhaseArrays.mk (mG 1).μ (mG 1).d (mG 1).v (mG 1).Q0) (mG ε) ε := fun ε hε => by
    rw [wh_fixed_arrays _ _ hmG1]; exact (hSg ε hε).1
  have hSm : (mS 1).S = (svdArrays α ς N B).S := congrArg PhaseArrays.S (wh_fixed_arrays _ _ hmS1)
  have hSgm : (mG 1).S = (sgdArrays α ς N B).S := congrArg PhaseArrays.S (wh_fixed_arrays _ _ hmG1)
  have hSvpos : 0 < (svdArrays α ς N B).S := by
    rw [(prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos).1]
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 hγ)) (wh_Hsum_pos (α / 2) hN)
  have hSgpos : 0 < (sgdArrays α ς N B).S := by
    rw [(prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos).2.2.1]
    exact mul_pos (div_pos (pow_pos hN0 2) two_pos)
      (Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos (wh_muBar_pos α hN)) hB0))
  have hT0s : 0 < svdT0 N B := by unfold svdT0; exact Real.sqrt_pos.2 hγ
  have hT0g : 0 < sgdT0 α N B := by
    unfold sgdT0
    exact Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos (wh_muBar_pos α hN)) hB0)
  obtain ⟨hfS, hfG, -, -, -, -⟩ := prop_app_phase_prefactors_ii α ς N B hα hp hN hNB 1 one_pos
    (mS 1) (mG 1) hmS1 hmG1 (QS 1) (QG 1) hQS1 hQG1
  obtain ⟨-, -, -, -, -, -, -, hDN⟩ := prop_app_phase_prefactors_i α ς N B hα hp hN hNB 1 one_pos
  have hTS := thm_app_phase_fixed (mS 1) (by rw [hSm]; exact hSvpos) T hT mS QS hmEs
    (fun ε hε => (hSv ε hε).2)
  have hTG := thm_app_phase_fixed (mG 1) (by rw [hSgm]; exact hSgpos) T hT mG QG hmGs
    (fun ε hε => (hSg ε hε).2)
  have hIS := wh_forcing_int N (α + ς) (α / 2) (svdT0 N B) hT0s (mS 1).forcing hfS
  have hIG := wh_forcing_int N (α + ς) α (sgdT0 α N B) hT0g (mG 1).forcing hfG
  have hJS : 0 < JN N (α + ς) (α / 2) := by
    have h := hTS.1.1
    rw [hIS] at h
    exact pos_of_mul_pos_right h hT0s.le
  have hJG : 0 < JN N (α + ς) α := by
    have h := hTG.1.1
    rw [hIG] at h
    exact pos_of_mul_pos_right h hT0g.le
  have hintS := wh_JN_integrable N (α + ς) (α / 2) (svdT0 N B) hT0s (mS 1).forcing hfS hTS.1.2
  have hintG := wh_JN_integrable N (α + ς) α (sgdT0 α N B) hT0g (mG 1).forcing hfG hTG.1.2
  have hJmono : JN N (α + ς) (α / 2) ≤ JN N (α + ς) α := wh_JN_mono N (α + ς) α hp hα hintS hintG
  have hEqS : Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ))
      (fun ε => (stepHit (mS ε) (QS ε) T ε).toReal)
      (fun ε => (svdArrays α ς N B).S * svdT0 N B * JN N (α + ς) (α / 2) / (2 * Real.sqrt ε)) := by
    have h := hTS.2
    rw [hSm, hIS] at h
    refine h.congr_right (Filter.Eventually.of_forall fun ε => ?_)
    dsimp only
    ring
  have hEqG : Asymptotics.IsEquivalent (𝓝[>] (0 : ℝ))
      (fun ε => (stepHit (mG ε) (QG ε) T ε).toReal)
      (fun ε => (sgdArrays α ς N B).S * sgdT0 α N B * JN N (α + ς) α / (2 * Real.sqrt ε)) := by
    have h := hTG.2
    rw [hSgm, hIG] at h
    refine h.congr_right (Filter.Eventually.of_forall fun ε => ?_)
    dsimp only
    ring
  have hdiv := hEqG.div hEqS
  have hlim : Tendsto (fun ε => phaseR T ε (mS ε) (mG ε) (QS ε) (QG ε)) (𝓝[>] (0 : ℝ))
      (𝓝 (phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2))) := by
    refine (hdiv.congr_right (w := Function.const ℝ
        (phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2))) ?_).tendsto_const
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    have hs : Real.sqrt ε ≠ 0 := (Real.sqrt_pos.2 hε').ne'
    have e1 : (sgdArrays α ς N B).S * sgdT0 α N B * JN N (α + ς) α / (2 * Real.sqrt ε)
        / ((svdArrays α ς N B).S * svdT0 N B * JN N (α + ς) (α / 2) / (2 * Real.sqrt ε))
        = (sgdArrays α ς N B).S * sgdT0 α N B / ((svdArrays α ς N B).S * svdT0 N B)
          * (JN N (α + ς) α / JN N (α + ς) (α / 2)) := by
      have := hSvpos.ne'
      have := hT0s.ne'
      have := hJS.ne'
      field_simp
    show (sgdArrays α ς N B).S * sgdT0 α N B * JN N (α + ς) α / (2 * Real.sqrt ε)
        / ((svdArrays α ς N B).S * svdT0 N B * JN N (α + ς) (α / 2) / (2 * Real.sqrt ε))
        = Function.const ℝ (phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2)) ε
    rw [e1, hDN]
    simp only [Function.const_apply]
    ring
  have hfourth : phaseDN α N ≤ phaseDN α N * JN N (α + ς) α / JN N (α + ς) (α / 2) := by
    have h1 : 1 ≤ JN N (α + ς) α / JN N (α + ς) (α / 2) := (one_le_div hJS).2 hJmono
    rw [mul_div_assoc]
    exact le_mul_of_one_le_right (wh_phaseDN_nonneg α hN) h1
  refine ⟨?_, ?_, hlim, hfourth, fun h4 => ?_⟩
  · exact hEqS
  · exact hEqG
  · have hH1 := wh_Hsum_ge_one α hN
    have hH2 : Hsum (α / 2) N < 2 := by
      have hle : Hsum (α / 2) N ≤ Hsum 2 N := by
        unfold Hsum
        apply Finset.sum_le_sum
        intro i hi
        have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hi).1
        exact Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)
      have hz := (lem_app_phase_harmonic_vi (a := (2 : ℝ)) (by norm_num) N hN).1
      have hv := lem_app_phase_harmonic_vii
      linarith
    have hphi : Real.pi / 2 < phaseDN α N := by
      unfold phaseDN
      rw [lt_div_iff₀ (wh_Hsum_pos (α / 2) hN)]
      nlinarith [mul_pos Real.pi_pos (sub_pos.2 hH2), mul_nonneg Real.pi_pos.le (sub_nonneg.2 hH1)]
    exact lt_of_lt_of_le hphi hfourth

/-! ## Limits of the ratio -/

/-! ### Proof helpers for `prop:app-phase-winners`(i) (P-H.9.P3) -/

lemma wh_int_pow {a : ℝ} (ha : a ≠ 1) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-a) = ((N : ℝ) ^ (1 - a) - 1) / (1 - a) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (N : ℝ) := by
    rw [Set.uIcc_of_le hN1]
    intro h
    linarith [h.1]
  have hr : -a ≠ -1 := by
    intro h
    apply ha
    linarith
  rw [integral_rpow (Or.inr ⟨hr, h0⟩), Real.one_rpow, show -a + 1 = 1 - a by ring]

lemma wh_H_lt1 {a : ℝ} (ha : 0 < a) (ha1 : a < 1) {N : ℕ} (hN : 1 ≤ N) :
    (N : ℝ) ^ (1 - a) ≤ Hsum a N ∧ Hsum a N ≤ (1 + 1 / (1 - a)) * (N : ℝ) ^ (1 - a) := by
  have hc : 0 < 1 - a := by linarith
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx1 : 1 ≤ (N : ℝ) ^ (1 - a) := Real.one_le_rpow hN1 hc.le
  refine ⟨lem_app_phase_harmonic_ii ha ha1.le N hN, ?_⟩
  have hup := (lem_app_phase_harmonic_i ha N hN).2
  rw [wh_int_pow (ne_of_lt ha1) hN] at hup
  have hdiv : ((N : ℝ) ^ (1 - a) - 1) * (1 / (1 - a)) ≤ (N : ℝ) ^ (1 - a) * (1 / (1 - a)) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e1 : ((N : ℝ) ^ (1 - a) - 1) / (1 - a) = ((N : ℝ) ^ (1 - a) - 1) * (1 / (1 - a)) := by
    ring
  have e2 : (1 + 1 / (1 - a)) * (N : ℝ) ^ (1 - a) = (N : ℝ) ^ (1 - a) + (N : ℝ) ^ (1 - a) * (1 / (1 - a)) := by
    ring
  rw [e1] at hup
  rw [e2]
  nlinarith [hdiv]

lemma wh_H_gt1 {a : ℝ} (ha : 1 < a) {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ Hsum a N ∧ Hsum a N ≤ 1 + 1 / (a - 1) := by
  refine ⟨wh_Hsum_ge_one a hN, ?_⟩
  have hup := (lem_app_phase_harmonic_i (by linarith : (0 : ℝ) < a) N hN).2
  rw [wh_int_pow (ne_of_gt ha) hN] at hup
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ (N : ℝ) ^ (1 - a) := Real.rpow_nonneg (by linarith) _
  have hsub : ((N : ℝ) ^ (1 - a) - 1) / (1 - a) = (1 - (N : ℝ) ^ (1 - a)) * (1 / (a - 1)) := by
    have : (1 : ℝ) - a ≠ 0 := by linarith
    have : (a : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hsub] at hup
  have : (1 - (N : ℝ) ^ (1 - a)) * (1 / (a - 1)) ≤ 1 / (a - 1) := by
    have hp : (0 : ℝ) < 1 / (a - 1) := by apply div_pos one_pos; linarith
    nlinarith
  linarith

lemma wh_H_eq1 {N : ℕ} (hN : 1 ≤ N) :
    Real.log (N : ℝ) ≤ Hsum 1 N ∧ Hsum 1 N ≤ 1 + Real.log (N : ℝ) := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  refine ⟨?_, ?_⟩
  · exact le_trans (Real.log_le_log hNpos (by linarith)) (lem_app_phase_harmonic_v N hN)
  · have hup := (lem_app_phase_harmonic_i (a := 1) one_pos N hN).2
    have hint : ∫ x in (1 : ℝ)..(N : ℝ), x ^ (-(1 : ℝ)) = Real.log N := by
      simp_rw [Real.rpow_neg_one]
      rw [integral_inv_of_pos one_pos hNpos, div_one]
    rw [hint] at hup
    exact hup

/-- Quotient sandwich: `L ≤ A ≤ U`, `a ≤ B ≤ b`, `0 < a`. -/
lemma wh_quot {A B L U a b : ℝ} (ha : 0 < a) (hL : 0 ≤ L) (hA1 : L ≤ A) (hA2 : A ≤ U)
    (hB1 : a ≤ B) (hB2 : B ≤ b) : L / b ≤ A / B ∧ A / B ≤ U / a := by
  constructor
  · exact div_le_div₀ (le_trans hL hA1) hA1 (lt_of_lt_of_le ha hB1) hB2
  · exact div_le_div₀ (le_trans hL (le_trans hA1 hA2)) hA2 ha hB1

lemma wh_D_lt1 {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N →
      c1 * (N : ℝ) ^ (-(α / 2)) ≤ phaseDN α N ∧ phaseDN α N ≤ c2 * (N : ℝ) ^ (-(α / 2)) := by
  have hβ : 0 < α / 2 := by linarith
  have hβ1 : α / 2 < 1 := by linarith
  have hcA1 : 1 ≤ 1 + 1 / (1 - α) := by
    have : 0 < 1 / (1 - α) := div_pos one_pos (by linarith)
    linarith
  have hcB1 : 1 ≤ 1 + 1 / (1 - α / 2) := by
    have : 0 < 1 / (1 - α / 2) := div_pos one_pos (by linarith)
    linarith
  have hcB : 0 < 1 + 1 / (1 - α / 2) := by linarith
  refine ⟨Real.pi / (1 + 1 / (1 - α / 2)), Real.pi * (1 + 1 / (1 - α)), ?_, ?_, ?_⟩
  · exact div_pos Real.pi_pos hcB
  · have h1 : Real.pi / (1 + 1 / (1 - α / 2)) ≤ Real.pi :=
      div_le_self Real.pi_pos.le hcB1
    have h2 : Real.pi ≤ Real.pi * (1 + 1 / (1 - α)) :=
      le_mul_of_one_le_right Real.pi_pos.le hcA1
    linarith
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hN' : 1 ≤ N := by omega
  set X := (N : ℝ) ^ (1 - α / 2) with hXdef
  set Y := (N : ℝ) ^ (-(α / 2)) with hYdef
  have hX : 0 < X := Real.rpow_pos_of_pos hNpos _
  have hY : 0 < Y := Real.rpow_pos_of_pos hNpos _
  have hXY : (N : ℝ) ^ (1 - α) = Y * X := by
    rw [hXdef, hYdef, ← Real.rpow_add hNpos]
    congr 1
    ring
  have hA := wh_H_lt1 hα hα1 hN'
  have hB := wh_H_lt1 hβ hβ1 hN'
  rw [← hXdef] at hB
  have hq := wh_quot hX (by positivity) hA.1 hA.2 hB.1 hB.2
  rw [hXY] at hq hA
  unfold phaseDN
  rw [mul_div_assoc]
  have k1 : Real.pi / (1 + 1 / (1 - α / 2)) * Y =
      Real.pi * (Y * X / ((1 + 1 / (1 - α / 2)) * X)) := by
    field_simp
  have k2 : Real.pi * ((1 + 1 / (1 - α)) * (Y * X) / X) = Real.pi * (1 + 1 / (1 - α)) * Y := by
    field_simp
  constructor
  · rw [k1]
    exact mul_le_mul_of_nonneg_left hq.1 Real.pi_pos.le
  · rw [← k2]
    exact mul_le_mul_of_nonneg_left hq.2 Real.pi_pos.le

lemma wh_D_eq1 {α : ℝ} (hα : α = 1) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N →
      c1 * (Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2))) ≤ phaseDN α N ∧
        phaseDN α N ≤ c2 * (Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2))) := by
  subst hα
  have hβ : 0 < (1 : ℝ) / 2 := by norm_num
  have hβ1 : (1 : ℝ) / 2 < 1 := by norm_num
  have hcB : 0 < 1 + 1 / (1 - (1:ℝ) / 2) := by norm_num
  have hcB1 : 1 ≤ 1 + 1 / (1 - (1:ℝ) / 2) := by norm_num
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C := 1 + 1 / Real.log 2 with hCdef
  have hC1 : 1 ≤ C := by
    have : 0 < 1 / Real.log 2 := div_pos one_pos hl2
    linarith
  refine ⟨Real.pi / (1 + 1 / (1 - (1:ℝ) / 2)), Real.pi * C, div_pos Real.pi_pos hcB, ?_, ?_⟩
  · have h1 : Real.pi / (1 + 1 / (1 - (1:ℝ) / 2)) ≤ Real.pi := div_le_self Real.pi_pos.le hcB1
    have h2 : Real.pi ≤ Real.pi * C := le_mul_of_one_le_right Real.pi_pos.le hC1
    linarith
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN' : 1 ≤ N := by omega
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log two_pos hN2
  set X := (N : ℝ) ^ (1 - (1:ℝ) / 2) with hXdef
  set Y := (N : ℝ) ^ (-((1:ℝ) / 2)) with hYdef
  have hX : 0 < X := Real.rpow_pos_of_pos hNpos _
  have hXY : Y * X = 1 := by
    rw [hXdef, hYdef, ← Real.rpow_add hNpos]
    norm_num
  have hY' : Y = 1 / X := (eq_div_iff hX.ne').mpr hXY
  have hA := wh_H_eq1 hN'
  have hB := wh_H_lt1 hβ hβ1 hN'
  rw [← hXdef] at hB
  have hq := wh_quot hX (Real.log_nonneg (by linarith)) hA.1 hA.2 hB.1 hB.2
  unfold phaseDN
  rw [mul_div_assoc]
  have hC : 1 + Real.log (N : ℝ) ≤ C * Real.log (N : ℝ) := by
    have : 1 ≤ (1 / Real.log 2) * Real.log (N : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl2]
      linarith
    rw [hCdef, add_mul, one_mul]
    linarith
  have k1 : Real.pi / (1 + 1 / (1 - (1:ℝ) / 2)) * (Real.log (N : ℝ) * Y) =
      Real.pi * (Real.log (N : ℝ) / ((1 + 1 / (1 - (1:ℝ) / 2)) * X)) := by
    rw [hY']
    field_simp
  have k2 : Real.pi * ((1 + Real.log (N : ℝ)) / X) ≤ Real.pi * C * (Real.log (N : ℝ) * Y) := by
    rw [hY']
    have : (1 + Real.log (N : ℝ)) / X ≤ C * Real.log (N : ℝ) * (1 / X) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right hC hX.le
    have e : Real.pi * C * (Real.log (N : ℝ) * (1 / X)) = Real.pi * (C * Real.log (N : ℝ) * (1 / X)) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left this Real.pi_pos.le
  constructor
  · rw [k1]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact hq.1
  · refine le_trans ?_ k2
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact hq.2

lemma wh_D_eq2 {α : ℝ} (hα : α = 2) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N →
      c1 * ((N : ℝ) / Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2))) ≤ phaseDN α N ∧
        phaseDN α N ≤ c2 * ((N : ℝ) / Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2))) := by
  subst hα
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set C := 1 + 1 / Real.log 2 with hCdef
  have hC1 : 1 ≤ C := by
    have : 0 < 1 / Real.log 2 := div_pos one_pos hl2
    linarith
  refine ⟨Real.pi / C, 2 * Real.pi, div_pos Real.pi_pos (by linarith), ?_, ?_⟩
  · have h1 : Real.pi / C ≤ Real.pi := div_le_self Real.pi_pos.le hC1
    linarith [Real.pi_pos]
  intro N hN
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN' : 1 ≤ N := by omega
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (N : ℝ) := Real.log_le_log two_pos hN2
  have hYe : (N : ℝ) ^ (-((2:ℝ) / 2)) = 1 / (N : ℝ) := by
    norm_num [Real.rpow_neg_one]
  rw [hYe]
  have hG : (N : ℝ) / Real.log (N : ℝ) * (1 / (N : ℝ)) = 1 / Real.log (N : ℝ) := by
    field_simp
  rw [hG]
  have hA := wh_H_gt1 (a := 2) (by norm_num) hN'
  have hB := wh_H_eq1 hN'
  have hq := wh_quot (A := Hsum 2 N) (B := Hsum 1 N) (L := 1) (U := 1 + 1 / (2 - 1))
    (a := Real.log (N : ℝ)) (b := 1 + Real.log (N : ℝ)) hlogpos (by norm_num) hA.1 hA.2 hB.1 hB.2
  unfold phaseDN
  rw [show (2 : ℝ) / 2 = 1 by norm_num, mul_div_assoc]
  have hC : 1 + Real.log (N : ℝ) ≤ C * Real.log (N : ℝ) := by
    have : 1 ≤ (1 / Real.log 2) * Real.log (N : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hl2]
      linarith
    rw [hCdef, add_mul, one_mul]
    linarith
  constructor
  · have e1 : Real.pi / C * (1 / Real.log (N : ℝ)) = Real.pi * (1 / (C * Real.log (N : ℝ))) := by
      field_simp
    have e2 : 1 / (C * Real.log (N : ℝ)) ≤ 1 / (1 + Real.log (N : ℝ)) :=
      one_div_le_one_div_of_le (by linarith) hC
    rw [e1]
    apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
    exact le_trans e2 hq.1
  · have e3 : (1 + 1 / (2 - 1 : ℝ)) / Real.log (N : ℝ) = 2 * (1 / Real.log (N : ℝ)) := by
      norm_num
      ring
    have hq2 : Hsum 2 N / Hsum 1 N ≤ 2 * (1 / Real.log (N : ℝ)) := by
      rw [← e3]
      exact hq.2
    calc Real.pi * (Hsum 2 N / Hsum 1 N) ≤ Real.pi * (2 * (1 / Real.log (N : ℝ))) :=
          mul_le_mul_of_nonneg_left hq2 Real.pi_pos.le
      _ = 2 * Real.pi * (1 / Real.log (N : ℝ)) := by ring

lemma wh_D_mid {α : ℝ} (hα1 : 1 < α) (hα2 : α < 2) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N →
      c1 * ((N : ℝ) ^ (α - 1) * (N : ℝ) ^ (-(α / 2))) ≤ phaseDN α N ∧
        phaseDN α N ≤ c2 * ((N : ℝ) ^ (α - 1) * (N : ℝ) ^ (-(α / 2))) := by
  have hβ : 0 < α / 2 := by linarith
  have hβ1 : α / 2 < 1 := by linarith
  have hcA1 : 1 ≤ 1 + 1 / (α - 1) := by
    have : 0 < 1 / (α - 1) := div_pos one_pos (by linarith)
    linarith
  have hcB1 : 1 ≤ 1 + 1 / (1 - α / 2) := by
    have : 0 < 1 / (1 - α / 2) := div_pos one_pos (by linarith)
    linarith
  have hcB : 0 < 1 + 1 / (1 - α / 2) := by linarith
  refine ⟨Real.pi / (1 + 1 / (1 - α / 2)), Real.pi * (1 + 1 / (α - 1)), div_pos Real.pi_pos hcB,
    ?_, ?_⟩
  · have h1 : Real.pi / (1 + 1 / (1 - α / 2)) ≤ Real.pi := div_le_self Real.pi_pos.le hcB1
    have h2 : Real.pi ≤ Real.pi * (1 + 1 / (α - 1)) := le_mul_of_one_le_right Real.pi_pos.le hcA1
    linarith
  intro N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hNpos : (0 : ℝ) < N := by linarith
  have hN' : 1 ≤ N := by omega
  set X := (N : ℝ) ^ (1 - α / 2) with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hNpos _
  have hZ : (N : ℝ) ^ (α - 1) * (N : ℝ) ^ (-(α / 2)) = 1 / X := by
    rw [eq_div_iff hX.ne', hXdef, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
    rw [show α - 1 + -(α / 2) + (1 - α / 2) = 0 by ring, Real.rpow_zero]
  rw [hZ]
  have hA := wh_H_gt1 (by linarith : 1 < α) hN'
  have hB := wh_H_lt1 hβ hβ1 hN'
  rw [← hXdef] at hB
  have hq := wh_quot hX zero_le_one hA.1 hA.2 hB.1 hB.2
  unfold phaseDN
  rw [mul_div_assoc]
  constructor
  · have e1 : Real.pi / (1 + 1 / (1 - α / 2)) * (1 / X) =
        Real.pi * (1 / ((1 + 1 / (1 - α / 2)) * X)) := by
      field_simp
    rw [e1]
    exact mul_le_mul_of_nonneg_left hq.1 Real.pi_pos.le
  · have e2 : Real.pi * (1 + 1 / (α - 1)) * (1 / X) =
        Real.pi * ((1 + 1 / (α - 1)) / X) := by
      ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hq.2 Real.pi_pos.le

lemma wh_D_gt2 {α : ℝ} (hα2 : 2 < α) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ c1 ≤ c2 ∧ ∀ N : ℕ, 2 ≤ N →
      c1 * 1 ≤ phaseDN α N ∧ phaseDN α N ≤ c2 * 1 := by
  have hβ1 : 1 < α / 2 := by linarith
  have hpos1 : 0 < 1 / (α / 2 - 1) := div_pos one_pos (by linarith)
  have hpos2 : 0 < 1 / (α - 1) := div_pos one_pos (by linarith)
  have hcB1 : 1 / (1 + 1 / (α / 2 - 1)) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  refine ⟨Real.pi * (1 / (1 + 1 / (α / 2 - 1))), Real.pi * (1 + 1 / (α - 1)),
    mul_pos Real.pi_pos (div_pos one_pos (by linarith)), ?_, ?_⟩
  · have h1 : Real.pi * (1 / (1 + 1 / (α / 2 - 1))) ≤ Real.pi * 1 :=
      mul_le_mul_of_nonneg_left hcB1 Real.pi_pos.le
    have h2 : Real.pi * 1 ≤ Real.pi * (1 + 1 / (α - 1)) :=
      mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le
    linarith
  intro N hN
  have hN' : 1 ≤ N := by omega
  have hA := wh_H_gt1 (by linarith : 1 < α) hN'
  have hB := wh_H_gt1 hβ1 hN'
  have hq := wh_quot (A := Hsum α N) (B := Hsum (α / 2) N) (L := 1) (U := 1 + 1 / (α - 1))
    (a := 1) (b := 1 + 1 / (α / 2 - 1)) one_pos zero_le_one hA.1 hA.2 hB.1 hB.2
  unfold phaseDN
  rw [mul_div_assoc]
  constructor
  · rw [mul_one]
    exact mul_le_mul_of_nonneg_left hq.1 Real.pi_pos.le
  · have hq2 := hq.2
    rw [div_one] at hq2
    rw [mul_one]
    exact mul_le_mul_of_nonneg_left hq2 Real.pi_pos.le

lemma wh_exp (α ς : ℝ) (hα : 0 < α) (hp : 0 < α + ς - 1) :
    -(1 / (2 * ((α + ς - 1) / α))) = -(α / (2 * (α + ς - 1))) := by
  congr 1
  field_simp

lemma wh_Xi (α ς : ℝ) (hα : 0 < α) (hp : 0 < α + ς - 1) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (ε * (N : ℝ) ^ (α + ς - 1)) ^ (-(1 / (2 * ((α + ς - 1) / α))))
      = ε ^ (-(α / (2 * (α + ς - 1)))) * (N : ℝ) ^ (-(α / 2)) := by
  rw [wh_exp α ς hα hp, Real.mul_rpow hε.le (Real.rpow_nonneg (Nat.cast_nonneg _) _),
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 2
  field_simp

lemma wh_fin {D G E W c1 c2 : ℝ} (hE : 0 < E) (hW : W = G * E)
    (h1 : c1 * G ≤ D) (h2 : D ≤ c2 * G) : c1 * W ≤ D * E ∧ D * E ≤ c2 * W := by
  rw [hW]
  constructor
  · calc c1 * (G * E) = (c1 * G) * E := by ring
      _ ≤ D * E := mul_le_mul_of_nonneg_right h1 hE.le
  · calc D * E ≤ (c2 * G) * E := mul_le_mul_of_nonneg_right h2 hE.le
      _ = c2 * (G * E) := by ring

lemma wh_W_lt1 (α ς : ℝ) (hα : 0 < α) (hα1 : α < 1) (hp : 0 < α + ς - 1) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    winnersRateI α ς N ε = (N : ℝ) ^ (-(α / 2)) * ε ^ (-(α / (2 * (α + ς - 1)))) := by
  dsimp only [winnersRateI]
  rw [if_pos hα1, wh_Xi α ς hα hp N ε hε]
  ring

lemma wh_W_eq1 (α ς : ℝ) (hα : α = 1) (hp : 0 < α + ς - 1) (N : ℕ) (ε : ℝ) (hε : 0 < ε) :
    winnersRateI α ς N ε = Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2)) *
      ε ^ (-(α / (2 * (α + ς - 1)))) := by
  have hαpos : 0 < α := by rw [hα]; norm_num
  dsimp only [winnersRateI]
  rw [if_neg (by rw [hα]; norm_num), if_pos hα, wh_Xi α ς hαpos hp N ε hε]
  ring

lemma wh_W_mid (α ς : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hp : 0 < α + ς - 1) (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    winnersRateI α ς N ε = (N : ℝ) ^ (α - 1) * (N : ℝ) ^ (-(α / 2)) *
      ε ^ (-(α / (2 * (α + ς - 1)))) := by
  have hαpos : 0 < α := by linarith
  dsimp only [winnersRateI]
  rw [if_neg (not_lt.mpr hα1.le), if_neg (ne_of_gt hα1), if_pos hα2,
    wh_Xi α ς hαpos hp N ε hε]
  ring

lemma wh_W_eq2 (α ς : ℝ) (hα : α = 2) (hp : 0 < α + ς - 1) (N : ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    winnersRateI α ς N ε = (N : ℝ) / Real.log (N : ℝ) * (N : ℝ) ^ (-(α / 2)) *
      ε ^ (-(α / (2 * (α + ς - 1)))) := by
  have hαpos : 0 < α := by rw [hα]; norm_num
  dsimp only [winnersRateI]
  rw [if_neg (by rw [hα]; norm_num), if_neg (by rw [hα]; norm_num),
    if_neg (by rw [hα]; norm_num), if_pos hα, wh_Xi α ς hαpos hp N ε hε]
  ring

lemma wh_W_gt2 (α ς : ℝ) (hα : 0 < α) (hα2 : 2 < α) (hp : 0 < α + ς - 1) (N : ℕ)
    (ε : ℝ) :
    winnersRateI α ς N ε = 1 * ε ^ (-(α / (2 * (α + ς - 1)))) := by
  dsimp only [winnersRateI]
  rw [if_neg (not_lt.mpr (by linarith : (1:ℝ) ≤ α)), if_neg (ne_of_gt (by linarith : 1 < α)),
    if_neg (not_lt.mpr hα2.le), if_neg (ne_of_gt hα2), one_mul, wh_exp α ς hα hp]

lemma wh_K (α ς : ℝ) (hα : 0 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1) :
    ∃ dLo dHi : ℝ, 0 < dLo ∧ dLo ≤ dHi ∧ ∀ N : ℕ, 2 ≤ N → ∀ ε : ℝ, 0 < ε →
      dLo * winnersRateI α ς N ε ≤ phaseDN α N * phaseRatioRate α ς ε ∧
        phaseDN α N * phaseRatioRate α ς ε ≤ dHi * winnersRateI α ς N ε := by
  have hp : 0 < α + ς - 1 := by linarith
  have hPR : ∀ ε : ℝ, phaseRatioRate α ς ε = ε ^ (-(α / (2 * (α + ς - 1)))) := by
    intro ε
    unfold phaseRatioRate
    rw [if_pos hς₂]
  by_cases h1 : α < 1
  · obtain ⟨c1, c2, hc1, hc12, hD⟩ := wh_D_lt1 hα h1
    refine ⟨c1, c2, hc1, hc12, fun N hN ε hε => ?_⟩
    rw [hPR ε]
    exact wh_fin (Real.rpow_pos_of_pos hε _) (wh_W_lt1 α ς hα h1 hp N ε hε)
      (hD N hN).1 (hD N hN).2
  by_cases h2 : α = 1
  · obtain ⟨c1, c2, hc1, hc12, hD⟩ := wh_D_eq1 h2
    refine ⟨c1, c2, hc1, hc12, fun N hN ε hε => ?_⟩
    rw [hPR ε]
    exact wh_fin (Real.rpow_pos_of_pos hε _) (wh_W_eq1 α ς h2 hp N ε hε)
      (hD N hN).1 (hD N hN).2
  have hα1 : 1 < α := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2)
  by_cases h3 : α < 2
  · obtain ⟨c1, c2, hc1, hc12, hD⟩ := wh_D_mid hα1 h3
    refine ⟨c1, c2, hc1, hc12, fun N hN ε hε => ?_⟩
    rw [hPR ε]
    exact wh_fin (Real.rpow_pos_of_pos hε _) (wh_W_mid α ς hα1 h3 hp N ε hε)
      (hD N hN).1 (hD N hN).2
  by_cases h4 : α = 2
  · obtain ⟨c1, c2, hc1, hc12, hD⟩ := wh_D_eq2 h4
    refine ⟨c1, c2, hc1, hc12, fun N hN ε hε => ?_⟩
    rw [hPR ε]
    exact wh_fin (Real.rpow_pos_of_pos hε _) (wh_W_eq2 α ς h4 hp N ε hε)
      (hD N hN).1 (hD N hN).2
  have hα2 : 2 < α := lt_of_le_of_ne (not_lt.mp h3) (Ne.symm h4)
  obtain ⟨c1, c2, hc1, hc12, hD⟩ := wh_D_gt2 hα2
  refine ⟨c1, c2, hc1, hc12, fun N hN ε hε => ?_⟩
  rw [hPR ε, wh_W_gt2 α ς hα hα2 hp N ε]
  exact wh_fin (G := 1) (Real.rpow_pos_of_pos hε _) (by ring) (hD N hN).1 (hD N hN).2

lemma wh_comb {X y cLo cHi dLo dHi W : ℝ} (hc : 0 < cLo) (hcc : cLo ≤ cHi)
    (hs : Sandwich (cLo / cHi) (cHi / cLo) X y) (hk : dLo * W ≤ X ∧ X ≤ dHi * W) :
    Sandwich (cLo / cHi * dLo) (cHi / cLo * dHi) W y := by
  unfold Sandwich at hs ⊢
  obtain ⟨s1, s2⟩ := hs
  obtain ⟨k1, k2⟩ := hk
  have hp1 : 0 ≤ cLo / cHi := div_nonneg hc.le (hc.trans_le hcc).le
  have hp2 : 0 ≤ cHi / cLo := div_nonneg (hc.trans_le hcc).le hc.le
  constructor
  · calc cLo / cHi * dLo * W = (cLo / cHi) * (dLo * W) := by ring
      _ ≤ (cLo / cHi) * X := mul_le_mul_of_nonneg_left k1 hp1
      _ ≤ y := s1
  · calc y ≤ (cHi / cLo) * X := s2
      _ ≤ (cHi / cLo) * (dHi * W) := mul_le_mul_of_nonneg_left k2 hp2
      _ = cHi / cLo * dHi * W := by ring

lemma wh_W_small (α ς : ℝ) (hα1 : α < 1) (N : ℕ) (ε : ℝ) :
    winnersRateI α ς N ε = (ε * (N : ℝ) ^ (α + ς - 1)) ^ (-(1 / (2 * ((α + ς - 1) / α)))) := by
  dsimp only [winnersRateI]
  rw [if_pos hα1]

lemma wh_W_one (ς : ℝ) (N : ℕ) (ε : ℝ) :
    winnersRateI 1 ς N ε = Real.log (N : ℝ) * (ε * (N : ℝ) ^ (1 + ς - 1)) ^
      (-(1 / (2 * ((1 + ς - 1) / 1)))) := by
  dsimp only [winnersRateI]
  rw [if_neg (by norm_num), if_pos rfl]

/-- Label `prop:app-phase-winners`, part (i), the `≍` display for the range `ς < 1`
(window of `thm:app-phase-A`). Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The constants of the `≍` are existential after the window hypothesis `PhaseAWindowHolds` and
before all `(N, B, ε)`. The table is `winnersRateI`. The bound is stated for `N ≥ 2`: the
`α = 1` and `α = 2` rows contain `log N`, which is `0` at `N = 1`, so the `≍` is not meaningful there
(correction, recorded in `CORRECTIONS.md` by the coordinator). -/
theorem prop_app_phase_winners_i (α ς T : ℝ) (hα : 0 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseAWindowHolds α ς T Nst Est cLo cHi) :
    ∃ dLo dHi : ℝ, 0 < dLo ∧ dLo ≤ dHi ∧
      ∀ (N B : ℕ) (ε : ℝ) (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ),
        PhaseWinA α ς T Nst Est N B ε → 2 ≤ N →
        IsMatchedModel (svdArrays α ς N B) mS ε → IsVolterraSol mS QS →
        IsMatchedModel (sgdArrays α ς N B) mG ε → IsVolterraSol mG QG →
        Sandwich dLo dHi (winnersRateI α ς N ε) (phaseR T ε mS mG QS QG) := by
  obtain ⟨dLo, dHi, hdLo, hdLoHi, hK⟩ := wh_K α ς hα hς₁ hς₂
  have hc0 : 0 < cLo := hW.1
  have hcc : cLo ≤ cHi := hW.2.1
  refine ⟨cLo / cHi * dLo, cHi / cLo * dHi, ?_, ?_, ?_⟩
  · exact mul_pos (div_pos hc0 (hc0.trans_le hcc)) hdLo
  · have h1 : cLo / cHi ≤ cHi / cLo := by
      rw [div_le_div_iff₀ (hc0.trans_le hcc) hc0]
      nlinarith
    have h2 : 0 ≤ cHi / cLo := div_nonneg (hc0.trans_le hcc).le hc0.le
    have h3 : 0 ≤ cLo / cHi := div_nonneg hc0.le (hc0.trans_le hcc).le
    calc cLo / cHi * dLo ≤ cHi / cLo * dLo := mul_le_mul_of_nonneg_right h1 hdLo.le
      _ ≤ cHi / cLo * dHi := mul_le_mul_of_nonneg_left hdLoHi h2
  · intro N B ε mS mG QS QG hwin hN hS hQS hG hQG
    have hε : 0 < ε := hwin.2.2.1
    have hcor := cor_app_phase_ratio_i α ς T hα hς₁ hς₂ hT Nst Est cLo cHi hW N B ε mS mG QS QG
      hwin hS hQS hG hQG
    exact wh_comb hc0 hcc hcor (hK N hN ε hε)

/-- Label `prop:app-phase-winners`, part (i), limit `𝖱 → 0` for `0 < α < 1`. Snapshot
`cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The sequence hypothesis is `εN^{p-1} → ∞`, the sequence form of the window of
`thm:app-phase-A` (its sequence clause); the window is then derived from `hW`.

Correction: the source's literal claim `𝖱 → 0` for `0 < α < 1` is false without the
divergence `εN^{p-1} → ∞` (on the window alone, `Ξ_N ≥ E_*` only bounds `𝖱`). The hypothesis
is added here; the entry is recorded in `CORRECTIONS.md` (added by the coordinator). -/
theorem prop_app_phase_winners_i_zero (α ς T : ℝ) (hα : 0 < α) (hα1 : α < 1)
    (hς₁ : 1 - α < ς) (hς₂ : ς < 1) (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseAWindowHolds α ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      Tendsto (fun n => εs n * (Nseq n : ℝ) ^ (α + ς - 1)) atTop atTop →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) := by
  intro Nseq Bseq εs mS mG QS QG hMS hΞ
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hc0 : 0 < cLo := hW.1
  have hcc : cLo ≤ cHi := hW.2.1
  obtain ⟨dLo, dHi, -, -, hK⟩ := wh_K α ς hα hς₁ hς₂
  have hev : ∀ᶠ n in atTop, PhaseWinA α ς T Nst Est (Nseq n) (Bseq n) (εs n) :=
    hW.2.2.2.1 Nseq Bseq εs hN hεT hεpos hN1 hNB hΞ
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hev2 : ∀ᶠ n in atTop, 2 ≤ Nseq n := hNℕ.eventually_ge_atTop 2
  have hcpos : 0 < 1 / (2 * ((α + ς - 1) / α)) := by
    apply div_pos one_pos
    apply mul_pos two_pos
    exact div_pos (by linarith) hα
  have hW0 : Tendsto (fun n => winnersRateI α ς (Nseq n) (εs n)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop hcpos).comp hΞ
    refine Tendsto.congr (fun n => ?_) h
    exact (wh_W_small α ς hα1 (Nseq n) (εs n)).symm
  have hUp : Tendsto (fun n => cHi / cLo * dHi * winnersRateI α ς (Nseq n) (εs n)) atTop (𝓝 0) := by
    have := hW0.const_mul (cHi / cLo * dHi)
    rwa [mul_zero] at this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp
  · exact Filter.Eventually.of_forall fun n => by
      unfold phaseR
      exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · filter_upwards [hev, hev2] with n hn hn2
    have hcor := cor_app_phase_ratio_i α ς T hα hς₁ hς₂ hT Nst Est cLo cHi hW (Nseq n) (Bseq n)
      (εs n) (mS n) (mG n) (QS n) (QG n) hn (hSm n) (hSV n) (hGm n) (hGV n)
    have hcomb := wh_comb hc0 hcc hcor (hK (Nseq n) hn2 (εs n) (hεpos n))
    exact hcomb.2

/-- Label `prop:app-phase-winners`, part (i), the case `α = 1` with
`ε_N = N^{-r}(log N)^b`, `b > 0`, `r = r_{s-SVD} = (p-1)/α`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The sequence lies in the window for all large indices (part of the claim, derived from `hW`). -/
theorem prop_app_phase_winners_i_alpha1 (ς T b : ℝ) (hς₁ : 0 < ς) (hς₂ : ς < 1) (hb : 0 < b)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseAWindowHolds 1 ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq 1 ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, εs n = logPowEps ((1 + ς - 1) / 1) b (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinA 1 ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      (b < 2 * ((1 + ς - 1) / 1) →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) ∧
      (2 * ((1 + ς - 1) / 1) < b →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) := by
  intro Nseq Bseq εs mS mG QS QG hMS hform
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hc0 : 0 < cLo := hW.1
  have hcc : cLo ≤ cHi := hW.2.1
  obtain ⟨dLo, dHi, hdLo, -, hK⟩ := wh_K 1 ς one_pos (by linarith) hς₂
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hev2 : ∀ᶠ n in atTop, 2 ≤ Nseq n := hNℕ.eventually_ge_atTop 2
  have hLog : Tendsto (fun n => Real.log (Nseq n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hN
  have hXi : ∀ᶠ n in atTop, εs n * (Nseq n : ℝ) ^ (1 + ς - 1) = Real.log (Nseq n : ℝ) ^ b := by
    filter_upwards [hform, hev2] with n hn hn2
    have hN2 : (2 : ℝ) ≤ Nseq n := by exact_mod_cast hn2
    have hNpos : (0 : ℝ) < Nseq n := by linarith
    rw [hn]
    unfold logPowEps
    have hid : (Nseq n : ℝ) ^ (-((1 + ς - 1) / 1)) * (Nseq n : ℝ) ^ (1 + ς - 1) = 1 := by
      rw [← Real.rpow_add hNpos, show -((1 + ς - 1) / 1) + (1 + ς - 1) = (0 : ℝ) by ring,
        Real.rpow_zero]
    calc (Nseq n : ℝ) ^ (-((1 + ς - 1) / 1)) * Real.log (Nseq n : ℝ) ^ b * (Nseq n : ℝ) ^ (1 + ς - 1)
        = ((Nseq n : ℝ) ^ (-((1 + ς - 1) / 1)) * (Nseq n : ℝ) ^ (1 + ς - 1)) *
            Real.log (Nseq n : ℝ) ^ b := by ring
      _ = Real.log (Nseq n : ℝ) ^ b := by rw [hid, one_mul]
  have hΞ : Tendsto (fun n => εs n * (Nseq n : ℝ) ^ (1 + ς - 1)) atTop atTop :=
    Tendsto.congr' (hXi.mono fun n hn => hn.symm) ((tendsto_rpow_atTop hb).comp hLog)
  have hev : ∀ᶠ n in atTop, PhaseWinA 1 ς T Nst Est (Nseq n) (Bseq n) (εs n) :=
    hW.2.2.2.1 Nseq Bseq εs hN hεT hεpos hN1 hNB hΞ
  have hr : (1 + ς - 1) / 1 = ς := by ring
  have hWeq : ∀ᶠ n in atTop, winnersRateI 1 ς (Nseq n) (εs n) =
      Real.log (Nseq n : ℝ) ^ (1 + b * (-(1 / (2 * ((1 + ς - 1) / 1))))) := by
    filter_upwards [hXi, hev2] with n hn hn2
    have hN2 : (2 : ℝ) ≤ Nseq n := by exact_mod_cast hn2
    have hLpos : 0 < Real.log (Nseq n : ℝ) := Real.log_pos (by linarith)
    rw [wh_W_one, hn, ← Real.rpow_mul hLpos.le, Real.rpow_add hLpos, Real.rpow_one]
  have hneg_tend : ∀ κ : ℝ, κ < 0 → Tendsto (fun n => Real.log (Nseq n : ℝ) ^ κ) atTop (𝓝 0) := by
    intro κ hκ
    have := (tendsto_rpow_neg_atTop (y := -κ) (by linarith)).comp hLog
    simp only [Function.comp_def, neg_neg] at this
    exact this
  refine ⟨hev, ?_, ?_⟩
  · intro hb2
    rw [hr] at hb2
    have hκpos : 0 < 1 + b * (-(1 / (2 * ((1 + ς - 1) / 1)))) := by
      rw [hr]
      have e : b * (-(1 / (2 * ς))) = -(b / (2 * ς)) := by ring
      rw [e]
      have : b / (2 * ς) < 1 := by
        rw [div_lt_one (by linarith)]
        linarith
      linarith
    have hWtend : Tendsto (fun n => winnersRateI 1 ς (Nseq n) (εs n)) atTop atTop :=
      Tendsto.congr' (hWeq.mono fun n hn => hn.symm) ((tendsto_rpow_atTop hκpos).comp hLog)
    have hLow := Tendsto.const_mul_atTop (mul_pos (div_pos hc0 (hc0.trans_le hcc)) hdLo) hWtend
    refine tendsto_atTop_mono' atTop ?_ hLow
    filter_upwards [hev, hev2] with n hn hn2
    have hcor := cor_app_phase_ratio_i 1 ς T one_pos (by linarith) hς₂ hT Nst Est cLo cHi hW
      (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn (hSm n) (hSV n) (hGm n) (hGV n)
    have hcomb := wh_comb hc0 hcc hcor (hK (Nseq n) hn2 (εs n) (hεpos n))
    exact hcomb.1
  · intro hb2
    rw [hr] at hb2
    have hκneg : 1 + b * (-(1 / (2 * ((1 + ς - 1) / 1)))) < 0 := by
      rw [hr]
      have e : b * (-(1 / (2 * ς))) = -(b / (2 * ς)) := by ring
      rw [e]
      have : 1 < b / (2 * ς) := by
        rw [one_lt_div (by linarith)]
        linarith
      linarith
    have hWtend : Tendsto (fun n => winnersRateI 1 ς (Nseq n) (εs n)) atTop (𝓝 0) :=
      Tendsto.congr' (hWeq.mono fun n hn => hn.symm) (hneg_tend _ hκneg)
    have hUp : Tendsto (fun n => cHi / cLo * dHi * winnersRateI 1 ς (Nseq n) (εs n)) atTop (𝓝 0) := by
      have := hWtend.const_mul (cHi / cLo * dHi)
      rwa [mul_zero] at this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp
    · exact Filter.Eventually.of_forall fun n => by
        unfold phaseR
        exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · filter_upwards [hev, hev2] with n hn hn2
      have hcor := cor_app_phase_ratio_i 1 ς T one_pos (by linarith) hς₂ hT Nst Est cLo cHi hW
        (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn (hSm n) (hSV n) (hGm n) (hGV n)
      have hcomb := wh_comb hc0 hcc hcor (hK (Nseq n) hn2 (εs n) (hεpos n))
      exact hcomb.2

/-- Private (P-H.9.P4): the rate `winnersRateI` on the power family `ε = N^{-ω}`, `1 < α < 2`. -/
lemma wh_mid_rate (α ς ω : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hp : 0 < α + ς - 1)
    (N : ℕ) (hN : 1 ≤ N) :
    winnersRateI α ς N ((N : ℝ) ^ (-ω)) =
      (N : ℝ) ^ (α / (2 * (α + ς - 1)) * (ω - (α + ς - 1) / α * (2 - α))) := by
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  have hαpos : 0 < α := by linarith
  have hp' : α + ς - 1 ≠ 0 := hp.ne'
  have hα' : α ≠ 0 := hαpos.ne'
  rw [wh_W_mid α ς hα1 hα2 hp N ((N : ℝ) ^ (-ω)) (Real.rpow_pos_of_pos hNpos (-ω)),
    ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos, ← Real.rpow_add hNpos]
  congr 1
  field_simp
  ring

/-- Private (P-H.9.P4): the rate `winnersRateI` on the logarithmic family `ε = (log N)^{-ω}`, `α = 2`. -/
lemma wh_two_rate (ς ω : ℝ) (hp : 0 < 2 + ς - 1) (N : ℕ) (hN : 2 ≤ N) :
    winnersRateI 2 ς N (Real.log (N : ℝ) ^ (-ω)) =
      Real.log (N : ℝ) ^ (ω * (2 / (2 * (2 + ς - 1))) - 1) := by
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have h1 : (N : ℝ) ^ (-((2 : ℝ) / 2)) = (N : ℝ)⁻¹ := by
    rw [show -((2 : ℝ) / 2) = -1 by norm_num, Real.rpow_neg_one]
  have e : (-ω) * (-(2 / (2 * (2 + ς - 1)))) = ω * (2 / (2 * (2 + ς - 1))) := by ring
  rw [wh_W_eq2 2 ς rfl hp N (Real.log (N : ℝ) ^ (-ω)) (Real.rpow_pos_of_pos hL (-ω)), h1,
    ← Real.rpow_mul hL.le, e, Real.rpow_sub_one hL.ne']
  have hNne : (N : ℝ) ≠ 0 := hNpos.ne'
  have hLne : Real.log (N : ℝ) ≠ 0 := hL.ne'
  field_simp

/-- Private (P-H.9.P4): `s`-power against a power of the logarithm tends to `+∞`. -/
lemma wh_log_Xi (s ω : ℝ) (hs : 0 < s) :
    Tendsto (fun x : ℝ => Real.log x ^ (-ω) * x ^ s) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => Real.log x ^ ω / x ^ s) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop ω hs).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => Real.log x ^ ω / x ^ s) atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h1, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hl : 0 < Real.log x := Real.log_pos hx
    exact div_pos (Real.rpow_pos_of_pos hl ω) (Real.rpow_pos_of_pos (by linarith) s)
  refine Tendsto.congr' ?_ h2.inv_tendsto_nhdsGT_zero
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hl : 0 < Real.log x := Real.log_pos hx
  dsimp only [Pi.inv_apply]
  rw [inv_div, Real.rpow_neg hl.le]
  ring

/-- Private (P-H.9.P4): a positive power of a sequence tending to `+∞` tends to `+∞`. -/
lemma wh_seq_rpow_top {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {E : ℝ} (hE : 0 < E) :
    Tendsto (fun n => f n ^ E) atTop atTop :=
  (tendsto_rpow_atTop hE).comp hf

/-- Private (P-H.9.P4): a negative power of a sequence tending to `+∞` tends to `0`. -/
lemma wh_seq_rpow_zero {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) {E : ℝ} (hE : E < 0) :
    Tendsto (fun n => f n ^ E) atTop (𝓝 0) := by
  have h := (tendsto_rpow_neg_atTop (show 0 < -E by linarith)).comp hf
  simpa only [Function.comp_def, neg_neg] using h

/-- Label `prop:app-phase-winners`, part (i), the case `1 < α < 2` with `ε_N = N^{-ω}`,
`0 < ω < p-1`, and `ω_c = r_{s-SVD}(2-α)`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The sequence lies in the window for all large indices (part of the claim). -/
theorem prop_app_phase_winners_i_mid (α ς T ω : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (hς₁ : 1 - α < ς) (hς₂ : ς < 1) (hω0 : 0 < ω) (hωp : ω < α + ς - 1) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseAWindowHolds α ς T Nst Est cLo cHi) :
    (0 < (α + ς - 1) / α * (2 - α) ∧ (α + ς - 1) / α * (2 - α) < α + ς - 1) ∧
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ n, εs n = powerEps ω (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinA α ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      (ω < (α + ς - 1) / α * (2 - α) →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
      ((α + ς - 1) / α * (2 - α) < ω →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) := by
  have hαpos : 0 < α := by linarith
  have hp : 0 < α + ς - 1 := by linarith
  have hκ : 0 < α / (2 * (α + ς - 1)) := div_pos hαpos (mul_pos two_pos hp)
  have hωc0 : 0 < (α + ς - 1) / α * (2 - α) := mul_pos (div_pos hp hαpos) (by linarith)
  have hωc1 : (α + ς - 1) / α * (2 - α) < α + ς - 1 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hαpos]
    nlinarith [mul_pos hp (show (0 : ℝ) < 2 * α - 2 by linarith)]
  refine ⟨⟨hωc0, hωc1⟩, ?_⟩
  intro Nseq Bseq εs mS mG QS QG hMS hform
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hNpos : ∀ n, (0 : ℝ) < Nseq n := fun n => by
    have : (1 : ℝ) ≤ Nseq n := by exact_mod_cast hN1 n
    linarith
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hev2 : ∀ᶠ n in atTop, 2 ≤ Nseq n := hNℕ.eventually_ge_atTop 2
  have hΞeq : ∀ n, εs n * (Nseq n : ℝ) ^ (α + ς - 1) = (Nseq n : ℝ) ^ ((α + ς - 1) - ω) := by
    intro n
    rw [hform n]
    unfold powerEps
    rw [← Real.rpow_add (hNpos n)]
    congr 1
    ring
  have hpowΞ : Tendsto (fun n => (Nseq n : ℝ) ^ ((α + ς - 1) - ω)) atTop atTop :=
    wh_seq_rpow_top hN (by linarith)
  have hΞ : Tendsto (fun n => εs n * (Nseq n : ℝ) ^ (α + ς - 1)) atTop atTop :=
    Tendsto.congr (fun n => (hΞeq n).symm) hpowΞ
  have hev : ∀ᶠ n in atTop, PhaseWinA α ς T Nst Est (Nseq n) (Bseq n) (εs n) :=
    hW.2.2.2.1 Nseq Bseq εs hN hεT hεpos hN1 hNB hΞ
  have hrate : ∀ n, winnersRateI α ς (Nseq n) (εs n) =
      (Nseq n : ℝ) ^ (α / (2 * (α + ς - 1)) * (ω - (α + ς - 1) / α * (2 - α))) := by
    intro n
    rw [hform n]
    unfold powerEps
    exact wh_mid_rate α ς ω hα1 hα2 hp (Nseq n) (hN1 n)
  obtain ⟨dLo, dHi, hdLo, -, hS⟩ :=
    prop_app_phase_winners_i α ς T hαpos hς₁ hς₂ hT Nst Est cLo cHi hW
  have hlo : ∀ᶠ n in atTop, dLo * winnersRateI α ς (Nseq n) (εs n) ≤
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ∧
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ≤ dHi * winnersRateI α ς (Nseq n) (εs n) := by
    filter_upwards [hev, hev2] with n hn hn2
    exact hS (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn hn2 (hSm n) (hSV n)
      (hGm n) (hGV n)
  refine ⟨hev, ?_, ?_⟩
  · intro hlt
    have hE : α / (2 * (α + ς - 1)) * (ω - (α + ς - 1) / α * (2 - α)) < 0 :=
      mul_neg_of_pos_of_neg hκ (by linarith)
    have hWt : Tendsto (fun n => winnersRateI α ς (Nseq n) (εs n)) atTop (𝓝 0) :=
      Tendsto.congr (fun n => (hrate n).symm) (wh_seq_rpow_zero hN hE)
    have hUp : Tendsto (fun n => dHi * winnersRateI α ς (Nseq n) (εs n)) atTop (𝓝 0) := by
      have := hWt.const_mul dHi
      rwa [mul_zero] at this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp
    · exact Filter.Eventually.of_forall fun n => by
        unfold phaseR
        exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · filter_upwards [hlo] with n hn
      exact hn.2
  · intro hgt
    have hE : 0 < α / (2 * (α + ς - 1)) * (ω - (α + ς - 1) / α * (2 - α)) :=
      mul_pos hκ (by linarith)
    have hWt : Tendsto (fun n => winnersRateI α ς (Nseq n) (εs n)) atTop atTop :=
      Tendsto.congr (fun n => (hrate n).symm) (wh_seq_rpow_top hN hE)
    have hLow : Tendsto (fun n => dLo * winnersRateI α ς (Nseq n) (εs n)) atTop atTop :=
      Tendsto.const_mul_atTop hdLo hWt
    refine tendsto_atTop_mono' atTop ?_ hLow
    filter_upwards [hlo] with n hn
    exact hn.1

/-- Label `prop:app-phase-winners`, part (i), the case `α = 2` with `ε_N = (log N)^{-ω}`,
`ω > 0`, `r_{s-SVD} = (p-1)/2`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The sequence lies in the window for all large indices (part of the claim). -/
theorem prop_app_phase_winners_i_two (ς T ω : ℝ) (hς₁ : -1 < ς) (hς₂ : ς < 1) (hω : 0 < ω)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseAWindowHolds 2 ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq 2 ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, εs n = logEps ω (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinA 2 ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      (ω < 2 * ((2 + ς - 1) / 2) →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
      (2 * ((2 + ς - 1) / 2) < ω →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) := by
  have hs : 0 < 2 + ς - 1 := by linarith
  have hκ2 : 0 < (2 : ℝ) / (2 * (2 + ς - 1)) := div_pos two_pos (mul_pos two_pos hs)
  have hq1 : (2 + ς - 1) * ((2 : ℝ) / (2 * (2 + ς - 1))) = 1 := by
    have : (2 + ς - 1) ≠ 0 := hs.ne'
    field_simp
  intro Nseq Bseq εs mS mG QS QG hMS hform
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hev2 : ∀ᶠ n in atTop, 2 ≤ Nseq n := hNℕ.eventually_ge_atTop 2
  have hLogT : Tendsto (fun n => Real.log (Nseq n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hN
  have hL2 : Tendsto (fun n => Real.log (Nseq n : ℝ) ^ (-ω) * (Nseq n : ℝ) ^ (2 + ς - 1))
      atTop atTop :=
    (wh_log_Xi (2 + ς - 1) ω hs).comp hN
  have hEV : (fun n => Real.log (Nseq n : ℝ) ^ (-ω) * (Nseq n : ℝ) ^ (2 + ς - 1)) =ᶠ[atTop]
      (fun n => εs n * (Nseq n : ℝ) ^ (2 + ς - 1)) := by
    filter_upwards [hform] with n hn
    rw [hn]
    rfl
  have hΞ : Tendsto (fun n => εs n * (Nseq n : ℝ) ^ (2 + ς - 1)) atTop atTop :=
    Tendsto.congr' hEV hL2
  have hev : ∀ᶠ n in atTop, PhaseWinA 2 ς T Nst Est (Nseq n) (Bseq n) (εs n) :=
    hW.2.2.2.1 Nseq Bseq εs hN hεT hεpos hN1 hNB hΞ
  have hWeq : ∀ᶠ n in atTop, winnersRateI 2 ς (Nseq n) (εs n) =
      Real.log (Nseq n : ℝ) ^ (ω * (2 / (2 * (2 + ς - 1))) - 1) := by
    filter_upwards [hform, hev2] with n hn hn2
    rw [hn]
    exact wh_two_rate ς ω hs (Nseq n) hn2
  obtain ⟨dLo, dHi, hdLo, -, hS⟩ :=
    prop_app_phase_winners_i 2 ς T (by norm_num) (by linarith) hς₂ hT Nst Est cLo cHi hW
  have hlo : ∀ᶠ n in atTop, dLo * winnersRateI 2 ς (Nseq n) (εs n) ≤
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ∧
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ≤ dHi * winnersRateI 2 ς (Nseq n) (εs n) := by
    filter_upwards [hev, hev2] with n hn hn2
    exact hS (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn hn2 (hSm n) (hSV n)
      (hGm n) (hGV n)
  refine ⟨hev, ?_, ?_⟩
  · intro hlt
    have hE : ω * (2 / (2 * (2 + ς - 1))) - 1 < 0 := by
      have h2 : ω * ((2 : ℝ) / (2 * (2 + ς - 1))) < (2 + ς - 1) * ((2 : ℝ) / (2 * (2 + ς - 1))) :=
        mul_lt_mul_of_pos_right (by linarith) hκ2
      linarith
    have hWt : Tendsto (fun n => winnersRateI 2 ς (Nseq n) (εs n)) atTop (𝓝 0) :=
      Tendsto.congr' (hWeq.mono fun n hn => hn.symm) (wh_seq_rpow_zero hLogT hE)
    have hUp : Tendsto (fun n => dHi * winnersRateI 2 ς (Nseq n) (εs n)) atTop (𝓝 0) := by
      have := hWt.const_mul dHi
      rwa [mul_zero] at this
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hUp
    · exact Filter.Eventually.of_forall fun n => by
        unfold phaseR
        exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    · filter_upwards [hlo] with n hn
      exact hn.2
  · intro hgt
    have hE : 0 < ω * (2 / (2 * (2 + ς - 1))) - 1 := by
      have h2 : (2 + ς - 1) * ((2 : ℝ) / (2 * (2 + ς - 1))) < ω * ((2 : ℝ) / (2 * (2 + ς - 1))) :=
        mul_lt_mul_of_pos_right (by linarith) hκ2
      linarith
    have hWt : Tendsto (fun n => winnersRateI 2 ς (Nseq n) (εs n)) atTop atTop :=
      Tendsto.congr' (hWeq.mono fun n hn => hn.symm) (wh_seq_rpow_top hLogT hE)
    have hLow : Tendsto (fun n => dLo * winnersRateI 2 ς (Nseq n) (εs n)) atTop atTop :=
      Tendsto.const_mul_atTop hdLo hWt
    refine tendsto_atTop_mono' atTop ?_ hLow
    filter_upwards [hlo] with n hn
    exact hn.1

/-- Label `prop:app-phase-winners`, part (i), the case `α > 2`: `𝖱 → ∞`. Snapshot
`cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1391–1410):

```latex
\item \emph{The range $\texp<1$} (window of \cref{thm:app-phase-A}). With
$\Xi_N\defeq\epsilon N^{p-1}$ and $r_{\text{s-SVD}}=(p-1)/\alpha$,
\[
\mathsf R\asymp\begin{cases}
\Xi_N^{-1/(2r_{\text{s-SVD}})},&0<\alpha<1,\\
(\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=1,\\
N^{\alpha-1}\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&1<\alpha<2,\\
(N/\log N)\,\Xi_N^{-1/(2r_{\text{s-SVD}})},&\alpha=2,\\
\epsilon^{-1/(2r_{\text{s-SVD}})},&\alpha>2.
\end{cases}
\]
Hence $\mathsf R\to0$ for $0<\alpha<1$ and $\mathsf R\to\infty$ for $\alpha>2$.
For $\alpha=1$ and $\epsilon_N=N^{-r_{\text{s-SVD}}}(\log N)^{b}$ with $b>0$,
$\mathsf R\to\infty$ if $b<2r_{\text{s-SVD}}$ and $\mathsf R\to0$ if
$b>2r_{\text{s-SVD}}$. For $1<\alpha<2$ and $\epsilon_N=N^{-\omega}$ with
$0<\omega<p-1$, put $\omega_c\defeq r_{\text{s-SVD}}(2-\alpha)\in(0,p-1)$; then
$\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\alpha=2$ and $\epsilon_N=(\log N)^{-\omega}$ with $\omega>0$, $\mathsf R\to0$ if
$\omega<2r_{\text{s-SVD}}$ and $\mathsf R\to\infty$ if $\omega>2r_{\text{s-SVD}}$. All
these sequences lie in the window.
```

The sequences are assumed in the window (the rate is `ε^{-1/(2r)}`, no `Ξ`-divergence needed). -/
theorem prop_app_phase_winners_i_gt2 (α ς T : ℝ) (hα : 2 < α) (hς₁ : 1 - α < ς) (hς₂ : ς < 1)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseAWindowHolds α ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, PhaseWinA α ς T Nst Est (Nseq n) (Bseq n) (εs n)) →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop := by
  have hp : 0 < α + ς - 1 := by linarith
  have hα0 : 0 < α := by linarith
  have hκ : 0 < α / (2 * (α + ς - 1)) := div_pos hα0 (mul_pos two_pos hp)
  intro Nseq Bseq εs mS mG QS QG hMS hev0
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hev2 : ∀ᶠ n in atTop, 2 ≤ Nseq n := hNℕ.eventually_ge_atTop 2
  obtain ⟨dLo, dHi, hdLo, -, hS⟩ :=
    prop_app_phase_winners_i α ς T hα0 hς₁ hς₂ hT Nst Est cLo cHi hW
  have hεpos' : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεT, Filter.Eventually.of_forall fun n => hεpos n⟩
  have hεpow : Tendsto (fun n => εs n ^ (-(α / (2 * (α + ς - 1))))) atTop atTop :=
    (tendsto_rpow_neg_nhdsGT_zero (by linarith : -(α / (2 * (α + ς - 1))) < 0)).comp hεpos'
  have hR : ∀ n, winnersRateI α ς (Nseq n) (εs n) = εs n ^ (-(α / (2 * (α + ς - 1)))) := by
    intro n
    rw [wh_W_gt2 α ς hα0 hα hp (Nseq n) (εs n), one_mul]
  have hWt : Tendsto (fun n => winnersRateI α ς (Nseq n) (εs n)) atTop atTop :=
    Tendsto.congr (fun n => (hR n).symm) hεpow
  have hLow : Tendsto (fun n => dLo * winnersRateI α ς (Nseq n) (εs n)) atTop atTop :=
    Tendsto.const_mul_atTop hdLo hWt
  have hlo : ∀ᶠ n in atTop, dLo * winnersRateI α ς (Nseq n) (εs n) ≤
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := by
    filter_upwards [hev0, hev2] with n hn hn2
    exact (hS (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn hn2 (hSm n) (hSV n)
      (hGm n) (hGV n)).1
  exact tendsto_atTop_mono' atTop hlo hLow

/-! ### Proof helpers for `prop:app-phase-winners` (ii), (iii) (P-H.9.P5) -/

lemma wh5_H_tendsto {a : ℝ} (ha : 1 < a) :
    Tendsto (fun N : ℕ => Hsum a N) atTop (𝓝 (zetaR a)) := by
  have hp : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a) / (a - 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun N : ℕ => (N : ℝ) ^ (1 - a)) atTop (𝓝 0) := by
      rw [show (1 : ℝ) - a = -(a - 1) by ring]
      exact (tendsto_rpow_neg_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have h2 := h.div_const (a - 1)
    rw [zero_div] at h2
    exact h2
  have hlim : Tendsto (fun N : ℕ => zetaR a - Hsum a N) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hp
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (lem_app_phase_harmonic_vi ha N hN).2
  have h2 := (tendsto_const_nhds (x := zetaR a)).sub hlim
  simpa using h2

lemma wh5_one_le_zeta {a : ℝ} (ha : 1 < a) : 1 ≤ zetaR a := by
  have h := (lem_app_phase_harmonic_vi ha 1 le_rfl).1
  have h1 : Hsum a 1 = 1 := by simp [Hsum]
  linarith

lemma wh5_zeta_mono {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) : zetaR b ≤ zetaR a := by
  refine le_of_tendsto_of_tendsto' (wh5_H_tendsto (by linarith)) (wh5_H_tendsto ha) (fun N => ?_)
  unfold Hsum
  apply Finset.sum_le_sum
  intro i hi
  have hi1 : (1 : ℝ) ≤ (i : ℝ) := by exact_mod_cast (Finset.mem_Icc.1 hi).1
  exact Real.rpow_le_rpow_of_exponent_le hi1 (by linarith)

lemma wh5_DN_tendsto (α : ℝ) (hα : 2 < α) :
    Tendsto (fun N : ℕ => phaseDN α N) atTop (𝓝 (Real.pi * zetaR α / zetaR (α / 2))) :=
  ((prop_app_phase_prefactors_iv α (by linarith)).2.2.2.2 hα).symm.tendsto_nhds tendsto_const_nhds

lemma wh5_phaseDN_pos (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 < phaseDN α N :=
  div_pos (mul_pos Real.pi_pos (wh_Hsum_pos α hN)) (wh_Hsum_pos (α / 2) hN)

lemma wh5_sandwich (α ς T : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
    (QS QG : ∀ n, ℝ → ℝ) (hMS : MatchedSeq α ς Nseq Bseq εs mS mG QS QG)
    (hwin : ∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) :
    ∀ᶠ n in atTop, (cLo / cHi) * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) ≤
        phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ∧
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ≤
        (cHi / cLo) * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) := by
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  filter_upwards [hwin] with n hn
  exact cor_app_phase_ratio_ii α ς T hα hς hT Nst Est cLo cHi hW (Nseq n) (Bseq n) (εs n)
    (mS n) (mG n) (QS n) (QG n) hn (hSm n) (hSV n) (hGm n) (hGV n)

lemma wh5_rate1 :
    Tendsto (fun x : ℝ => x ^ (-(1 / 2 : ℝ)) / Real.log (1 / x)) (𝓝[>] 0) atTop := by
  have h0 := tendsto_log_div_rpow_nhdsGT_zero (r := -(1 / 2 : ℝ)) (by norm_num)
  have h1 : Tendsto (fun x : ℝ => Real.log (1 / x) / x ^ (-(1 / 2 : ℝ))) (𝓝[>] 0) (𝓝 0) := by
    have h := h0.neg
    rw [neg_zero] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [show (1 : ℝ) / x = x⁻¹ from one_div x, Real.log_inv, neg_div]
  have h2 : Tendsto (fun x : ℝ => Real.log (1 / x) / x ^ (-(1 / 2 : ℝ))) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨h1, ?_⟩
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with x hx
    exact div_pos (Real.log_pos (one_lt_one_div hx.1 hx.2)) (Real.rpow_pos_of_pos hx.1 _)
  have h3 := h2.inv_tendsto_nhdsGT_zero
  refine h3.congr (fun x => ?_)
  simp only [Pi.inv_apply]
  rw [inv_div]

lemma wh5_rate_top (α ς : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hς2 : ς ≤ α + 1)
    {εs : ℕ → ℝ} (hε0 : Tendsto εs atTop (𝓝 0)) (hεpos : ∀ n, 0 < εs n) :
    Tendsto (fun n => phaseRatioRate α ς (εs n)) atTop atTop := by
  have hεn : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hε0, Filter.Eventually.of_forall fun n => hεpos n⟩
  have hlog : Tendsto (fun n => Real.log (1 / εs n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (hεn.inv_tendsto_nhdsGT_zero.congr (fun n => by simp [one_div]))
  by_cases h1 : ς = 1
  · subst h1
    have : (fun n => phaseRatioRate α 1 (εs n)) =
        fun n => εs n ^ (-(1 / 2 : ℝ)) / Real.log (1 / εs n) := by
      funext n
      simp [phaseRatioRate]
    rw [this]
    exact wh5_rate1.comp hεn
  · have h1' : 1 < ς := lt_of_le_of_ne hς (Ne.symm h1)
    by_cases h2 : ς = α + 1
    · have : (fun n => phaseRatioRate α ς (εs n)) = fun n => Real.log (1 / εs n) := by
        funext n
        unfold phaseRatioRate
        rw [if_neg (by linarith), if_neg h1, if_neg (by linarith), if_pos h2]
      rw [this]
      exact hlog
    · have h2' : ς < α + 1 := lt_of_le_of_ne hς2 h2
      have : (fun n => phaseRatioRate α ς (εs n)) =
          fun n => εs n ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) := by
        funext n
        unfold phaseRatioRate
        rw [if_neg (by linarith), if_neg h1, if_pos h2']
      rw [this]
      have hneg : -((α + 1 - ς) / (2 * (α + ς - 1))) < 0 := by
        have : 0 < (α + 1 - ς) / (2 * (α + ς - 1)) :=
          div_pos (by linarith) (by linarith)
        linarith
      exact (tendsto_rpow_neg_nhdsGT_zero hneg).comp hεn

lemma wh5_rate_big (α ς ε : ℝ) (hς : 1 ≤ ς) (hbig : α + 1 < ς) (hα : 1 < α) :
    phaseRatioRate α ς ε = 1 := by
  unfold phaseRatioRate
  rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_neg (by linarith)]

lemma wh5_Jpq_nonneg (p q : ℝ) : 0 ≤ Jpq p q :=
  setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)

lemma wh5_Jpq_integrable {p q : ℝ} (h : Jpq p q ≠ 0) :
    IntegrableOn (fun u => Real.sqrt (fNq ⊤ p q u)) (Ioi (0 : ℝ)) := by
  by_contra hc
  exact h (integral_undef hc)

lemma wh5_Jpq_mono (p α : ℝ) (hp : 1 < p) (hα : 0 < α)
    (h1 : Jpq p (α / 2) ≠ 0) (h2 : Jpq p α ≠ 0) : Jpq p (α / 2) ≤ Jpq p α := by
  unfold Jpq
  apply setIntegral_mono_on (wh5_Jpq_integrable h1) (wh5_Jpq_integrable h2) measurableSet_Ioi
  intro u hu
  exact Real.sqrt_le_sqrt (wh_fNq_mono ⊤ p α (α / 2) u hp (le_of_lt (Set.mem_Ioi.1 hu))
    (by linarith))

lemma wh5_DN_zero (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) :
    Tendsto (fun N : ℕ => phaseDN α N) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hpre := prop_app_phase_prefactors_iv α hα0
  rcases lt_or_eq_of_le hα2 with hlt | heq
  · have h1 := hpre.2.2.1 hα1 hlt
    have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (α / 2 - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (by linarith : 0 < 1 - α / 2)).comp
        tendsto_natCast_atTop_atTop
      refine this.congr (fun N => ?_)
      simp only [Function.comp]
      congr 1; ring
    have h3 := h2.const_mul (Real.pi * (1 - α / 2) * zetaR α)
    rw [mul_zero] at h3
    exact h1.symm.tendsto_nhds h3
  · subst heq
    have h1 := hpre.2.2.2.1 rfl
    have h3 : Tendsto (fun N : ℕ => Real.pi * zetaR 2 / Real.log (N : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    exact h1.symm.tendsto_nhds h3

lemma wh5_log_rpow_neg (a K : ℝ) (ha : 0 < a) :
    Tendsto (fun x : ℝ => x ^ (-a) * (Real.log x + K)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
  have h2 : Tendsto (fun x : ℝ => x ^ (-a)) atTop (𝓝 0) := tendsto_rpow_neg_atTop ha
  have h3 := h1.add (h2.const_mul K)
  rw [mul_zero, add_zero] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le]
  ring

lemma wh5_DN_log (α : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (K : ℝ) :
    Tendsto (fun N : ℕ => phaseDN α N * (Real.log (N : ℝ) + K)) atTop (𝓝 0) := by
  have hα0 : 0 < α := by linarith
  have hequiv := (prop_app_phase_prefactors_iv α hα0).2.2.1 hα1 hα2
  have hequiv2 := hequiv.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ) + K))
  have h2 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-(1 - α / 2)) * (Real.log (N : ℝ) + K)) atTop
      (𝓝 0) :=
    (wh5_log_rpow_neg (1 - α / 2) K (by linarith)).comp tendsto_natCast_atTop_atTop
  have h3 := h2.const_mul (Real.pi * (1 - α / 2) * zetaR α)
  rw [mul_zero] at h3
  refine hequiv2.symm.tendsto_nhds (h3.congr (fun N => ?_))
  show Real.pi * (1 - α / 2) * zetaR α * ((N : ℝ) ^ (-(1 - α / 2)) * (Real.log (N : ℝ) + K)) =
    Real.pi * (1 - α / 2) * zetaR α * (N : ℝ) ^ (α / 2 - 1) * (Real.log (N : ℝ) + K)
  rw [show -(1 - α / 2) = α / 2 - 1 by ring]
  ring

lemma wh5_log_le {Est ε : ℝ} {N : ℕ} (hE : 0 < Est) (hε : 0 < ε) (hN : 1 ≤ N)
    (h : Est ≤ ε * (N : ℝ)) : Real.log (1 / ε) ≤ Real.log (N : ℝ) + (-Real.log Est) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 : Real.log Est ≤ Real.log (ε * (N : ℝ)) := Real.log_le_log hE h
  rw [Real.log_mul hε.ne' hNpos.ne'] at h1
  rw [one_div, Real.log_inv]
  linarith

lemma wh5_models (α ς : ℝ) (N B : ℕ) (hα : 0 < α) (hp : 1 < α + ς) (hN : 1 ≤ N)
    (hNB : N ≤ B) :
    ∃ (mS mG : ℝ → RowModel (Fin N)) (QS QG : ℝ → ℝ → ℝ),
      ∀ ε : ℝ, 0 < ε →
        (IsMatchedModel (svdArrays α ς N B) (mS ε) ε ∧ IsVolterraSol (mS ε) (QS ε)) ∧
        (IsMatchedModel (sgdArrays α ς N B) (mG ε) ε ∧ IsVolterraSol (mG ε) (QG ε)) := by
  obtain ⟨hm1, hm2, -, -⟩ := prop_app_phase_prefactors_m1 α ς N B hα hp hN hNB
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hBpos : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hγ : 0 < gammaRat N B := by unfold gammaRat; exact div_pos hNpos hBpos
  have key1 : ∀ ε : ℝ, 0 < ε → ∃ (a b : RowModel (Fin N)) (qa qb : ℝ → ℝ),
      (IsMatchedModel (svdArrays α ς N B) a ε ∧ IsVolterraSol a qa) ∧
      (IsMatchedModel (sgdArrays α ς N B) b ε ∧ IsVolterraSol b qb) := by
    intro ε hε
    have hpre := prop_app_phase_prefactors_i α ς N B hα hp hN hNB ε hε
    have hηS : 0 < matchedStep (svdArrays α ς N B) ε := by
      rw [hpre.2.1]
      exact div_pos (mul_pos four_pos (Real.sqrt_pos.2 hε))
        (mul_pos (Real.sqrt_pos.2 hγ) (wh_Hsum_pos _ hN))
    have hηG : 0 < matchedStep (sgdArrays α ς N B) ε := by
      rw [hpre.2.2.2.1]
      exact mul_pos (div_pos (mul_pos four_pos (Real.sqrt_pos.2 hε)) (pow_pos hNpos 2))
        (Real.sqrt_pos.2 (div_pos hBpos (mul_pos Real.pi_pos (wh_muBar_pos α hN))))
    obtain ⟨a, ha1, ha2, ha3, ha4, ha5⟩ := hm1 _ hηS
    obtain ⟨b, hb1, hb2, hb3, hb4, hb5⟩ := hm2 _ hηG
    obtain ⟨qa, hqa, -⟩ := thm_app_phase_volterra_i a
    obtain ⟨qb, hqb, -⟩ := thm_app_phase_volterra_i b
    exact ⟨a, b, qa, qb, ⟨⟨ha1, ha2, ha3, ha4, ha5⟩, hqa⟩, ⟨⟨hb1, hb2, hb3, hb4, hb5⟩, hqb⟩⟩
  have key : ∀ ε : ℝ, ∃ (a b : RowModel (Fin N)) (qa qb : ℝ → ℝ), 0 < ε →
      (IsMatchedModel (svdArrays α ς N B) a ε ∧ IsVolterraSol a qa) ∧
      (IsMatchedModel (sgdArrays α ς N B) b ε ∧ IsVolterraSol b qb) := by
    intro ε
    by_cases hε : 0 < ε
    · obtain ⟨a, b, qa, qb, h⟩ := key1 ε hε
      exact ⟨a, b, qa, qb, fun _ => h⟩
    · obtain ⟨a, b, qa, qb, _⟩ := key1 1 one_pos
      exact ⟨a, b, qa, qb, fun h => absurd h hε⟩
  choose a b qa qb h using key
  exact ⟨a, b, qa, qb, h⟩

lemma wh5_est_pos (α ς T : ℝ) (hα : 0 < α) (hp : 1 < α + ς) (hr : rq (α + ς) α = 1)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (he0 : 0 < phaseEps0 α ς T) : 0 < Est := by
  by_contra hEst
  push_neg at hEst
  have hcLo : 0 < cLo := hW.1
  set N0 : ℕ := max Nst 1 with hN0def
  have hN1 : 1 ≤ N0 := le_max_right _ _
  have hNst : Nst ≤ N0 := le_max_left _ _
  have hN0pos : (0 : ℝ) < N0 := by exact_mod_cast (show 0 < N0 by omega)
  obtain ⟨mS, mG, QS, QG, hmod⟩ := wh5_models α ς N0 N0 hα hp hN1 le_rfl
  have hfix := (cor_app_phase_fixed α ς T N0 N0 hα hp hN1 le_rfl hT mS mG QS QG
    (fun ε hε => (hmod ε hε).1) (fun ε hε => (hmod ε hε).2)).2.1
  have hpre := prop_app_phase_prefactors_i α ς N0 N0 hα hp hN1 le_rfl 1 one_pos
  have hc0 : 0 < (sgdArrays α ς N0 N0).S * sgdT0 α N0 N0 := by
    rw [hpre.2.2.2.2.2.1]
    exact div_pos (mul_pos (mul_pos Real.pi_pos (pow_pos hN0pos 2)) (wh_muBar_pos α hN1))
      (mul_pos two_pos hN0pos)
  set c0 := (sgdArrays α ς N0 N0).S * sgdT0 α N0 N0 with hc0def
  set J := JN N0 (α + ς) α with hJdef
  have hJ0 : 0 ≤ J :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)
  -- the upper bound from the fixed-dimension equivalent
  have hup : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (stepHit (mG ε) (QG ε) T ε).toReal ≤ 3 / 2 * (c0 * J / (2 * Real.sqrt ε)) := by
    have h := hfix.isLittleO.def (by norm_num : (0 : ℝ) < 1 / 2)
    filter_upwards [h, self_mem_nhdsWithin] with ε hε hεpos
    have hεpos' : 0 < ε := hεpos
    have hv : 0 ≤ c0 * J / (2 * Real.sqrt ε) :=
      div_nonneg (mul_nonneg hc0.le hJ0) (mul_nonneg two_pos.le (Real.sqrt_nonneg _))
    simp only [Pi.sub_apply, Real.norm_eq_abs] at hε
    rw [abs_of_nonneg hv] at hε
    have := (abs_le.mp hε).2
    have e : (sgdArrays α ς N0 N0).S * sgdT0 α N0 N0 * JN N0 (α + ς) α / (2 * Real.sqrt ε) =
        c0 * J / (2 * Real.sqrt ε) := rfl
    rw [e] at this
    linarith
  -- the lower bound from the window
  have hlow : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      cLo * (c0 * (ε ^ (-(1 / 2 : ℝ)) * Real.log (1 / ε))) ≤
        (stepHit (mG ε) (QG ε) T ε).toReal := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min he0 one_pos)] with ε hε
    have hε0 : 0 < ε := hε.1
    have hεe : ε < phaseEps0 α ς T := lt_of_lt_of_le hε.2 (min_le_left _ _)
    have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_right _ _)
    have hwin : PhaseWinB α ς T Nst Est N0 N0 ε :=
      ⟨hNst, le_rfl, hε0, hεe, by nlinarith⟩
    obtain ⟨-, -, hsg⟩ := hW.2.2.1 N0 N0 ε (mS ε) (mG ε) (QS ε) (QG ε) hwin
      (hmod ε hε0).1.1 (hmod ε hε0).1.2 (hmod ε hε0).2.1 (hmod ε hε0).2.2
    have hlog : 0 ≤ Real.log (1 / ε) :=
      Real.log_nonneg (by rw [one_div]; exact one_le_inv_iff₀.mpr ⟨hε0, hε1.le⟩)
    have hX : 0 ≤ c0 * phasePi (rq (α + ς) α) ε := by
      rw [hr]
      unfold phasePi
      simp only [lt_irrefl, if_false, if_true]
      exact mul_nonneg hc0.le (mul_nonneg (Real.rpow_nonneg hε0.le _) hlog)
    obtain ⟨hl, hu⟩ := hsg
    have hne : stepHit (mG ε) (QG ε) T ε ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ hu
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    have h1 : ENNReal.ofReal (cLo * (c0 * phasePi (rq (α + ς) α) ε)) ≤
        stepHit (mG ε) (QG ε) T ε := by
      rw [ENNReal.ofReal_mul hcLo.le]
      exact hl
    have h2 := ENNReal.toReal_mono hne h1
    rw [ENNReal.toReal_ofReal (mul_nonneg hcLo.le hX), hr] at h2
    unfold phasePi at h2
    simpa using h2
  have hlogtop : Tendsto (fun ε : ℝ => Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp (tendsto_inv_nhdsGT_zero.congr (fun x => by simp [one_div]))
  have hbig := hlogtop.eventually_gt_atTop (3 / 4 * J / cLo + 1)
  obtain ⟨ε, h1, h2, h3, hε⟩ := (hup.and (hlow.and (hbig.and self_mem_nhdsWithin))).exists
  have hε0 : 0 < ε := hε
  have hsq : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε0
  have hrp : ε ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt ε := by
    rw [Real.rpow_neg hε0.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hrp] at h2
  have h4 : cLo * (c0 * (1 / Real.sqrt ε * Real.log (1 / ε))) ≤
      3 / 2 * (c0 * J / (2 * Real.sqrt ε)) := le_trans h2 h1
  have h5 : cLo * Real.log (1 / ε) ≤ 3 / 4 * J := by
    have e1 : cLo * (c0 * (1 / Real.sqrt ε * Real.log (1 / ε))) =
        (c0 / Real.sqrt ε) * (cLo * Real.log (1 / ε)) := by ring
    have e2 : 3 / 2 * (c0 * J / (2 * Real.sqrt ε)) = (c0 / Real.sqrt ε) * (3 / 4 * J) := by
      field_simp; ring
    rw [e1, e2] at h4
    exact le_of_mul_le_mul_left h4 (div_pos hc0 hsq)
  have h6 : 3 / 4 * J / cLo + 1 < Real.log (1 / ε) := h3
  have h7 : 3 / 4 * J + cLo < cLo * Real.log (1 / ε) := by
    have := mul_lt_mul_of_pos_left h6 hcLo
    rw [mul_add, mul_div_cancel₀ _ hcLo.ne'] at this
    linarith
  linarith

/-- Label `prop:app-phase-winners`, part (ii), `α > 2`, `ς ≥ 1` (window of
`thm:app-phase-B`). Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1411–1414):

```latex
\item \emph{$\alpha>2$, $\texp\ge1$} (window of \cref{thm:app-phase-B}).
$\mathsf R\to\infty$ if $\texp\le\alpha+1$, and
$\mathsf R\to\pi\zeta(\alpha)J(p,\alpha)/(\zeta(\alpha/2)J(p,\alpha/2))\in(0,\infty)$ if
$\texp>\alpha+1$; this limit exceeds $\pi/2$ if $\alpha\ge4$.
```

The limit is `winnersLimitII`. The sequences are assumed in the window. -/
theorem prop_app_phase_winners_ii (α ς T : ℝ) (hα : 2 < α) (hς : 1 ≤ ς) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (hE : PhaseBEquivHolds α ς T Nst Est) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) →
      (ς ≤ α + 1 →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) ∧
      (α + 1 < ς →
        0 < winnersLimitII α ς ∧
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop
          (𝓝 (winnersLimitII α ς))) ∧
      (α + 1 < ς → 4 ≤ α → Real.pi / 2 < winnersLimitII α ς) := by
  intro Nseq Bseq εs mS mG QS QG hMS hwin
  have hα1 : 1 < α := by linarith
  have hα0 : 0 < α := by linarith
  have hcLo : 0 < cLo := hW.1
  have hcc : cLo ≤ cHi := hW.2.1
  have hcHi : 0 < cHi := lt_of_lt_of_le hcLo hcc
  have hsand := wh5_sandwich α ς T hα1 hς hT Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hwin
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hDn := (wh5_DN_tendsto α hα).comp hNℕ
  have hζ1 : 1 ≤ zetaR α := wh5_one_le_zeta hα1
  have hζ2 : 1 ≤ zetaR (α / 2) := wh5_one_le_zeta (by linarith)
  have hLpos : 0 < Real.pi * zetaR α / zetaR (α / 2) :=
    div_pos (mul_pos Real.pi_pos (by linarith)) (by linarith)
  have hRnn : ∀ n, 0 ≤ phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := fun n =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- positivity of the J's in the saturated regime
  have hJpos : α + 1 < ς → 0 < Jpq (α + ς) (α / 2) ∧ 0 < Jpq (α + ς) α := by
    intro hbig
    have hequiv := (cor_app_phase_ratio_iv α ς T hα1 hς hT Nst Est cLo cHi hW hE Nseq Bseq εs mS mG
      QS QG hN hεT hεpos hN1 hNB hSm hSV hGm hGV hwin).2 hbig
    have hne : Jpq (α + ς) α / Jpq (α + ς) (α / 2) ≠ 0 := by
      intro h0
      have hz : IsEquivalent atTop
          (fun n => (stepHit (mG n) (QG n) T (εs n)).toReal /
            (stepHit (mS n) (QS n) T (εs n)).toReal) (fun _ : ℕ => (0 : ℝ)) := by
        refine hequiv.congr_right (Filter.Eventually.of_forall fun n => ?_)
        show phaseDN α (Nseq n) * Jpq (α + ς) α / Jpq (α + ς) (α / 2) = 0
        rw [mul_div_assoc, h0, mul_zero]
      have hz' := isEquivalent_zero_iff_eventually_zero.mp hz
      have hpos : ∀ᶠ n in atTop, 0 < phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := by
        filter_upwards [hsand] with n hn
        refine lt_of_lt_of_le ?_ hn.1
        rw [wh5_rate_big α ς _ hς hbig hα1, mul_one]
        exact mul_pos (div_pos hcLo hcHi) (wh5_phaseDN_pos α (hN1 n))
      obtain ⟨n, hn1, hn2⟩ := (hz'.and hpos).exists
      have : phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) = 0 := hn1
      linarith
    have h1 : Jpq (α + ς) α ≠ 0 := fun h => hne (by rw [h, zero_div])
    have h2 : Jpq (α + ς) (α / 2) ≠ 0 := fun h => hne (by rw [h, div_zero])
    exact ⟨lt_of_le_of_ne (wh5_Jpq_nonneg _ _) (Ne.symm h2),
      lt_of_le_of_ne (wh5_Jpq_nonneg _ _) (Ne.symm h1)⟩
  refine ⟨fun hle => ?_, fun hbig => ?_, fun hbig h4 => ?_⟩
  · have hrate := wh5_rate_top α ς hα1 hς hle hεT hεpos
    have hlow : Tendsto (fun n => (cLo / cHi) *
        (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n))) atTop atTop :=
      Tendsto.const_mul_atTop (div_pos hcLo hcHi) (Tendsto.pos_mul_atTop hLpos hDn hrate)
    exact tendsto_atTop_mono' atTop (hsand.mono fun n hn => hn.1) hlow
  · obtain ⟨hJh, hJα⟩ := hJpos hbig
    have hequiv := (cor_app_phase_ratio_iv α ς T hα1 hς hT Nst Est cLo cHi hW hE Nseq Bseq εs mS mG
      QS QG hN hεT hεpos hN1 hNB hSm hSV hGm hGV hwin).2 hbig
    have hlim : winnersLimitII α ς = Real.pi * zetaR α / zetaR (α / 2) *
        (Jpq (α + ς) α / Jpq (α + ς) (α / 2)) := by
      unfold winnersLimitII
      rw [div_mul_div_comm]
    refine ⟨?_, ?_⟩
    · rw [hlim]
      exact mul_pos hLpos (div_pos hJα hJh)
    · have hv : Tendsto (fun n => phaseDN α (Nseq n) * Jpq (α + ς) α / Jpq (α + ς) (α / 2))
          atTop (𝓝 (winnersLimitII α ς)) := by
        rw [hlim]
        refine (hDn.mul_const (Jpq (α + ς) α / Jpq (α + ς) (α / 2))).congr (fun n => ?_)
        rw [mul_div_assoc]
        rfl
      exact hequiv.symm.tendsto_nhds hv
  · obtain ⟨hJh, hJα⟩ := hJpos hbig
    have hmono := wh5_Jpq_mono (α + ς) α (by linarith) hα0 hJh.ne' hJα.ne'
    have hζh : zetaR (α / 2) < 2 :=
      lt_of_le_of_lt (wh5_zeta_mono (by norm_num) (by linarith)) lem_app_phase_harmonic_vii
    have hζh0 : 0 < zetaR (α / 2) := by linarith
    unfold winnersLimitII
    rw [lt_div_iff₀ (mul_pos hζh0 hJh)]
    have h1 : zetaR (α / 2) * Jpq (α + ς) (α / 2) < 2 * Jpq (α + ς) (α / 2) :=
      mul_lt_mul_of_pos_right hζh hJh
    have h2 : Jpq (α + ς) α ≤ zetaR α * Jpq (α + ς) α :=
      le_mul_of_one_le_left hJα.le hζ1
    have hπ := Real.pi_pos
    nlinarith [mul_pos hπ hJh, mul_lt_mul_of_pos_left h1 hπ,
      mul_le_mul_of_nonneg_left (hmono.trans h2) hπ.le]

/-- Label `prop:app-phase-winners`, part (iii), `1 < α ≤ 2`, `ς ≥ 1` (window of
`thm:app-phase-B`). Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1415–1418):

```latex
\item \emph{$1<\alpha\le2$, $\texp\ge1$} (window of \cref{thm:app-phase-B}).
$\mathsf R\to0$ if $\texp>\alpha+1$. If $\texp=\alpha+1$ and $1<\alpha<2$, then
$\mathsf R\to0$. If $\alpha=2$, $\texp=3$ and $\log(1/\epsilon)/\log N\to c_\infty$,
then $0\le c_\infty\le1$ and $\mathsf R\to\pi\zeta(2)c_\infty/(8J(5,1))$.
```

The `α = 2, ς = 3` clause uses the limit hypothesis on `log(1/ε)/log N` as stated; the
conclusion `0 ≤ c_∞ ≤ 1` is part of the claim. -/
theorem prop_app_phase_winners_iii (α ς T : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (hE : PhaseBEquivHolds α ς T Nst Est) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) →
      (α + 1 < ς →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
      (ς = α + 1 → α < 2 →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
      (α = 2 → ς = 3 → ∀ c : ℝ,
        Tendsto (fun n => Real.log (1 / εs n) / Real.log (Nseq n : ℝ)) atTop (𝓝 c) →
        0 ≤ c ∧ c ≤ 1 ∧
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop
          (𝓝 (Real.pi * zetaR 2 * c / (8 * Jpq 5 1)))) := by
  intro Nseq Bseq εs mS mG QS QG hMS hwin
  have hα0 : 0 < α := by linarith
  have hcLo : 0 < cLo := hW.1
  have hcc : cLo ≤ cHi := hW.2.1
  have hcHi : 0 < cHi := lt_of_lt_of_le hcLo hcc
  have hsand := wh5_sandwich α ς T hα1 hς hT Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hwin
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hNℕ : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hRnn : ∀ n, 0 ≤ phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := fun n =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hDn0 : Tendsto (fun n => phaseDN α (Nseq n)) atTop (𝓝 0) :=
    (wh5_DN_zero α hα1 hα2).comp hNℕ
  have he0 : 0 < phaseEps0 α ς T := by
    obtain ⟨n, hn⟩ := hwin.exists
    exact lt_trans (hεpos n) hn.2.2.2.1
  have hε1 : ∀ᶠ n in atTop, εs n < 1 := hεT.eventually (gt_mem_nhds one_pos)
  have hrate_eq : ς = α + 1 → ∀ ε : ℝ, phaseRatioRate α ς ε = Real.log (1 / ε) := by
    intro heq ε
    unfold phaseRatioRate
    rw [if_neg (by linarith), if_neg (by linarith), if_neg (by linarith), if_pos heq]
  have hrq : ς = α + 1 → rq (α + ς) α = 1 := by
    intro heq
    unfold rq
    rw [heq]
    field_simp
    ring
  have hlogpos : ∀ n, εs n < 1 → 0 ≤ Real.log (1 / εs n) := fun n hn =>
    Real.log_nonneg (by rw [one_div]; exact one_le_inv_iff₀.mpr ⟨hεpos n, hn.le⟩)
  refine ⟨fun hbig => ?_, fun heq hlt => ?_, fun hα2' hς3 c hc => ?_⟩
  · have hg : Tendsto (fun n => cHi / cLo *
        (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n))) atTop (𝓝 0) := by
      have h1 : ∀ n, phaseRatioRate α ς (εs n) = 1 := fun n => wh5_rate_big α ς _ hς hbig hα1
      simp only [h1, mul_one]
      simpa using hDn0.const_mul (cHi / cLo)
    exact squeeze_zero' (Filter.Eventually.of_forall hRnn) (hsand.mono fun n hn => hn.2) hg
  · have hEst : 0 < Est :=
      wh5_est_pos α ς T hα0 (by linarith) (hrq heq) hT Nst Est cLo cHi hW he0
    have hg : Tendsto (fun n => cHi / cLo *
        (phaseDN α (Nseq n) * (Real.log (Nseq n : ℝ) + (-Real.log Est)))) atTop (𝓝 0) := by
      simpa using ((wh5_DN_log α hα1 hlt (-Real.log Est)).comp hNℕ).const_mul (cHi / cLo)
    refine squeeze_zero' (Filter.Eventually.of_forall hRnn) ?_ hg
    filter_upwards [hsand, hwin] with n hn hw
    refine le_trans hn.2 ?_
    rw [hrate_eq heq]
    have hlog := wh5_log_le hEst (hεpos n) (hN1 n) hw.2.2.2.2
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hlog (wh5_phaseDN_pos α (hN1 n)).le)
      (div_pos hcHi hcLo).le
  · subst hα2'
    subst hς3
    have hEst : 0 < Est :=
      wh5_est_pos 2 3 T hα0 (by norm_num) (by unfold rq; norm_num) hT Nst Est cLo cHi hW he0
    have hlogN : Tendsto (fun n => Real.log (Nseq n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp hN
    refine ⟨?_, ?_, ?_⟩
    · refine ge_of_tendsto hc ?_
      filter_upwards [hε1] with n hn
      exact div_nonneg (hlogpos n hn) (Real.log_nonneg (by exact_mod_cast hN1 n))
    · have hg : Tendsto (fun n => 1 + (-Real.log Est) / Real.log (Nseq n : ℝ)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).add
          ((tendsto_const_nhds (x := -Real.log Est)).div_atTop hlogN)
      refine le_of_tendsto_of_tendsto hc hg ?_
      filter_upwards [hwin, hlogN.eventually_gt_atTop 0] with n hw hpos
      have hlog := wh5_log_le hEst (hεpos n) (hN1 n) hw.2.2.2.2
      rw [div_le_iff₀ hpos, add_mul, div_mul_cancel₀ _ hpos.ne', one_mul]
      exact hlog
    · have hequiv := (cor_app_phase_ratio_iv 2 3 T (by norm_num) (by norm_num) hT Nst Est cLo cHi
        hW hE Nseq Bseq εs mS mG QS QG hN hεT hεpos hN1 hNB hSm hSV hGm hGV hwin).1 (by norm_num)
      have hD : IsEquivalent atTop (fun n => phaseDN 2 (Nseq n))
          (fun n => Real.pi * zetaR 2 / Real.log (Nseq n : ℝ)) :=
        ((prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl).comp_tendsto hNℕ
      have hmul : IsEquivalent atTop
          (fun n => phaseDN 2 (Nseq n) * Real.log (1 / εs n) /
            (2 * Real.sqrt (8 * 2) * Jpq (2 + 3) (2 / 2)))
          (fun n => Real.pi * zetaR 2 / Real.log (Nseq n : ℝ) * Real.log (1 / εs n) /
            (2 * Real.sqrt (8 * 2) * Jpq (2 + 3) (2 / 2))) :=
        (hD.mul (IsEquivalent.refl (u := fun n => Real.log (1 / εs n)))).div
          (IsEquivalent.refl (u := fun _ : ℕ => 2 * Real.sqrt (8 * 2) * Jpq (2 + 3) (2 / 2)))
      have hs4 : Real.sqrt (8 * 2) = 4 := by
        rw [show (8 : ℝ) * 2 = 4 ^ 2 by norm_num]
        exact Real.sqrt_sq (by norm_num)
      have hc8 : 2 * Real.sqrt (8 * 2) * Jpq (2 + 3) (2 / 2) = 8 * Jpq 5 1 := by
        rw [hs4]
        norm_num
      rw [hc8] at hmul hequiv
      have hlim : Tendsto (fun n => Real.pi * zetaR 2 / Real.log (Nseq n : ℝ) *
          Real.log (1 / εs n) / (8 * Jpq 5 1)) atTop
          (𝓝 (Real.pi * zetaR 2 * c / (8 * Jpq 5 1))) := by
        refine ((hc.const_mul (Real.pi * zetaR 2)).div_const (8 * Jpq 5 1)).congr (fun n => ?_)
        ring
      exact (hequiv.trans hmul).symm.tendsto_nhds hlim

/-! ### Proof helpers for `prop:app-phase-winners` (iv) (P-H.9.P6) -/

lemma wh7_Epq_pos {p q : ℝ} (hp : 1 < p) : 0 < Epq p q := by
  unfold Epq
  refine lt_max_of_lt_left ?_
  have : 0 < Za p := by
    unfold Za
    have := div_pos one_pos (show (0 : ℝ) < p - 1 by linarith)
    linarith
  exact mul_pos (Real.rpow_pos_of_pos (by norm_num) _) this

lemma wh7_Cpq_pos {p q : ℝ} (hp : 1 < p) : 0 < Cpq p q := by
  unfold Cpq
  exact Real.sqrt_pos.2 (by have := wh7_Epq_pos (q := q) hp; positivity)

lemma wh7_eps_lt {p q T : ℝ} (ε : ℝ) (h : ε < clockEps0 p q T) : ε < Cpq p q ^ 2 := by
  unfold clockEps0 at h
  split_ifs at h <;> simp only [lt_min_iff] at h
  · exact h.1.1.2
  · exact h.1.2

lemma wh7_Ir_gt1 {r x : ℝ} (hr : 1 < r) (hx : 1 ≤ x) :
    (1 - (2 : ℝ) ^ (1 - r)) / (r - 1) ≤ Ir r x := by
  have key : Ir r x = ((1 + x) ^ (1 - r) - 1) / (1 - r) := by
    unfold Ir
    have key : ∫ w in (0 : ℝ)..x, (1 + w) ^ (-r) = ∫ y in (1 + 0 : ℝ)..(1 + x), y ^ (-r) :=
      intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-r)) 1
    have hne : (-r) ≠ -1 := by intro h; linarith
    have h0 : (0 : ℝ) ∉ Set.uIcc 1 (1 + x) := by
      rw [Set.uIcc_of_le (by linarith)]
      intro h; linarith [h.1]
    rw [key, add_zero, integral_rpow (Or.inr ⟨hne, h0⟩), Real.one_rpow]
    rw [show -r + 1 = 1 - r by ring]
  rw [key]
  have h2 : (1 + x) ^ (1 - r) ≤ (2 : ℝ) ^ (1 - r) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by linarith)
  have h1 : (1 - r) ≠ 0 := ne_of_lt (by linarith)
  have h3 : (r - 1) ≠ 0 := ne_of_gt (by linarith)
  have e : ((1 + x) ^ (1 - r) - 1) / (1 - r) = (1 - (1 + x) ^ (1 - r)) / (r - 1) := by
    rw [div_eq_div_iff h1 h3]; ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma wh7_cr_pos {r : ℝ} (hr : 1 < r) : 0 < (1 - (2 : ℝ) ^ (1 - r)) / (r - 1) := by
  have : (2 : ℝ) ^ (1 - r) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact div_pos (by linarith) (by linarith)

lemma wh7_Ir_one {x : ℝ} (hx : 0 ≤ x) : Ir 1 x = Real.log (1 + x) := by
  unfold Ir
  have key : ∫ w in (0 : ℝ)..x, (1 + w) ^ (-(1 : ℝ)) = ∫ y in (1 + 0 : ℝ)..(1 + x), y ^ (-(1 : ℝ)) :=
    intervalIntegral.integral_comp_add_left (fun y : ℝ => y ^ (-(1 : ℝ))) 1
  rw [key, add_zero]
  simp only [Real.rpow_neg_one]
  rw [integral_inv_of_pos (by norm_num) (by linarith)]
  simp

lemma wh7_rq_gt1 {α ς : ℝ} (hα : 0 < α) (hς : 1 < ς) : 1 < rq (α + ς) (α / 2) := by
  unfold rq
  rw [lt_div_iff₀ (by linarith)]
  linarith

lemma wh7_rq_eq1 {α : ℝ} (hα : 0 < α) : rq (α + 1) (α / 2) = 1 := by
  unfold rq
  field_simp
  ring

lemma wh7_DN_eq (α : ℝ) (N : ℕ) : phaseDN α N = Real.pi / 2 * phaseKsvd α N := by
  unfold phaseDN phaseKsvd
  ring

lemma wh7_Ksvd_nonneg (α : ℝ) {N : ℕ} (hN : 1 ≤ N) : 0 ≤ phaseKsvd α N := by
  unfold phaseKsvd
  exact div_nonneg (mul_nonneg (by norm_num) (wh_Hsum_pos α hN).le) (wh_Hsum_pos (α / 2) hN).le

lemma wh7_height_ge (α ς : ℝ) (hα : 0 < α) (hς : 1 < ς) {ε : ℝ} (hε : 0 < ε)
    (hεs : ε ≤ (Cpq (α + ς) (α / 2) / (2 : ℝ) ^ rq (α + ς) (α / 2)) ^ 2) :
    1 ≤ phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε := by
  have hp : 1 < α + ς := by linarith
  have hC := wh7_Cpq_pos (p := α + ς) (q := α / 2) hp
  have hr : 1 < rq (α + ς) (α / 2) := wh7_rq_gt1 hα hς
  set C := Cpq (α + ς) (α / 2)
  set r := rq (α + ς) (α / 2)
  have h2r : 0 < (2 : ℝ) ^ r := Real.rpow_pos_of_pos (by norm_num) _
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have h1 : Real.sqrt ε ≤ C / (2 : ℝ) ^ r := by
    calc Real.sqrt ε ≤ Real.sqrt ((C / (2 : ℝ) ^ r) ^ 2) := Real.sqrt_le_sqrt hεs
      _ = C / (2 : ℝ) ^ r := Real.sqrt_sq (by positivity)
  have h2 : (2 : ℝ) ^ r ≤ C / Real.sqrt ε := by
    rw [le_div_iff₀ hs]
    rw [le_div_iff₀ h2r] at h1
    linarith
  have h3 : ((2 : ℝ) ^ r) ^ (1 / r) ≤ (C / Real.sqrt ε) ^ (1 / r) :=
    Real.rpow_le_rpow h2r.le h2 (by positivity)
  have h4 : ((2 : ℝ) ^ r) ^ (1 / r) = 2 := by
    rw [← Real.rpow_mul (by norm_num)]
    have : r * (1 / r) = 1 := by field_simp
    rw [this, Real.rpow_one]
  unfold phaseHeight
  linarith

lemma wh7_D_gt1 (α ς T : ℝ) (hα : 0 < α) (hς : 1 < ς) {N B : ℕ} {ε : ℝ}
    (hW : PhaseLowWindow α ς T N B ε)
    (hH : 1 ≤ phaseHeight (Cpq (α + ς) (α / 2)) (rq (α + ς) (α / 2)) ε) :
    phaseDN α N ≤ Real.pi / 2 / (Cpq (α + ς) (α / 2) *
        ((1 - (2 : ℝ) ^ (1 - rq (α + ς) (α / 2))) / (rq (α + ς) (α / 2) - 1))) *
      Real.sqrt ε := by
  have hp : 1 < α + ς := by linarith
  have hC := wh7_Cpq_pos (p := α + ς) (q := α / 2) hp
  have hr : 1 < rq (α + ς) (α / 2) := wh7_rq_gt1 hα hς
  have hcr := wh7_cr_pos hr
  obtain ⟨hN4, -, -, -, hk, -⟩ := hW
  have hk0 := wh7_Ksvd_nonneg α (N := N) (by omega)
  have hIr := wh7_Ir_gt1 hr hH
  set C := Cpq (α + ς) (α / 2)
  set cr := (1 - (2 : ℝ) ^ (1 - rq (α + ς) (α / 2))) / (rq (α + ς) (α / 2) - 1)
  have h1 : phaseKsvd α N * (C * cr) ≤ Real.sqrt ε := by
    refine le_trans ?_ hk
    calc phaseKsvd α N * (C * cr) = phaseKsvd α N * C * cr := by ring
      _ ≤ phaseKsvd α N * C * Ir (rq (α + ς) (α / 2)) (phaseHeight C (rq (α + ς) (α / 2)) ε) :=
          mul_le_mul_of_nonneg_left hIr (by positivity)
  have h2 : phaseKsvd α N ≤ Real.sqrt ε / (C * cr) := by
    rw [le_div_iff₀ (by positivity)]; exact h1
  rw [wh7_DN_eq]
  calc Real.pi / 2 * phaseKsvd α N ≤ Real.pi / 2 * (Real.sqrt ε / (C * cr)) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = Real.pi / 2 / (C * cr) * Real.sqrt ε := by ring

lemma wh7_D_eq1 (α ς T : ℝ) (hα : 0 < α) (hς : ς = 1) {N B : ℕ} {ε : ℝ}
    (hW : PhaseLowWindow α ς T N B ε)
    (hL0 : 0 < Real.log (1 / ε))
    (hL : -4 * Real.log (Cpq (α + ς) (α / 2)) ≤ Real.log (1 / ε)) :
    phaseDN α N ≤ 2 * Real.pi / (Cpq (α + ς) (α / 2) * Real.log (1 / ε)) * Real.sqrt ε := by
  subst hς
  have hp : 1 < α + 1 := by linarith
  have hC := wh7_Cpq_pos (p := α + 1) (q := α / 2) hp
  have hr := wh7_rq_eq1 hα
  obtain ⟨hN4, -, hε, hε0, hk, -⟩ := hW
  have hk0 := wh7_Ksvd_nonneg α (N := N) (by omega)
  have hεC : ε < Cpq (α + 1) (α / 2) ^ 2 := by
    unfold phaseEps0 at hε0
    exact wh7_eps_lt ε (lt_of_lt_of_le hε0 (min_le_left _ _))
  set C := Cpq (α + 1) (α / 2)
  rw [hr] at hk
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hsC : Real.sqrt ε < C := by
    rw [Real.sqrt_lt' hC]; exact hεC
  have hH : phaseHeight C 1 ε = C / Real.sqrt ε - 1 := by
    unfold phaseHeight
    rw [div_one, Real.rpow_one]
  rw [hH, wh7_Ir_one (by have := (one_lt_div hs).2 hsC; linarith)] at hk
  have hlog : Real.log (1 + (C / Real.sqrt ε - 1)) = Real.log C + Real.log (1 / ε) / 2 := by
    rw [show 1 + (C / Real.sqrt ε - 1) = C / Real.sqrt ε by ring,
      Real.log_div hC.ne' hs.ne', Real.log_sqrt hε.le, one_div, Real.log_inv]
    ring
  rw [hlog] at hk
  have hlow : Real.log (1 / ε) / 4 ≤ Real.log C + Real.log (1 / ε) / 2 := by linarith
  have h1 : phaseKsvd α N * (C * (Real.log (1 / ε) / 4)) ≤ Real.sqrt ε := by
    refine le_trans ?_ hk
    calc phaseKsvd α N * (C * (Real.log (1 / ε) / 4))
        = phaseKsvd α N * C * (Real.log (1 / ε) / 4) := by ring
      _ ≤ phaseKsvd α N * C * (Real.log C + Real.log (1 / ε) / 2) :=
          mul_le_mul_of_nonneg_left hlow (by positivity)
  have h2 : phaseKsvd α N ≤ 4 * Real.sqrt ε / (C * Real.log (1 / ε)) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  rw [wh7_DN_eq]
  calc Real.pi / 2 * phaseKsvd α N ≤ Real.pi / 2 * (4 * Real.sqrt ε / (C * Real.log (1 / ε))) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = 2 * Real.pi / (C * Real.log (1 / ε)) * Real.sqrt ε := by ring

lemma wh7_rate_nonneg (α ς : ℝ) (hς : 1 < ς) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    0 ≤ phaseRatioRate α ς ε := by
  unfold phaseRatioRate
  split_ifs
  · exact absurd ‹ς < 1› (by linarith)
  · exact absurd ‹ς = 1› (by linarith)
  · exact (Real.rpow_pos_of_pos hε _).le
  · exact Real.log_nonneg (by rw [one_div]; exact one_le_inv_iff₀.mpr ⟨hε, hε1.le⟩)
  · exact zero_le_one

/-- Label `prop:app-phase-winners`, part (iv), `0 < α ≤ 1`, `ς ≥ 1` (low-exponent window).
Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1419–1422):

```latex
\item \emph{$0<\alpha\le1$, $\texp\ge1$} (low-exponent window). $\mathsf R\to0$; more
precisely $\mathsf R$ is $O(\log(1/\epsilon)^{-2})$, $O(\epsilon^{(\texp-1)/(p-1)})$,
$O(\sqrt\epsilon\log(1/\epsilon))$ and $O(\sqrt\epsilon)$ for $\texp=1$,
$1<\texp<\alpha+1$, $\texp=\alpha+1$ and $\texp>\alpha+1$ respectively.
```

The `O`-constant `C` is existential before all sequences, with dependence on `α, ς, T` only
(card §6.6). The four displays are guarded by the four cases of `ς`. -/
theorem prop_app_phase_winners_iv (α ς T : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hς : 1 ≤ ς)
    (hT : 4 ≤ T) :
    ∃ C : ℝ, ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, PhaseLowWindow α ς T (Nseq n) (Bseq n) (εs n)) →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) ∧
      (ς = 1 → ∀ᶠ n in atTop,
        |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
          C / Real.log (1 / εs n) ^ 2) ∧
      (1 < ς → ς < α + 1 → ∀ᶠ n in atTop,
        |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
          C * εs n ^ ((ς - 1) / (α + ς - 1))) ∧
      (ς = α + 1 → ∀ᶠ n in atTop,
        |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
          C * Real.sqrt (εs n) * Real.log (1 / εs n)) ∧
      (α + 1 < ς → ∀ᶠ n in atTop,
        |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤ C * Real.sqrt (εs n)) := by
  obtain ⟨cLo, cHi, hcLo, hcc, hcor⟩ := cor_app_phase_ratio_iii α ς T hα hα1 hς hT
  have hcHi : 0 < cHi := lt_of_lt_of_le hcLo hcc
  have hp : 1 < α + ς := by linarith
  have hC0 : 0 < Cpq (α + ς) (α / 2) := wh7_Cpq_pos hp
  obtain ⟨K0, hK0⟩ : ∃ K0 : ℝ, K0 = 2 * Real.pi * cHi / Cpq (α + ς) (α / 2) := ⟨_, rfl⟩
  obtain ⟨K1, hK1⟩ : ∃ K1 : ℝ, K1 = cHi * (Real.pi / 2) /
      (Cpq (α + ς) (α / 2) * ((1 - (2 : ℝ) ^ (1 - rq (α + ς) (α / 2))) /
        (rq (α + ς) (α / 2) - 1))) := ⟨_, rfl⟩
  have hK0nn : 0 ≤ K0 := by rw [hK0]; positivity
  refine ⟨max K0 K1, ?_⟩
  intro Nseq Bseq εs mS mG QS QG hMS hwin
  obtain ⟨hN, hεT, hεpos, hN1, hNB, hSm, hSV, hGm, hGV⟩ := hMS
  have hRnn : ∀ n, 0 ≤ phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := fun n =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have habs : ∀ n, |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| =
      phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) := fun n => abs_of_nonneg (hRnn n)
  have hsand : ∀ᶠ n in atTop, phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ≤
      cHi * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) := by
    filter_upwards [hwin] with n hn
    exact (hcor (Nseq n) (Bseq n) (εs n) (mS n) (mG n) (QS n) (QG n) hn (hSm n) (hSV n)
      (hGm n) (hGV n)).2
  have hεn : Tendsto εs atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hεT, Filter.Eventually.of_forall hεpos⟩
  have hlog : Tendsto (fun n => Real.log (1 / εs n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (hεn.inv_tendsto_nhdsGT_zero.congr (fun n => by simp [one_div]))
  have hε1 : ∀ᶠ n in atTop, εs n < 1 := hεT.eventually (gt_mem_nhds one_pos)
  -- the case ς = 1
  have E1 : ς = 1 → ∀ᶠ n in atTop, |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
      max K0 K1 / Real.log (1 / εs n) ^ 2 := by
    intro h1
    filter_upwards [hsand, hwin, hlog.eventually_ge_atTop (-4 * Real.log (Cpq (α + ς) (α / 2))),
      hlog.eventually_gt_atTop 0] with n hR hW hL hL0
    have hD := wh7_D_eq1 α ς T hα h1 hW hL0 hL
    have hε := hεpos n
    have hrate : phaseRatioRate α ς (εs n) = εs n ^ (-(1 / 2 : ℝ)) / Real.log (1 / εs n) := by
      unfold phaseRatioRate
      rw [if_neg (show ¬ ς < 1 by rw [h1]; exact lt_irrefl _), if_pos h1]
    have hs : 0 < Real.sqrt (εs n) := Real.sqrt_pos.2 hε
    have hP : Real.sqrt (εs n) * εs n ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hε]
      norm_num
    have hE : 0 < εs n ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hε _
    have hrn : 0 ≤ εs n ^ (-(1 / 2 : ℝ)) / Real.log (1 / εs n) := by positivity
    rw [habs]
    calc phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)
        ≤ cHi * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) := hR
      _ ≤ cHi * (2 * Real.pi / (Cpq (α + ς) (α / 2) * Real.log (1 / εs n)) * Real.sqrt (εs n) *
            (εs n ^ (-(1 / 2 : ℝ)) / Real.log (1 / εs n))) := by
          rw [hrate]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hrn) hcHi.le
      _ = K0 / Real.log (1 / εs n) ^ 2 * (Real.sqrt (εs n) * εs n ^ (-(1 / 2 : ℝ))) := by
          rw [hK0]; field_simp
      _ = K0 / Real.log (1 / εs n) ^ 2 := by rw [hP, mul_one]
      _ ≤ max K0 K1 / Real.log (1 / εs n) ^ 2 :=
          div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  -- the cases ς > 1
  have hbound : 1 < ς → ∀ᶠ n in atTop, phaseR T (εs n) (mS n) (mG n) (QS n) (QG n) ≤
      K1 * (Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) := by
    intro h1
    have hc : 0 < (Cpq (α + ς) (α / 2) / (2 : ℝ) ^ rq (α + ς) (α / 2)) ^ 2 := by
      have : 0 < (2 : ℝ) ^ rq (α + ς) (α / 2) := Real.rpow_pos_of_pos (by norm_num) _
      positivity
    filter_upwards [hsand, hwin, hε1, hεT.eventually (gt_mem_nhds hc)] with n hR hW hε1' hlt
    have hH := wh7_height_ge α ς hα h1 (hεpos n) hlt.le
    have hD := wh7_D_gt1 α ς T hα h1 hW hH
    have hrn := wh7_rate_nonneg α ς h1 (hεpos n) hε1'
    calc phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)
        ≤ cHi * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) := hR
      _ ≤ cHi * (Real.pi / 2 / (Cpq (α + ς) (α / 2) *
            ((1 - (2 : ℝ) ^ (1 - rq (α + ς) (α / 2))) / (rq (α + ς) (α / 2) - 1))) *
            Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hD hrn) hcHi.le
      _ = K1 * (Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) := by
          rw [hK1]; ring
  have E2 : 1 < ς → ς < α + 1 → ∀ᶠ n in atTop,
      |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
        max K0 K1 * εs n ^ ((ς - 1) / (α + ς - 1)) := by
    intro h1 h2
    filter_upwards [hbound h1] with n hb
    have hε := hεpos n
    have hrate : phaseRatioRate α ς (εs n) = εs n ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) := by
      unfold phaseRatioRate
      rw [if_neg (show ¬ ς < 1 by linarith), if_neg (show ¬ ς = 1 by linarith), if_pos h2]
    have hex : Real.sqrt (εs n) * εs n ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) =
        εs n ^ ((ς - 1) / (α + ς - 1)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hε]
      congr 1
      have : α + ς - 1 ≠ 0 := by intro h; linarith
      field_simp
      ring
    rw [habs]
    calc phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)
        ≤ K1 * (Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) := hb
      _ = K1 * εs n ^ ((ς - 1) / (α + ς - 1)) := by rw [hrate, hex]
      _ ≤ max K0 K1 * εs n ^ ((ς - 1) / (α + ς - 1)) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (hε.le) _)
  have E3 : ς = α + 1 → ∀ᶠ n in atTop,
      |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤
        max K0 K1 * Real.sqrt (εs n) * Real.log (1 / εs n) := by
    intro h2
    have h1 : 1 < ς := by linarith
    filter_upwards [hbound h1, hε1] with n hb hε1'
    have hε := hεpos n
    have hrate : phaseRatioRate α ς (εs n) = Real.log (1 / εs n) := by
      unfold phaseRatioRate
      rw [if_neg (show ¬ ς < 1 by linarith), if_neg (show ¬ ς = 1 by linarith),
        if_neg (show ¬ ς < α + 1 by linarith), if_pos h2]
    have hL : 0 ≤ Real.log (1 / εs n) :=
      Real.log_nonneg (by rw [one_div]; exact one_le_inv_iff₀.mpr ⟨hε, hε1'.le⟩)
    rw [habs]
    calc phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)
        ≤ K1 * (Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) := hb
      _ = K1 * Real.sqrt (εs n) * Real.log (1 / εs n) := by rw [hrate, mul_assoc]
      _ ≤ max K0 K1 * Real.sqrt (εs n) * Real.log (1 / εs n) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)) hL
  have E4 : α + 1 < ς → ∀ᶠ n in atTop,
      |phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)| ≤ max K0 K1 * Real.sqrt (εs n) := by
    intro h2
    have h1 : 1 < ς := by linarith
    filter_upwards [hbound h1] with n hb
    have hrate : phaseRatioRate α ς (εs n) = 1 := by
      unfold phaseRatioRate
      rw [if_neg (show ¬ ς < 1 by linarith), if_neg (show ¬ ς = 1 by linarith),
        if_neg (show ¬ ς < α + 1 by linarith), if_neg (show ¬ ς = α + 1 by linarith)]
    rw [habs]
    calc phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)
        ≤ K1 * (Real.sqrt (εs n) * phaseRatioRate α ς (εs n)) := hb
      _ = K1 * Real.sqrt (εs n) := by rw [hrate, mul_one]
      _ ≤ max K0 K1 * Real.sqrt (εs n) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _)
  refine ⟨?_, E1, E2, E3, E4⟩
  -- convergence to zero
  have hsq : Tendsto (fun n => Real.sqrt (εs n)) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hεT
    rwa [Real.sqrt_zero] at this
  rcases eq_or_lt_of_le hς with h1 | h1
  · -- ς = 1
    have hg : Tendsto (fun n => max K0 K1 / Real.log (1 / εs n) ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num) |>.comp hlog)
    refine squeeze_zero' (Filter.Eventually.of_forall hRnn) ?_ hg
    filter_upwards [E1 h1.symm] with n hn
    rwa [habs] at hn
  · rcases lt_trichotomy ς (α + 1) with h2 | h2 | h2
    · have he : 0 < (ς - 1) / (α + ς - 1) := div_pos (by linarith) (by linarith)
      have hg : Tendsto (fun n => max K0 K1 * εs n ^ ((ς - 1) / (α + ς - 1))) atTop (𝓝 0) := by
        have := (hεT.rpow_const (p := (ς - 1) / (α + ς - 1)) (Or.inr he.le)).const_mul (max K0 K1)
        rwa [Real.zero_rpow he.ne', mul_zero] at this
      refine squeeze_zero' (Filter.Eventually.of_forall hRnn) ?_ hg
      filter_upwards [E2 h1 h2] with n hn
      rwa [habs] at hn
    · have hg : Tendsto (fun n => max K0 K1 * Real.sqrt (εs n) * Real.log (1 / εs n))
          atTop (𝓝 0) := by
        have h0 := ((tendsto_log_mul_rpow_nhdsGT_zero (r := (1 / 2 : ℝ)) (by norm_num)).comp
          hεn).const_mul (-(max K0 K1))
        rw [mul_zero] at h0
        refine h0.congr (fun n => ?_)
        simp only [Function.comp]
        rw [Real.sqrt_eq_rpow, show (1 : ℝ) / εs n = (εs n)⁻¹ from one_div _, Real.log_inv]
        ring
      refine squeeze_zero' (Filter.Eventually.of_forall hRnn) ?_ hg
      filter_upwards [E3 h2] with n hn
      rwa [habs] at hn
    · have hg : Tendsto (fun n => max K0 K1 * Real.sqrt (εs n)) atTop (𝓝 0) := by
        simpa using hsq.const_mul (max K0 K1)
      refine squeeze_zero' (Filter.Eventually.of_forall hRnn) ?_ hg
      filter_upwards [E4 h2] with n hn
      rwa [habs] at hn

/-- Label `prop:app-phase-winners`, the "so that" identities of part (v):
`1 < τ_c(α) < α + 1` for `1 < α < 2`, and `τ_c(2) = 3`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1423–1427):

```latex
\item \emph{$1<\alpha\le2$, $1\le\texp<\alpha+1$} (window of \cref{thm:app-phase-B}). Put
\[
e_\texp\defeq\frac{\alpha+1-\texp}{2(p-1)},\qquad \texp_c(\alpha)\defeq\frac{\alpha^2-2\alpha+3}{3-\alpha} ,
\]
so that $1<\texp_c(\alpha)<\alpha+1$ for $1<\alpha<2$, and $\texp_c(2)=3$.
```
-/
theorem prop_app_phase_winners_tauc :
    (∀ α : ℝ, 1 < α → α < 2 → 1 < winnersTauC α ∧ winnersTauC α < α + 1) ∧
      winnersTauC 2 = 3 := by
  refine ⟨fun α h1 h2 => ?_, ?_⟩
  · have hd : 0 < 3 - α := by linarith
    unfold winnersTauC
    constructor
    · rw [lt_div_iff₀ hd]; nlinarith
    · rw [div_lt_iff₀ hd]; nlinarith
  · unfold winnersTauC; norm_num

lemma wh6_rate_pow (α ς : ℝ) (hς1 : 1 < ς) (hς2 : ς < α + 1) (ε : ℝ) :
    phaseRatioRate α ς ε = ε ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) := by
  unfold phaseRatioRate
  rw [if_neg (not_lt.mpr hς1.le), if_neg hς1.ne', if_pos hς2]

lemma wh6_tail (α ς : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hς1 : 1 < ς) (hς2 : ς < α + 1)
    (hτ : winnersTauC α ≤ ς) (Nseq : ℕ → ℕ) (εs : ℕ → ℝ)
    (hN : Tendsto (fun n => (Nseq n : ℝ)) atTop atTop) (hN1 : ∀ n, 1 ≤ Nseq n)
    (hεpos : ∀ n, 0 < εs n) (hεN : Tendsto (fun n => εs n * (Nseq n : ℝ)) atTop atTop) :
    Tendsto (fun n => phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)) atTop (𝓝 0) := by
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (α + 1 - ς) / (2 * (α + ς - 1)) := ⟨_, rfl⟩
  have hd2 : 0 < 2 * (α + ς - 1) := by linarith
  have he0 : 0 < e := by rw [he]; exact div_pos (by linarith) hd2
  have hd3 : 0 < 3 - α := by linarith
  have hτ' : α ^ 2 - 2 * α + 3 ≤ ς * (3 - α) := by
    unfold winnersTauC at hτ
    rwa [div_le_iff₀ hd3] at hτ
  have hkey : e ≤ 1 - α / 2 := by
    rw [he, div_le_iff₀ hd2]
    nlinarith [hτ']
  have hrate : ∀ ε : ℝ, phaseRatioRate α ς ε = ε ^ (-e) := fun ε => by
    rw [wh6_rate_pow α ς hς1 hς2 ε, he]
  -- the N-dependence of phaseDN
  have hequiv := (prop_app_phase_prefactors_iv α (by linarith)).2.2.1 hα1 hα2
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ᶠ N : ℕ in atTop,
      phaseDN α N ≤ K * (N : ℝ) ^ (α / 2 - 1) := by
    obtain ⟨c, hc⟩ := hequiv.isBigO.bound
    refine ⟨c * |Real.pi * (1 - α / 2) * zetaR α|, ?_⟩
    filter_upwards [hc, eventually_ge_atTop 1] with N hN hN1
    have hx : 0 ≤ (N : ℝ) ^ (α / 2 - 1) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hpos : 0 < phaseDN α N := wh5_phaseDN_pos α hN1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos, abs_mul, abs_of_nonneg hx] at hN
    exact le_of_le_of_eq hN (by ring)
  have hN' : Tendsto Nseq atTop atTop := tendsto_natCast_atTop_iff.mp hN
  have hK' : ∀ᶠ n in atTop, phaseDN α (Nseq n) ≤ K * (Nseq n : ℝ) ^ (α / 2 - 1) :=
    hN'.eventually hK
  -- the rate `N^{α/2-1} ε^{-e}` tends to zero
  have hG : Tendsto (fun n => (Nseq n : ℝ) ^ (α / 2 - 1) * (εs n) ^ (-e)) atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => (εs n * (Nseq n : ℝ)) ^ (-e)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop he0).comp hεN
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hlim
    · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg (hεpos n).le _)
    · have hN1R : (1 : ℝ) ≤ (Nseq n : ℝ) := by exact_mod_cast hN1 n
      have hNpos : (0 : ℝ) < (Nseq n : ℝ) := by linarith
      calc (Nseq n : ℝ) ^ (α / 2 - 1) * (εs n) ^ (-e)
          ≤ (Nseq n : ℝ) ^ (-e) * (εs n) ^ (-e) :=
            mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN1R (by linarith))
              (Real.rpow_nonneg (hεpos n).le _)
        _ = (εs n * (Nseq n : ℝ)) ^ (-e) := by
            rw [Real.mul_rpow (hεpos n).le hNpos.le]; ring
  have hKG : Tendsto (fun n => K * ((Nseq n : ℝ) ^ (α / 2 - 1) * (εs n) ^ (-e))) atTop (𝓝 0) := by
    have := hG.const_mul K
    rwa [mul_zero] at this
  simp only [hrate]
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hKG
  · exact mul_nonneg (wh5_phaseDN_pos α (hN1 n)).le (Real.rpow_nonneg (hεpos n).le _)
  · filter_upwards [hK'] with n hn
    have hεn : 0 ≤ (εs n) ^ (-e) := Real.rpow_nonneg (hεpos n).le _
    calc phaseDN α (Nseq n) * (εs n) ^ (-e)
        ≤ (K * (Nseq n : ℝ) ^ (α / 2 - 1)) * (εs n) ^ (-e) :=
          mul_le_mul_of_nonneg_right hn hεn
      _ = K * ((Nseq n : ℝ) ^ (α / 2 - 1) * (εs n) ^ (-e)) := by ring

/-- Label `prop:app-phase-winners`, part (v)(a), `1 < α < 2`, `τ_c(α) ≤ ς < α + 1` (window of
`thm:app-phase-B`). Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1429–1430):

```latex
\item If $1<\alpha<2$ and $\texp_c(\alpha)\le\texp<\alpha+1$, then $\mathsf R\to0$ along every
sequence with $N\to\infty$, $\epsilon\downarrow0$ and $\epsilon N\to\infty$.
```

The sequences are assumed with `εN → ∞` (the sequence form of the window). -/
theorem prop_app_phase_winners_v_a (α ς T : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (hς₁ : winnersTauC α ≤ ς) (hς₂ : ς < α + 1) (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      Tendsto (fun n => εs n * (Nseq n : ℝ)) atTop atTop →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) := by
  intro Nseq Bseq εs mS mG QS QG hMS hεN
  have hτ1 : 1 < winnersTauC α := (prop_app_phase_winners_tauc.1 α hα1 hα2).1
  have hς1 : 1 ≤ ς := by linarith
  have hwin : ∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n) :=
    hW.2.2.2 Nseq Bseq εs hMS.1 hMS.2.1 hMS.2.2.1 hMS.2.2.2.1 hMS.2.2.2.2.1 hεN
  have hsand := wh5_sandwich α ς T hα1 hς1 hT Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG
    hMS hwin
  have hlim := wh6_tail α ς hα1 hα2 (by linarith) hς₂ hς₁ Nseq εs hMS.1
    (fun n => hMS.2.2.2.1 n) hMS.2.2.1 hεN
  have hub : Tendsto (fun n => (cHi / cLo) * (phaseDN α (Nseq n) * phaseRatioRate α ς (εs n)))
      atTop (𝓝 0) := by
    have := hlim.const_mul (cHi / cLo)
    rwa [mul_zero] at this
  refine squeeze_zero' (Eventually.of_forall fun n => ?_) ?_ hub
  · unfold phaseR
    exact div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  · filter_upwards [hsand] with n hn
    exact hn.2

lemma wh8_power_window (ω : ℝ) (hω : ω < 1) (Nseq : ℕ → ℕ)
    (εs : ℕ → ℝ) (hN : Tendsto (fun n => (Nseq n : ℝ)) atTop atTop)
    (hN1 : ∀ n, 1 ≤ Nseq n) (hf : ∀ n, εs n = powerEps ω (Nseq n)) :
    Tendsto (fun n => εs n * (Nseq n : ℝ)) atTop atTop := by
  refine (wh_seq_rpow_top hN (show 0 < 1 - ω by linarith)).congr (fun n => ?_)
  have hn : (0 : ℝ) < Nseq n := by exact_mod_cast (show 0 < Nseq n by have := hN1 n; omega)
  rw [hf n, powerEps]
  calc (Nseq n : ℝ) ^ (1 - ω) = (Nseq n : ℝ) ^ (-ω + 1) := by congr 1; ring
    _ = (Nseq n : ℝ) ^ (-ω) * (Nseq n : ℝ) := by rw [Real.rpow_add hn, Real.rpow_one]

lemma wh8_log_window (Nseq : ℕ → ℕ) (εs : ℕ → ℝ)
    (hN : Tendsto (fun n => (Nseq n : ℝ)) atTop atTop)
    (hf : ∀ᶠ n in atTop, εs n = invLogEps (Nseq n)) :
    Tendsto (fun n => εs n * (Nseq n : ℝ)) atTop atTop := by
  refine ((wh_log_Xi 1 1 one_pos).comp hN).congr' ?_
  filter_upwards [hf] with n hn
  simpa only [Function.comp_apply, hn, invLogEps, Real.rpow_neg_one, Real.rpow_one, one_div]

lemma wh8_rate_upper (α ς ε : ℝ) (hα : 1 < α) (hς : 1 ≤ ς)
    (hς2 : ς < α + 1) (hε : 0 < ε) (hL : 1 ≤ Real.log (1 / ε)) :
    phaseRatioRate α ς ε ≤ ε ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) := by
  rcases eq_or_lt_of_le hς with h | h
  · subst ς
    have he : (α + 1 - 1) / (2 * (α + 1 - 1)) = (1 / 2 : ℝ) := by
      have ha : α ≠ 0 := by linarith
      field_simp [ha]
      <;> ring
    simp only [phaseRatioRate, lt_self_iff_false, ↓reduceIte, he]
    exact div_le_self (Real.rpow_nonneg hε.le _) hL
  · rw [wh6_rate_pow α ς h hς2 ε]

lemma wh8_log_product (α ς : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hς : 1 ≤ ς) (hς2 : ς < α + 1) :
    Tendsto (fun N : ℕ => phaseDN α N *
      Real.log (N : ℝ) ^ ((α + 1 - ς) / (2 * (α + ς - 1)))) atTop (𝓝 0) := by
  let e := (α + 1 - ς) / (2 * (α + ς - 1))
  have hd : 0 < 2 * (α + ς - 1) := by linarith
  have he : e < 1 := by dsimp [e]; rw [div_lt_one hd]; linarith
  rcases lt_or_eq_of_le hα2 with hlt | heq
  · have hD := (prop_app_phase_prefactors_iv α (by linarith)).2.2.1 hα1 hlt
    have hE := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ) ^ e))
    have hz : Tendsto (fun x : ℝ => x ^ (α / 2 - 1) * Real.log x ^ e) atTop (𝓝 0) := by
      have hz := (isLittleO_log_rpow_rpow_atTop e (show 0 < 1 - α / 2 by linarith)).tendsto_div_nhds_zero
      refine hz.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [show α / 2 - 1 = -(1 - α / 2) by ring, Real.rpow_neg hx.le]
      ring
    have hz' := (hz.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul
      (Real.pi * (1 - α / 2) * zetaR α)
    rw [mul_zero] at hz'
    exact hE.symm.tendsto_nhds (hz'.congr fun _ => by dsimp; ring)
  · subst α
    have hD := (prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl
    have hE := hD.mul (IsEquivalent.refl (u := fun N : ℕ => Real.log (N : ℝ) ^ e))
    have hz := (wh_seq_rpow_zero
      (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))
      (show e - 1 < 0 by linarith)).const_mul (Real.pi * zetaR 2)
    rw [mul_zero] at hz
    apply hE.symm.tendsto_nhds
    refine hz.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    dsimp only [Function.comp_apply, Pi.mul_apply]
    rw [Real.rpow_sub_one (Real.log_pos hn).ne']
    ring

lemma wh8_log_family (α ς T : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hς : 1 ≤ ς) (hς2 : ς < α + 1) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
    (QS QG : ∀ n, ℝ → ℝ) (hMS : MatchedSeq α ς Nseq Bseq εs mS mG QS QG)
    (hf : ∀ᶠ n in atTop, εs n = invLogEps (Nseq n)) :
    (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
    Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) := by
  have hw := hW.2.2.2 Nseq Bseq εs hMS.1 hMS.2.1 hMS.2.2.1 hMS.2.2.2.1
    hMS.2.2.2.2.1 (wh8_log_window Nseq εs hMS.1 hf)
  refine ⟨hw, ?_⟩
  have hs := wh5_sandwich α ς T hα1 hς hT Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hw
  have hlog : Tendsto (fun n => Real.log (1 / εs n)) atTop atTop :=
    by simpa only [one_div, Function.comp_def, Pi.inv_apply] using Real.tendsto_log_atTop.comp ((tendsto_nhdsWithin_iff.mpr
      ⟨hMS.2.1, Eventually.of_forall hMS.2.2.1⟩ : Tendsto εs atTop (𝓝[>] (0 : ℝ))).inv_tendsto_nhdsGT_zero)
  have hz := (wh8_log_product α ς hα1 hα2 hς hς2).comp
    (tendsto_natCast_atTop_iff.mp hMS.1)
  have hu := hz.const_mul (cHi / cLo)
  rw [mul_zero] at hu
  refine squeeze_zero' (Eventually.of_forall fun n =>
    div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) ?_ hu
  filter_upwards [hs, hf, hlog.eventually_ge_atTop 1,
    hMS.1.eventually_gt_atTop 1] with n hs hn hL hN
  have hln : 0 < Real.log (Nseq n : ℝ) := Real.log_pos hN
  have heq : (εs n) ^ (-((α + 1 - ς) / (2 * (α + ς - 1)))) =
      Real.log (Nseq n : ℝ) ^ ((α + 1 - ς) / (2 * (α + ς - 1))) := by
    rw [hn, invLogEps, one_div, Real.inv_rpow hln.le, ← Real.rpow_neg hln.le, neg_neg]
  refine hs.2.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ?_ (wh5_phaseDN_pos α (hMS.2.2.2.1 n)).le)
    (div_nonneg (lt_of_lt_of_le hW.1 hW.2.1).le hW.1.le))
  rw [← heq]
  exact wh8_rate_upper α ς (εs n) hα1 hς hς2 (hMS.2.2.1 n) hL

lemma wh8_prefactor (α : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2) :
    ∃ c b : ℝ, 0 < c ∧ IsEquivalent atTop (fun N : ℕ => phaseDN α N)
      (fun N => c * (N : ℝ) ^ (α / 2 - 1) * Real.log (N : ℝ) ^ b) := by
  have hz : 0 < zetaR α := lt_of_lt_of_le zero_lt_one (wh5_one_le_zeta hα1)
  rcases lt_or_eq_of_le hα2 with hlt | heq
  · refine ⟨Real.pi * (1 - α / 2) * zetaR α, 0,
      mul_pos (mul_pos Real.pi_pos (by linarith)) hz, ?_⟩
    simpa using (prop_app_phase_prefactors_iv α (by linarith)).2.2.1 hα1 hlt
  · subst α
    refine ⟨Real.pi * zetaR 2, -1, mul_pos Real.pi_pos hz, ?_⟩
    simpa only [div_self (by norm_num : (2 : ℝ) ≠ 0), sub_self, Real.rpow_zero,
      mul_one, Real.rpow_neg_one, div_eq_mul_inv] using
      (prop_app_phase_prefactors_iv 2 (by norm_num)).2.2.2.1 rfl

lemma wh8_power_rate (α ς ω : ℝ) (hα : 1 < α) (hς : 1 ≤ ς)
    (hς2 : ς < α + 1) (hω : 0 < ω) :
    ∃ d k : ℝ, 0 < d ∧ ∀ᶠ N : ℕ in atTop,
      phaseRatioRate α ς (powerEps ω N) =
        d * (N : ℝ) ^ (ω * ((α + 1 - ς) / (2 * (α + ς - 1)))) * Real.log (N : ℝ) ^ k := by
  rcases eq_or_lt_of_le hς with h | h
  · subst ς
    refine ⟨1 / ω, -1, one_div_pos.mpr hω, ?_⟩
    filter_upwards [eventually_ge_atTop 2] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have he : (α + 1 - 1) / (2 * (α + 1 - 1)) = (1 / 2 : ℝ) := by
      have ha : α ≠ 0 := by linarith
      field_simp [ha]
      <;> ring
    have hl : Real.log (1 / ((N : ℝ) ^ (-ω))) = ω * Real.log (N : ℝ) := by
      rw [one_div, Real.log_inv, Real.log_rpow hn]
      ring
    simp only [phaseRatioRate, lt_self_iff_false, ↓reduceIte, powerEps, he, hl]
    rw [← Real.rpow_mul hn.le, Real.rpow_neg_one]
    rw [show -ω * -(1 / 2 : ℝ) = ω * (1 / 2 : ℝ) by ring]
    ring
  · refine ⟨1, 0, zero_lt_one, ?_⟩
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [wh6_rate_pow α ς h hς2, powerEps, ← Real.rpow_mul hn.le]
    simp only [Real.rpow_zero, mul_one, one_mul]
    congr 1
    ring

lemma wh8_power_equiv (α ς ω : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hς : 1 ≤ ς) (hς2 : ς < α + 1) (hω : 0 < ω) :
    ∃ c b : ℝ, 0 < c ∧ IsEquivalent atTop
      (fun N : ℕ => phaseDN α N * phaseRatioRate α ς (powerEps ω N))
      (fun N => c * (N : ℝ) ^ (α / 2 - 1 + ω * ((α + 1 - ς) / (2 * (α + ς - 1)))) *
        Real.log (N : ℝ) ^ b) := by
  obtain ⟨c, b, hc, hD⟩ := wh8_prefactor α hα1 hα2
  obtain ⟨d, k, hd, hr⟩ := wh8_power_rate α ς ω hα1 hς hς2 hω
  refine ⟨c * d, b + k, mul_pos hc hd, ?_⟩
  refine (hD.mul (IsEquivalent.refl (u := fun N => phaseRatioRate α ς (powerEps ω N)))).congr_right ?_
  filter_upwards [hr, eventually_ge_atTop 2] with N hrate hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  dsimp only [Pi.mul_apply]
  rw [hrate, Real.rpow_add (by linarith : (0 : ℝ) < N), Real.rpow_add (Real.log_pos hn)]
  ring

lemma wh8_powlog_zero (a b : ℝ) (ha : a < 0) :
    Tendsto (fun x : ℝ => x ^ a * Real.log x ^ b) atTop (𝓝 0) := by
  have hz := (isLittleO_log_rpow_rpow_atTop b (show 0 < -a by linarith)).tendsto_div_nhds_zero
  refine hz.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.rpow_neg hx.le, div_eq_mul_inv, inv_inv]
  ring

lemma wh8_power_family (α ς T ω : ℝ) (hα1 : 1 < α) (hα2 : α ≤ 2)
    (hς : 1 ≤ ς) (hς2 : ς < α + 1) (hω0 : 0 < ω) (hω1 : ω < 1) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi)
    (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
    (QS QG : ∀ n, ℝ → ℝ) (hMS : MatchedSeq α ς Nseq Bseq εs mS mG QS QG)
    (hf : ∀ n, εs n = powerEps ω (Nseq n)) :
    (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
    (α / 2 - 1 + ω * ((α + 1 - ς) / (2 * (α + ς - 1))) < 0 →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
    (0 < α / 2 - 1 + ω * ((α + 1 - ς) / (2 * (α + ς - 1))) →
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) := by
  have hw := hW.2.2.2 Nseq Bseq εs hMS.1 hMS.2.1 hMS.2.2.1 hMS.2.2.2.1
    hMS.2.2.2.2.1 (wh8_power_window ω hω1 Nseq εs hMS.1 hMS.2.2.2.1 hf)
  have hs := wh5_sandwich α ς T hα1 hς hT Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hw
  obtain ⟨c, b, hc, he⟩ := wh8_power_equiv α ς ω hα1 hα2 hς hς2 hω0
  have heq : IsEquivalent atTop
      (fun n => phaseDN α (Nseq n) * phaseRatioRate α ς (εs n))
      (fun n => c * (Nseq n : ℝ) ^ (α / 2 - 1 + ω * ((α + 1 - ς) / (2 * (α + ς - 1)))) *
        Real.log (Nseq n : ℝ) ^ b) := by
    refine (he.comp_tendsto (tendsto_natCast_atTop_iff.mp hMS.1)).congr_left ?_
    exact Eventually.of_forall fun n => by dsimp; rw [hf n]
  refine ⟨hw, ?_, ?_⟩
  · intro hneg
    have hz := ((wh8_powlog_zero _ b hneg).comp hMS.1).const_mul c
    rw [mul_zero] at hz
    have hprod := heq.symm.tendsto_nhds (hz.congr fun n => by dsimp; ring)
    have hu := hprod.const_mul (cHi / cLo)
    rw [mul_zero] at hu
    exact squeeze_zero' (Eventually.of_forall fun _ =>
      div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (hs.mono fun _ h => h.2) hu
  · intro hpos
    have ht := ((wh_log_Xi _ (-b) hpos).comp hMS.1).const_mul_atTop hc
    have hprod := heq.symm.tendsto_atTop (ht.congr fun n => by dsimp; rw [neg_neg]; ring)
    have hl := hprod.const_mul_atTop (div_pos hW.1 (lt_of_lt_of_le hW.1 hW.2.1))
    exact tendsto_atTop_mono' atTop (hs.mono fun _ h => h.1) hl

lemma wh8_exponent (α ς ω : ℝ) (hα : 1 < α) (hς : 1 ≤ ς) (hς2 : ς < α + 1) :
    α / 2 - 1 + ω * ((α + 1 - ς) / (2 * (α + ς - 1))) =
      ((α + 1 - ς) / (2 * (α + ς - 1))) * (ω - winnersOmegaC α ς) := by
  have hp : α + ς - 1 ≠ 0 := by linarith
  have hd : α + 1 - ς ≠ 0 := by linarith
  unfold winnersOmegaC
  field_simp [hp, hd]
  <;> ring

/-- Label `prop:app-phase-winners`, part (v)(b), `1 < α < 2`, `1 ≤ ς < τ_c(α)` (window of
`thm:app-phase-B`), family `ε_N = N^{-ω}`, `0 < ω < 1`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1431–1434):

```latex
\item If $1<\alpha<2$ and $1\le\texp<\texp_c(\alpha)$, put
$\omega_c\defeq(2-\alpha)(p-1)/(\alpha+1-\texp)\in(0,1)$. For $\epsilon_N=N^{-\omega}$ with
$0<\omega<1$, $\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\epsilon_N=1/\log N$, $\mathsf R\to0$.
```

The threshold `ω_c = winnersOmegaC α ς` lies in `(0, 1)` (part of the claim); the sequences lie
in the window for large `N` (part of the claim). -/
theorem prop_app_phase_winners_v_b_pow (α ς T ω : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (hς : 1 ≤ ς) (hςc : ς < winnersTauC α) (hω0 : 0 < ω) (hω1 : ω < 1) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi) :
    0 < winnersOmegaC α ς ∧ winnersOmegaC α ς < 1 ∧
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ n, εs n = powerEps ω (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      (ω < winnersOmegaC α ς →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0)) ∧
      (winnersOmegaC α ς < ω →
        Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop) := by
  have hς2 : ς < α + 1 := lt_trans hςc (prop_app_phase_winners_tauc.1 α hα1 hα2).2
  have hd : 0 < α + 1 - ς := by linarith
  have hp : 0 < α + ς - 1 := by linarith
  have hωc0 : 0 < winnersOmegaC α ς :=
    div_pos (mul_pos (by linarith) hp) hd
  have hωc1 : winnersOmegaC α ς < 1 := by
    have ht : ς * (3 - α) < α ^ 2 - 2 * α + 3 := by
      have hden : 0 < 3 - α := by linarith
      simpa only [winnersTauC, lt_div_iff₀ hden] using hςc
    unfold winnersOmegaC
    rw [div_lt_one hd]
    nlinarith
  refine ⟨hωc0, hωc1, ?_⟩
  intro Nseq Bseq εs mS mG QS QG hMS hf
  have h := wh8_power_family α ς T ω hα1 hα2.le hς hς2 hω0 hω1 hT
    Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hf
  have he : 0 < (α + 1 - ς) / (2 * (α + ς - 1)) :=
    div_pos hd (mul_pos two_pos hp)
  refine ⟨h.1, ?_, ?_⟩
  · intro hlt
    apply h.2.1
    rw [wh8_exponent α ς ω hα1 hς hς2]
    exact mul_neg_of_pos_of_neg he (sub_neg.mpr hlt)
  · intro hgt
    apply h.2.2
    rw [wh8_exponent α ς ω hα1 hς hς2]
    exact mul_pos he (sub_pos.mpr hgt)

/-- Label `prop:app-phase-winners`, part (v)(b), `1 < α < 2`, `1 ≤ ς < τ_c(α)` (window of
`thm:app-phase-B`), family `ε_N = 1/log N`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1431–1434):

```latex
\item If $1<\alpha<2$ and $1\le\texp<\texp_c(\alpha)$, put
$\omega_c\defeq(2-\alpha)(p-1)/(\alpha+1-\texp)\in(0,1)$. For $\epsilon_N=N^{-\omega}$ with
$0<\omega<1$, $\mathsf R\to0$ if $\omega<\omega_c$ and $\mathsf R\to\infty$ if $\omega>\omega_c$.
For $\epsilon_N=1/\log N$, $\mathsf R\to0$.
```
-/
theorem prop_app_phase_winners_v_b_log (α ς T : ℝ) (hα1 : 1 < α) (hα2 : α < 2)
    (hς : 1 ≤ ς) (hςc : ς < winnersTauC α) (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseBWindowHolds α ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, εs n = invLogEps (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinB α ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) := by
  intro Nseq Bseq εs mS mG QS QG hMS hf
  have hς2 : ς < α + 1 := lt_trans hςc (prop_app_phase_winners_tauc.1 α hα1 hα2).2
  exact wh8_log_family α ς T hα1 hα2.le hς hς2 hT Nst Est cLo cHi hW
    Nseq Bseq εs mS mG QS QG hMS hf

/-- Label `prop:app-phase-winners`, part (v)(c), `α = 2`, `1 ≤ ς < 3` (window of
`thm:app-phase-B`), family `ε_N = N^{-ω}`, `0 < ω < 1`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1435–1436):

```latex
\item If $\alpha=2$ and $1\le\texp<3$, then $\mathsf R\to\infty$ for $\epsilon_N=N^{-\omega}$ with
$0<\omega<1$, and $\mathsf R\to0$ for $\epsilon_N=1/\log N$.
```

The sequences lie in the window for large `N` (part of the claim). -/
theorem prop_app_phase_winners_v_c_pow (ς T ω : ℝ) (hς : 1 ≤ ς) (hςc : ς < 3) (hω0 : 0 < ω)
    (hω1 : ω < 1) (hT : 4 ≤ T) (Nst : ℕ) (Est cLo cHi : ℝ)
    (hW : PhaseBWindowHolds 2 ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq 2 ς Nseq Bseq εs mS mG QS QG →
      (∀ n, εs n = powerEps ω (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinB 2 ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop atTop := by
  intro Nseq Bseq εs mS mG QS QG hMS hf
  have h := wh8_power_family 2 ς T ω (by norm_num) le_rfl hς (by linarith) hω0 hω1 hT
    Nst Est cLo cHi hW Nseq Bseq εs mS mG QS QG hMS hf
  refine ⟨h.1, h.2.2 ?_⟩
  have he : 0 < (2 + 1 - ς) / (2 * (2 + ς - 1)) :=
    div_pos (by linarith) (by linarith)
  norm_num at he ⊢
  exact mul_pos hω0 he

/-- Label `prop:app-phase-winners`, part (v)(c), `α = 2`, `1 ≤ ς < 3` (window of
`thm:app-phase-B`), family `ε_N = 1/log N`. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1435–1436):

```latex
\item If $\alpha=2$ and $1\le\texp<3$, then $\mathsf R\to\infty$ for $\epsilon_N=N^{-\omega}$ with
$0<\omega<1$, and $\mathsf R\to0$ for $\epsilon_N=1/\log N$.
```

The sequences lie in the window for large `N` (part of the claim). -/
theorem prop_app_phase_winners_v_c_log (ς T : ℝ) (hς : 1 ≤ ς) (hςc : ς < 3) (hT : 4 ≤ T)
    (Nst : ℕ) (Est cLo cHi : ℝ) (hW : PhaseBWindowHolds 2 ς T Nst Est cLo cHi) :
    ∀ (Nseq Bseq : ℕ → ℕ) (εs : ℕ → ℝ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq 2 ς Nseq Bseq εs mS mG QS QG →
      (∀ᶠ n in atTop, εs n = invLogEps (Nseq n)) →
      (∀ᶠ n in atTop, PhaseWinB 2 ς T Nst Est (Nseq n) (Bseq n) (εs n)) ∧
      Tendsto (fun n => phaseR T (εs n) (mS n) (mG n) (QS n) (QG n)) atTop (𝓝 0) := by
  intro Nseq Bseq εs mS mG QS QG hMS hf
  exact wh8_log_family 2 ς T (by norm_num) le_rfl hς (by linarith) hT Nst Est cLo cHi hW
    Nseq Bseq εs mS mG QS QG hMS hf

/-! ## The cutoff family -/

lemma wh9_scaled_hit {N : ℕ} (m : RowModel (Fin N)) (Y : ℝ → ℝ)
    (T ε T0 L J : ℝ) (hT : 4 ≤ T) (hε : 0 < ε) (hεF : ε < m.F0 / T)
    (hT0 : 0 < T0) (hL : 0 < L) (hS : 0 < m.S)
    (hb : ∀ i, 1 / (T0 * L) ≤ m.d i)
    (hη : m.η = 2 * Real.sqrt ε / m.S) (hY : IsVolterraSol m Y)
    (hJ : (∫ s in Ioi (0 : ℝ), Real.sqrt (m.forcing s)) = T0 * J) :
    ∃ I : ℝ, 0 ≤ I ∧
      (stepHit m Y T ε).toReal = m.S * T0 / (2 * Real.sqrt ε) * I ∧
      J - Real.sqrt (T * ε) * L ≤ I ∧
      I ≤ J + 2 * Real.sqrt ((Real.sqrt ε * L * Real.log (m.F0 / ε)) * J) +
        Real.sqrt ε * L * Real.log (m.F0 / ε) := by
  have hb0 : 0 < 2 / (T0 * L) := by positivity
  obtain ⟨-, u, -, ht, hI, hlo, hhi⟩ := aux_fixed_hit m m T ε (2 / (T0 * L))
    hT hε hεF hb0 (fun i => by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left (hb i) (show (0 : ℝ) ≤ 2 by norm_num))
    rfl rfl rfl rfl hη hS Y hY
  let V := ∫ v in (0 : ℝ)..u, Real.sqrt (Y v)
  have he : 2 / (2 / (T0 * L)) = T0 * L := by field_simp <;> ring
  have hlo' : T0 * J - T0 * (Real.sqrt (T * ε) * L) ≤ V := by
    rw [hJ] at hlo
    have hh : 2 * Real.sqrt (T * ε) / (2 / (T0 * L)) =
        T0 * (Real.sqrt (T * ε) * L) := by field_simp <;> ring
    simpa only [hh] using hlo
  have hs : Real.sqrt (Real.sqrt ε * (T0 * L * Real.log (m.F0 / ε)) * (T0 * J)) =
      T0 * Real.sqrt ((Real.sqrt ε * L * Real.log (m.F0 / ε)) * J) := by
    rw [show Real.sqrt ε * (T0 * L * Real.log (m.F0 / ε)) * (T0 * J) =
      T0 ^ 2 * ((Real.sqrt ε * L * Real.log (m.F0 / ε)) * J) by ring,
      Real.sqrt_mul (sq_nonneg T0), Real.sqrt_sq hT0.le]
  rw [hJ, he, hs] at hhi
  refine ⟨V / T0, div_nonneg hI hT0.le, ?_, ?_, ?_⟩
  · rw [ht, ENNReal.toReal_ofReal (mul_nonneg
      (one_div_nonneg.mpr (by rw [hη]; positivity)) hI), hη]
    dsimp only [V]
    field_simp
  · apply (le_div_iff₀ hT0).2
    dsimp only [V] at *
    nlinarith [hlo']
  · apply (div_le_iff₀ hT0).2
    dsimp only [V] at *
    nlinarith [hhi]

lemma wh9_matched_SF0 {N : ℕ} (A : PhaseArrays (Fin N))
    (m : RowModel (Fin N)) (ε : ℝ) (hm : IsMatchedModel A m ε) :
    m.S = A.S ∧ m.F0 = A.F0 := by
  constructor
  · unfold RowModel.S PhaseArrays.S
    rw [hm.1, hm.2.1, hm.2.2.1]
  · unfold RowModel.F0 PhaseArrays.F0
    rw [hm.1, hm.2.2.2.1]

lemma wh9_svd_rate (α : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hNB : N ≤ B)
    (hα : 0 < α) (i : Fin N) :
    1 / (svdT0 N B * (N : ℝ) ^ (α / 2)) ≤ (svdArrays α 1 N B).d i := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hg : 0 < gammaRat N B := div_pos hn hb
  have hi : 0 < idxR i := by unfold idxR; positivity
  have hiN : idxR i ≤ (N : ℝ) := by
    unfold idxR
    exact_mod_cast (show i.val + 1 ≤ N by omega)
  have hp := Real.rpow_le_rpow_of_nonpos hi hiN (show -(α / 2) ≤ 0 by linarith)
  dsimp only [svdArrays, svdT0]
  rw [Real.rpow_neg hg.le, ← Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hn.le] at hp
  simpa only [one_div, mul_inv_rev, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr (Real.sqrt_nonneg (gammaRat N B)))

lemma wh9_sgd_rate (α : ℝ) {N B : ℕ} (hN : 1 ≤ N) (hNB : N ≤ B)
    (hα : 0 < α) (i : Fin N) :
    1 / (sgdT0 α N B * (N : ℝ) ^ α) ≤ (sgdArrays α 1 N B).d i := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hm := wh_muBar_pos α hN
  have hi : 0 < idxR i := by unfold idxR; positivity
  have hiN : idxR i ≤ (N : ℝ) := by
    unfold idxR
    exact_mod_cast (show i.val + 1 ≤ N by omega)
  have hp := Real.rpow_le_rpow_of_nonpos hi hiN (show -α ≤ 0 by linarith)
  have hs : Real.sqrt ((B : ℝ) / (Real.pi * muBarOf α N)) = (sgdT0 α N B)⁻¹ := by
    unfold sgdT0
    rw [← Real.sqrt_inv, inv_div]
  dsimp only [sgdArrays, muOf]
  rw [hs, Real.rpow_neg hn.le] at *
  have ht : 0 < sgdT0 α N B := Real.sqrt_pos.2 (div_pos (mul_pos Real.pi_pos hm) hb)
  simpa only [one_div, mul_inv_rev, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hp (inv_nonneg.mpr ht.le)

lemma wh9_epsN (ω : ℝ) (hω : ω < 1) :
    Tendsto (fun N : ℕ => powerEps ω N * (N : ℝ)) atTop atTop := by
  refine (wh_seq_rpow_top (tendsto_natCast_atTop_atTop (R := ℝ))
    (show 0 < 1 - ω by linarith)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [powerEps, ← Real.rpow_add_one hn.ne']
  congr 1
  ring

lemma wh9_decay (δ ω C : ℝ) (hδ : 0 < δ) :
    Tendsto (fun N : ℕ => (N : ℝ) ^ (-δ) * (ω * Real.log (N : ℝ) + C)) atTop (𝓝 0) := by
  have h1 := ((wh8_powlog_zero (-δ) 1 (by linarith)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul ω
  have h2 := (wh_seq_rpow_zero (tendsto_natCast_atTop_atTop (R := ℝ))
    (show -δ < 0 by linarith)).mul_const C
  simpa only [Real.rpow_one, mul_zero, zero_mul, add_zero] using
    (h1.add h2).congr (fun N => by dsimp; simp only [Real.rpow_one]; ring)

lemma wh9_log_bound (α ω T : ℝ) (hα : 0 < α) (hT : 4 ≤ T)
    {N : ℕ} (hN : 1 ≤ N) {F0 : ℝ} (hF : F0 = (1 / 2 : ℝ) * Hsum (α + 1) N)
    (hε : powerEps ω N < 1 / (2 * T)) :
    powerEps ω N < F0 / T ∧
    Real.log (F0 / powerEps ω N) ≤ ω * Real.log (N : ℝ) + Real.log (1 + 1 / α) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp := wh_H_gt1 (show 1 < α + 1 by linarith) hN
  have hf0 : 0 < F0 := by rw [hF]; exact mul_pos (by norm_num) (wh_Hsum_pos _ hN)
  have hε0 : 0 < powerEps ω N := Real.rpow_pos_of_pos hn _
  have hflo : (1 / 2 : ℝ) ≤ F0 := by rw [hF]; linarith [hp.1]
  have hfhi : F0 ≤ 1 + 1 / α := by
    rw [show α + 1 - 1 = α by ring] at hp
    have hz : 0 < 1 + 1 / α := by positivity
    rw [hF]; linarith [hp.2]
  refine ⟨hε.trans_le ?_, ?_⟩
  · have ht : 0 < T := by linarith
    calc 1 / (2 * T) = (1 / 2 : ℝ) / T := by ring
      _ ≤ F0 / T := div_le_div_of_nonneg_right hflo ht.le
  · have h := Real.log_le_log (div_pos hf0 hε0)
      (div_le_div_of_nonneg_right hfhi hε0.le)
    rw [Real.log_div (by positivity : (1 + 1 / α : ℝ) ≠ 0) hε0.ne',
      powerEps, Real.log_rpow hn] at h
    simpa only [powerEps, sub_neg_eq_add, neg_mul, add_comm] using h

lemma wh9_cutoff_hit {N : ℕ} (m : RowModel (Fin N)) (Y : ℝ → ℝ)
    (α ω T T0 q : ℝ) (hα : 0 < α) (hT : 4 ≤ T) (hN : 1 ≤ N)
    (hε : powerEps ω N < 1 / (2 * T)) (hT0 : 0 < T0) (hS : 0 < m.S)
    (hb : ∀ i, 1 / (T0 * (N : ℝ) ^ q) ≤ m.d i)
    (hη : m.η = 2 * Real.sqrt (powerEps ω N) / m.S)
    (hF0 : m.F0 = (1 / 2 : ℝ) * Hsum (α + 1) N)
    (hF : ∀ u, 0 ≤ u → m.forcing (T0 * u) = fNq (N : ℕ∞) (α + 1) q u)
    (hY : IsVolterraSol m Y) :
    ∃ I : ℝ, 0 ≤ I ∧
      (stepHit m Y T (powerEps ω N)).toReal =
        m.S * T0 / (2 * Real.sqrt (powerEps ω N)) * I ∧
      JN N (α + 1) q - Real.sqrt T * (N : ℝ) ^ (q - ω / 2) ≤ I ∧
      I ≤ JN N (α + 1) q +
        2 * Real.sqrt (((N : ℝ) ^ (q - ω / 2) *
          (ω * Real.log (N : ℝ) + Real.log (1 + 1 / α))) * JN N (α + 1) q) +
        (N : ℝ) ^ (q - ω / 2) * (ω * Real.log (N : ℝ) + Real.log (1 + 1 / α)) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : 0 < powerEps ω N := Real.rpow_pos_of_pos hn _
  have hlog := wh9_log_bound α ω T hα hT hN hF0 hε
  have hp : Real.sqrt (powerEps ω N) * (N : ℝ) ^ q = (N : ℝ) ^ (q - ω / 2) := by
    rw [powerEps, Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
    congr 1
    ring
  obtain ⟨I, hI, ht, hlo, hhi⟩ := wh9_scaled_hit m Y T (powerEps ω N) T0
    ((N : ℝ) ^ q) (JN N (α + 1) q) hT he hlog.1 hT0
    (Real.rpow_pos_of_pos hn _) hS hb hη hY
    (wh_forcing_int N (α + 1) q T0 hT0 m.forcing hF)
  have hj : 0 ≤ JN N (α + 1) q :=
    setIntegral_nonneg measurableSet_Ioi (fun u _ => Real.sqrt_nonneg _)
  have hd : Real.sqrt (powerEps ω N) * (N : ℝ) ^ q * Real.log (m.F0 / powerEps ω N) ≤
      (N : ℝ) ^ (q - ω / 2) * (ω * Real.log (N : ℝ) + Real.log (1 + 1 / α)) := by
    rw [hp]
    exact mul_le_mul_of_nonneg_left hlog.2 (Real.rpow_nonneg hn.le _)
  refine ⟨I, hI, ht, ?_, ?_⟩
  · rw [Real.sqrt_mul (by linarith : 0 ≤ T), mul_assoc, hp] at hlo
    exact hlo
  · exact hhi.trans (by gcongr)

lemma wh9_Jlog (q : ℝ) (hq : 0 < q) :
    Tendsto (fun N : ℕ => JN N (2 * q + 1) q / Real.log (N : ℝ))
      atTop (𝓝 (aQ q * q)) := by
  let K := 2 * Cpq (2 * q + 1) q + q * Mpq (2 * q + 1) q *
    (2 : ℝ) ^ (-((2 * q + 1) / q)) / aQ q + 1 / Real.sqrt (2 * (2 * q + 1 - 1))
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hz : Tendsto (fun N : ℕ => (JN N (2 * q + 1) q - aQ q * q * Real.log (N : ℝ)) /
      Real.log (N : ℝ)) atTop (𝓝 0) := by
    apply tendsto_bdd_div_atTop_nhds_zero (b := -K) (B := K) _ _ hl
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (abs_le.mp (lem_app_phase_forcing_integrals_i hq rfl N hN)).1
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact (abs_le.mp (lem_app_phase_forcing_integrals_i hq rfl N hN)).2
  have hh := hz.add_const (aQ q * q)
  rw [zero_add] at hh
  refine hh.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  field_simp [(Real.log_pos hn).ne']
  <;> ring

lemma wh9_ratio_bounds {I J e d : ℝ} (hJ : 0 < J)
    (hlo : J - e ≤ I) (hhi : I ≤ J + 2 * Real.sqrt (d * J) + d) :
    1 - e / J ≤ I / J ∧ I / J ≤ 1 + 2 * Real.sqrt (d / J) + d / J := by
  have hs : Real.sqrt (d * J) = J * Real.sqrt (d / J) := by
    rw [show d * J = J ^ 2 * (d / J) by field_simp <;> ring,
      Real.sqrt_mul (sq_nonneg J), Real.sqrt_sq hJ.le]
  rw [hs] at hhi
  constructor
  · apply (le_div_iff₀ hJ).2
    have he : (1 - e / J) * J = J - e := by field_simp
    rwa [he]
  · apply (div_le_iff₀ hJ).2
    have he : (1 + 2 * Real.sqrt (d / J) + d / J) * J =
        J + 2 * (J * Real.sqrt (d / J)) + d := by field_simp <;> ring
    rwa [he]

lemma wh9_stability (u a J e d : ℕ → ℝ)
    (ha : ∀ᶠ n in atTop, 0 < a n) (hJ : ∀ᶠ n in atTop, 0 < J n)
    (hu : ∀ᶠ n in atTop, ∃ I : ℝ, u n = a n * I ∧ J n - e n ≤ I ∧
      I ≤ J n + 2 * Real.sqrt (d n * J n) + d n)
    (he : Tendsto (fun n => e n / J n) atTop (𝓝 0))
    (hd : Tendsto (fun n => d n / J n) atTop (𝓝 0)) :
    Tendsto (fun n => u n / (a n * J n)) atTop (𝓝 1) := by
  have hlo := (tendsto_const_nhds (x := (1 : ℝ))).sub he
  have hhi := ((tendsto_const_nhds (x := (1 : ℝ))).add (hd.sqrt.const_mul 2)).add hd
  simp only [sub_zero] at hlo
  simp only [Real.sqrt_zero, mul_zero, add_zero] at hhi
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [ha, hJ, hu] with n han hjn hn
    obtain ⟨I, ht, hl, hh⟩ := hn
    have heq : u n / (a n * J n) = I / J n := by rw [ht]; field_simp
    rw [heq]
    exact (wh9_ratio_bounds hjn hl hh).1
  · filter_upwards [ha, hJ, hu] with n han hjn hn
    obtain ⟨I, ht, hl, hh⟩ := hn
    have heq : u n / (a n * J n) = I / J n := by rw [ht]; field_simp
    rw [heq]
    exact (wh9_ratio_bounds hjn hl hh).2

lemma wh9_relative_zero (f J H : ℕ → ℝ) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ᶠ n in atTop, 0 ≤ f n ∧ 0 < H n ∧ c * H n ≤ J n)
    (hf : Tendsto (fun n => f n / H n) atTop (𝓝 0)) :
    Tendsto (fun n => f n / J n) atTop (𝓝 0) := by
  have hz := hf.div_const c
  rw [zero_div] at hz
  apply squeeze_zero' _ _ hz
  · filter_upwards [hpos] with n hn
    exact div_nonneg hn.1 (lt_of_lt_of_le (mul_pos hc hn.2.1) hn.2.2).le
  · filter_upwards [hpos] with n hn
    calc f n / J n ≤ f n / (c * H n) := div_le_div_of_nonneg_left hn.1 (mul_pos hc hn.2.1) hn.2.2
      _ = (f n / H n) / c := by ring

lemma wh9_pair_data (α : ℝ) (hα : 0 < α) {N B : ℕ}
    (hN : 1 ≤ N) (hNB : N ≤ B) (ε : ℝ) (hε : 0 < ε)
    (mS mG : RowModel (Fin N)) (QS QG : ℝ → ℝ)
    (hmS : IsMatchedModel (svdArrays α 1 N B) mS ε)
    (hmG : IsMatchedModel (sgdArrays α 1 N B) mG ε)
    (hQS : IsVolterraSol mS QS) (hQG : IsVolterraSol mG QG) :
    (0 < mS.S ∧ 0 < svdT0 N B) ∧ (0 < mG.S ∧ 0 < sgdT0 α N B) ∧
    (mS.F0 = (1 / 2 : ℝ) * Hsum (α + 1) N) ∧
    (mG.F0 = (1 / 2 : ℝ) * Hsum (α + 1) N) ∧
    (∀ u, 0 ≤ u → mS.forcing (svdT0 N B * u) = fNq (N : ℕ∞) (α + 1) (α / 2) u) ∧
    (∀ u, 0 ≤ u → mG.forcing (sgdT0 α N B * u) = fNq (N : ℕ∞) (α + 1) α u) := by
  have hp : 1 < α + 1 := by linarith
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hts : 0 < svdT0 N B := Real.sqrt_pos.2 (div_pos hn hb)
  have htg : 0 < sgdT0 α N B := Real.sqrt_pos.2
    (div_pos (mul_pos Real.pi_pos (wh_muBar_pos α hN)) hb)
  have hs := wh9_matched_SF0 _ mS ε hmS
  have hg := wh9_matched_SF0 _ mG ε hmG
  have hi := prop_app_phase_prefactors_i α 1 N B hα hp hN hNB ε hε
  have hm := prop_app_phase_prefactors_m1 α 1 N B hα hp hN hNB
  have hf := prop_app_phase_prefactors_ii α 1 N B hα hp hN hNB ε hε
    mS mG hmS hmG QS QG hQS hQG
  refine ⟨⟨?_, hts⟩, ⟨?_, htg⟩, hs.2.trans hm.2.2.1, hg.2.trans hm.2.2.2, hf.1, hf.2.1⟩
  · rw [hs.1, hi.1]
    exact mul_pos (mul_pos (by norm_num) hts) (wh_Hsum_pos _ hN)
  · rw [hg.1, hi.2.2.1]
    exact mul_pos (div_pos (pow_pos hn 2) two_pos) htg

lemma wh9_svd_limit (α ω T : ℝ) (hα : 0 < α) (hω : α < ω) (hT : 4 ≤ T)
    (Nseq Bseq : ℕ → ℕ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
    (QS QG : ℕ → ℝ → ℝ)
    (hMS : MatchedSeq α 1 Nseq Bseq (fun n => powerEps ω (Nseq n)) mS mG QS QG) :
    Tendsto (fun n => (stepHit (mS n) (QS n) T (powerEps ω (Nseq n))).toReal /
      ((svdArrays α 1 (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
        powerEps ω (Nseq n) ^ (-(1 / 2 : ℝ)) * Real.log (1 / powerEps ω (Nseq n)) /
        (4 * Real.sqrt (8 * (α / 2))))) atTop (𝓝 (α / ω)) := by
  let q := α / 2
  let J := fun n => JN (Nseq n) (α + 1) q
  let a := fun n => (mS n).S * svdT0 (Nseq n) (Bseq n) /
    (2 * Real.sqrt (powerEps ω (Nseq n)))
  let e := fun n => Real.sqrt T * (Nseq n : ℝ) ^ (q - ω / 2)
  let d := fun n => (Nseq n : ℝ) ^ (q - ω / 2) *
    (ω * Real.log (Nseq n : ℝ) + Real.log (1 + 1 / α))
  let c := aQ q * q
  have hq : 0 < q := by dsimp [q]; linarith
  have hc : 0 < c := mul_pos (Real.rpow_pos_of_pos (by linarith : 0 < 8 * q) _) hq
  have hw : 0 < ω := lt_trans hα hω
  have hdata := fun n => wh9_pair_data α hα (hMS.2.2.2.1 n) (hMS.2.2.2.2.1 n)
    _ (hMS.2.2.1 n) (mS n) (mG n) (QS n) (QG n)
    (hMS.2.2.2.2.2.1 n) (hMS.2.2.2.2.2.2.2.1 n)
    (hMS.2.2.2.2.2.2.1 n) (hMS.2.2.2.2.2.2.2.2 n)
  have hlog : Tendsto (fun n => Real.log (Nseq n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hMS.1
  have hJlim : Tendsto (fun n => J n / Real.log (Nseq n : ℝ)) atTop (𝓝 c) := by
    have hj := (wh9_Jlog q hq).comp (tendsto_natCast_atTop_iff.mp hMS.1)
    simpa only [J, c, Function.comp_def, show 2 * q + 1 = α + 1 by dsimp [q]; ring] using hj
  have hlow : ∀ᶠ n in atTop, 0 < Real.log (Nseq n : ℝ) ∧
      c / 2 * Real.log (Nseq n : ℝ) ≤ J n := by
    filter_upwards [hlog.eventually_gt_atTop 0,
      hJlim.eventually (lt_mem_nhds (show c / 2 < c by linarith))] with n hl hj
    exact ⟨hl, (le_div_iff₀ hl).mp hj.le⟩
  have he0 : Tendsto e atTop (𝓝 0) := by
    have hh := (wh_seq_rpow_zero hMS.1 (show q - ω / 2 < 0 by dsimp [q]; linarith)).const_mul (Real.sqrt T)
    simpa only [mul_zero] using hh
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have hh := (wh9_decay ((ω - α) / 2) ω (Real.log (1 + 1 / α))
      (by linarith)).comp (tendsto_natCast_atTop_iff.mp hMS.1)
    refine hh.congr (fun n => ?_)
    dsimp only [d, Function.comp_apply]
    rw [show -((ω - α) / 2) = q - ω / 2 by dsimp [q]; ring]
  have hdp : ∀ᶠ n in atTop, 0 ≤ d n := by
    filter_upwards [hlog.eventually_ge_atTop 0] with n hn
    dsimp [d]
    apply mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    have hl : 0 ≤ Real.log (1 + 1 / α) := Real.log_nonneg (by have := one_div_pos.mpr hα; linarith)
    exact add_nonneg (mul_nonneg hw.le hn) hl
  have heJ := wh9_relative_zero e J (fun n => Real.log (Nseq n : ℝ)) (c / 2)
    (by positivity) (by
      filter_upwards [hlow] with n hn
      exact ⟨by dsimp [e]; positivity, hn⟩) (he0.div_atTop hlog)
  have hdJ := wh9_relative_zero d J (fun n => Real.log (Nseq n : ℝ)) (c / 2)
    (by positivity) (by
      filter_upwards [hlow, hdp] with n hn hd
      exact ⟨hd, hn⟩) (hd0.div_atTop hlog)
  have hu : ∀ᶠ n in atTop, ∃ I : ℝ,
      (stepHit (mS n) (QS n) T (powerEps ω (Nseq n))).toReal = a n * I ∧
      J n - e n ≤ I ∧ I ≤ J n + 2 * Real.sqrt (d n * J n) + d n := by
    filter_upwards [hMS.2.1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * T)))] with n hn
    have hd := hdata n
    obtain ⟨I, -, ht, hl, hh⟩ := wh9_cutoff_hit (mS n) (QS n) α ω T
      (svdT0 (Nseq n) (Bseq n)) q hα hT (hMS.2.2.2.1 n) hn hd.1.2 hd.1.1
      (fun i => by
        rw [(hMS.2.2.2.2.2.1 n).2.1]
        exact wh9_svd_rate α (hMS.2.2.2.1 n) (hMS.2.2.2.2.1 n) hα i)
      (by rw [(wh9_matched_SF0 _ _ _ (hMS.2.2.2.2.2.1 n)).1];
          exact (hMS.2.2.2.2.2.1 n).2.2.2.2)
      hd.2.2.1 hd.2.2.2.2.1 (hMS.2.2.2.2.2.2.1 n)
    exact ⟨I, ht, hl, hh⟩
  have hr := wh9_stability _ a J e d
    (Eventually.of_forall fun n => by
      dsimp [a]
      exact div_pos (mul_pos (hdata n).1.1 (hdata n).1.2)
        (mul_pos two_pos (Real.sqrt_pos.2 (hMS.2.2.1 n))))
    (hlow.mono fun n hn => lt_of_lt_of_le (mul_pos (by positivity) hn.1) hn.2)
    hu heJ hdJ
  have hh := (hr.mul hJlim).const_mul (2 * Real.sqrt (8 * q) / ω)
  have hcval : (2 * Real.sqrt (8 * q) / ω) * (1 * c) = α / ω := by
    dsimp [c, aQ]
    rw [Real.rpow_neg (by linarith : 0 ≤ 8 * q), ← Real.sqrt_eq_rpow]
    have hs : Real.sqrt (8 * q) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    dsimp [q] at *
    field_simp
    <;> ring
  rw [hcval] at hh
  refine hh.congr' ?_
  filter_upwards [hMS.1.eventually_gt_atTop 1, hlow] with n hn hjpos
  have hJJ : JN (Nseq n) (α + 1) (α / 2) ≠ 0 :=
    (lt_of_lt_of_le (mul_pos (by positivity : 0 < c / 2) hjpos.1) hjpos.2).ne'
  have hn0 : (0 : ℝ) < Nseq n := by linarith
  have hε : 0 < powerEps ω (Nseq n) := hMS.2.2.1 n
  have hs : (mS n).S ≠ 0 := (hdata n).1.1.ne'
  have ht : svdT0 (Nseq n) (Bseq n) ≠ 0 := (hdata n).1.2.ne'
  have hsq : Real.sqrt (powerEps ω (Nseq n)) ≠ 0 := (Real.sqrt_pos.2 hε).ne'
  have hl : Real.log (Nseq n : ℝ) ≠ 0 := (Real.log_pos hn).ne'
  have hp : powerEps ω (Nseq n) ^ (-(1 / 2 : ℝ)) =
      (Real.sqrt (powerEps ω (Nseq n)))⁻¹ := by
    rw [Real.rpow_neg hε.le, ← Real.sqrt_eq_rpow]
  have he : Real.log (1 / powerEps ω (Nseq n)) = ω * Real.log (Nseq n : ℝ) := by
    rw [one_div, Real.log_inv, powerEps, Real.log_rpow hn0]; ring
  dsimp only [a, J, q]
  rw [← (wh9_matched_SF0 _ _ _ (hMS.2.2.2.2.2.1 n)).1, hp, he]
  field_simp
  <;> ring

lemma wh9_sgd_comparison (α ω T : ℝ) (hα : 0 < α) (hω : α < ω) (hT : 4 ≤ T) :
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (Nseq Bseq : ℕ → ℕ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
        (QS QG : ∀ n, ℝ → ℝ),
        MatchedSeq α 1 Nseq Bseq (fun n => powerEps ω (Nseq n)) mS mG QS QG →
        (∀ᶠ n in atTop,
          cLo * (Nseq n : ℝ) ^ (-(ω - α) / 2) ≤
            (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
              ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
                powerEps ω (Nseq n) ^ (-(1 : ℝ))) ∧
          (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
              ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
                powerEps ω (Nseq n) ^ (-(1 : ℝ))) ≤
            cHi * (Nseq n : ℝ) ^ (-(ω - α) / 2)) ∧
        Tendsto (fun n => (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
          ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
            powerEps ω (Nseq n) ^ (-(1 : ℝ)))) atTop (𝓝 0) := by
  let l := Real.sqrt (Aconst (α + 1)) * (4 : ℝ) ^ (-(α / 2))
  let u := 3 * Cpq (α + 1) α
  have hl : 0 < l := mul_pos (Real.sqrt_pos.2 (by unfold Aconst; positivity))
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hu : 0 ≤ u := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
  let cHi := l + u + 2 * Real.sqrt u + 2
  have hchi : l / 4 ≤ cHi := by dsimp [cHi]; linarith only [hl, hu, Real.sqrt_nonneg u]
  refine ⟨l / 4, cHi, by positivity, hchi, ?_⟩
  intro Nseq Bseq mS mG QS QG hMS
  let H := fun n => (Nseq n : ℝ) ^ (α / 2)
  let e := fun n => Real.sqrt T * (Nseq n : ℝ) ^ (α - ω / 2)
  let d := fun n => (Nseq n : ℝ) ^ (α - ω / 2) *
    (ω * Real.log (Nseq n : ℝ) + Real.log (1 + 1 / α))
  have hdata := fun n => wh9_pair_data α hα (hMS.2.2.2.1 n) (hMS.2.2.2.2.1 n)
    _ (hMS.2.2.1 n) (mS n) (mG n) (QS n) (QG n)
    (hMS.2.2.2.2.2.1 n) (hMS.2.2.2.2.2.2.2.1 n)
    (hMS.2.2.2.2.2.2.1 n) (hMS.2.2.2.2.2.2.2.2 n)
  have hH : ∀ n, 0 < H n := fun n => Real.rpow_pos_of_pos
    (by exact_mod_cast (show 0 < Nseq n by have := hMS.2.2.2.1 n; omega)) _
  have he0 : Tendsto (fun n => e n / H n) atTop (𝓝 0) := by
    have hz := (wh_seq_rpow_zero hMS.1 (show -(ω - α) / 2 < 0 by linarith)).const_mul (Real.sqrt T)
    rw [mul_zero] at hz
    refine hz.congr (fun n => ?_)
    have hn : (0 : ℝ) < Nseq n := by exact_mod_cast (show 0 < Nseq n by have := hMS.2.2.2.1 n; omega)
    dsimp [e, H]
    rw [mul_div_assoc, ← Real.rpow_sub hn]
    congr 2
    ring
  have hd0 : Tendsto (fun n => d n / H n) atTop (𝓝 0) := by
    have hz := (wh9_decay ((ω - α) / 2) ω (Real.log (1 + 1 / α))
      (by linarith)).comp (tendsto_natCast_atTop_iff.mp hMS.1)
    refine hz.congr (fun n => ?_)
    have hn : (0 : ℝ) < Nseq n := by exact_mod_cast (show 0 < Nseq n by have := hMS.2.2.2.1 n; omega)
    dsimp [d, H]
    rw [mul_div_right_comm, ← Real.rpow_sub hn]
    congr 2
    ring
  have hsand : ∀ᶠ n in atTop,
      l / 4 * (Nseq n : ℝ) ^ (-(ω - α) / 2) ≤
        (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
          ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
            powerEps ω (Nseq n) ^ (-(1 : ℝ))) ∧
      (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
          ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
            powerEps ω (Nseq n) ^ (-(1 : ℝ))) ≤
        cHi * (Nseq n : ℝ) ^ (-(ω - α) / 2) := by
    filter_upwards [hMS.1.eventually_ge_atTop (4 * (4 : ℝ) ^ (1 / α)),
      hMS.2.1.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / (2 * T))),
      he0.eventually (gt_mem_nhds (show (0 : ℝ) < l / 2 by positivity)),
      hd0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with n hN he hee hdd
    have hd := hdata n
    have hn : (0 : ℝ) < Nseq n := by exact_mod_cast (show 0 < Nseq n by have := hMS.2.2.2.1 n; omega)
    have hε := hMS.2.2.1 n
    have hJ := lem_app_phase_forcing_integrals_ii hα rfl (Nseq n) hN
    obtain ⟨I, -, ht, hIl, hIu⟩ := wh9_cutoff_hit (mG n) (QG n) α ω T
      (sgdT0 α (Nseq n) (Bseq n)) α hα hT (hMS.2.2.2.1 n) he hd.2.1.2 hd.2.1.1
      (fun i => by
        rw [(hMS.2.2.2.2.2.2.2.1 n).2.1]
        exact wh9_sgd_rate α (hMS.2.2.2.1 n) (hMS.2.2.2.2.1 n) hα i)
      (by rw [(wh9_matched_SF0 _ _ _ (hMS.2.2.2.2.2.2.2.1 n)).1];
          exact (hMS.2.2.2.2.2.2.2.1 n).2.2.2.2)
      hd.2.2.2.1 hd.2.2.2.2.2 (hMS.2.2.2.2.2.2.2.2 n)
    have hee' : e n ≤ l / 2 * H n := (div_le_iff₀ (hH n)).mp hee.le
    have hdd' : d n ≤ H n := (div_le_one (hH n)).mp hdd.le
    have hJl : l * H n ≤ JN (Nseq n) (α + 1) α := hJ.1
    have hJu : JN (Nseq n) (α + 1) α ≤ u * H n := hJ.2
    have hJ0 : 0 ≤ JN (Nseq n) (α + 1) α :=
      setIntegral_nonneg measurableSet_Ioi (fun x _ => Real.sqrt_nonneg _)
    have hsqrt : Real.sqrt (d n * JN (Nseq n) (α + 1) α) ≤ H n * Real.sqrt u := by
      calc Real.sqrt (d n * JN (Nseq n) (α + 1) α)
          ≤ Real.sqrt (H n * (u * H n)) := Real.sqrt_le_sqrt
            ((mul_le_mul_of_nonneg_right hdd' hJ0).trans
              (mul_le_mul_of_nonneg_left hJ.2 (hH n).le))
        _ = H n * Real.sqrt u := by
          rw [show H n * (u * H n) = H n ^ 2 * u by ring,
            Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hH n).le]
    have hIlo : l / 2 * H n ≤ I := by
      change JN (Nseq n) (α + 1) α - e n ≤ I at hIl
      linarith only [hIl, hJl, hee']
    have hIhi : I ≤ (u + 2 * Real.sqrt u + 1) * H n := by
      change I ≤ JN (Nseq n) (α + 1) α + 2 * Real.sqrt (d n * JN (Nseq n) (α + 1) α) + d n at hIu
      nlinarith only [hIu, hJu, hsqrt, hdd']
    have heq : (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
        ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
          powerEps ω (Nseq n) ^ (-(1 : ℝ))) = Real.sqrt (powerEps ω (Nseq n)) / 2 * I := by
      rw [ht, ← (wh9_matched_SF0 _ _ _ (hMS.2.2.2.2.2.2.2.1 n)).1, Real.rpow_neg_one]
      have hss := hd.2.1.1.ne'
      have htt := hd.2.1.2.ne'
      have hsq := (Real.sqrt_pos.2 hε).ne'
      field_simp
      rw [Real.sq_sqrt hε.le]
      ring
    have hp : Real.sqrt (powerEps ω (Nseq n)) * H n = (Nseq n : ℝ) ^ (-(ω - α) / 2) := by
      dsimp [H, powerEps]
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
      congr 1
      ring
    rw [heq]
    constructor
    · have hh := mul_le_mul_of_nonneg_left hIlo (by positivity : 0 ≤ Real.sqrt (powerEps ω (Nseq n)) / 2)
      calc l / 4 * (Nseq n : ℝ) ^ (-(ω - α) / 2)
          = Real.sqrt (powerEps ω (Nseq n)) / 2 * (l / 2 * H n) := by rw [← hp]; ring
        _ ≤ Real.sqrt (powerEps ω (Nseq n)) / 2 * I := hh
    · have hh := mul_le_mul_of_nonneg_left hIhi (by positivity : 0 ≤ Real.sqrt (powerEps ω (Nseq n)) / 2)
      have hc : (u + 2 * Real.sqrt u + 1) / 2 ≤ cHi := by
        dsimp [cHi]; linarith only [hl, hu, Real.sqrt_nonneg u]
      have hh2 := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn.le (-(ω - α) / 2))
      calc Real.sqrt (powerEps ω (Nseq n)) / 2 * I
          ≤ Real.sqrt (powerEps ω (Nseq n)) / 2 * ((u + 2 * Real.sqrt u + 1) * H n) := hh
        _ = ((u + 2 * Real.sqrt u + 1) / 2) * (Nseq n : ℝ) ^ (-(ω - α) / 2) := by rw [← hp]; ring
        _ ≤ cHi * (Nseq n : ℝ) ^ (-(ω - α) / 2) := hh2
  refine ⟨hsand, ?_⟩
  have hz := (wh_seq_rpow_zero hMS.1 (show -(ω - α) / 2 < 0 by linarith)).const_mul cHi
  rw [mul_zero] at hz
  refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg ENNReal.toReal_nonneg ?_)
    (hsand.mono fun _ h => h.2) hz
  rw [← (wh9_matched_SF0 _ _ _ (hMS.2.2.2.2.2.2.2.1 n)).1]
  exact mul_nonneg (mul_nonneg (hdata n).2.1.1.le (hdata n).2.1.2.le)
    (Real.rpow_nonneg (hMS.2.2.1 n).le _)

/-- Label `prop:app-phase-cutoff`, declaration of record. Snapshot `cr-2026-10-23`.

Statement (verbatim, `sections/07-phase-comparison/section.tex`, l.1442–1451):

```latex
\begin{proposition}[A family outside the windows]\label{prop:app-phase-cutoff}
Fix $0<\alpha<1$, $\texp=1$, $\alpha<\omega<1$ and $T\ge4$, let
$\epsilon_N\defeq N^{-\omega}$, and let $B_N\ge N$ be arbitrary integers. Then
$\epsilon_NN\to\infty$, and
\begin{gather*}
\frac{t^{\text{s-SVD}}_{T\epsilon_N}}{\mathcal S_{\text{s-SVD}}T_0^{\text{s-SVD}}\,\epsilon_N^{-1/2}\log(1/\epsilon_N)/(4\sqrt{8q_{\text{s-SVD}}})}\longrightarrow\frac\alpha{\omega}<1,\\
\frac{t^{\text{s-SGD}}_{T\epsilon_N}}{\mathcal S_{\text{s-SGD}}T_0^{\text{s-SGD}}\,\epsilon_N^{-1}}\asymp N^{-(\omega-\alpha)/2}\longrightarrow0 ,
\end{gather*}
with constants depending only on $\alpha$, $\omega$ and $T$.
\end{proposition}
```

The family is `ε_N = N^{-ω}` with arbitrary `B_N ≥ N` (`Nseq n ≤ Bseq n`). The `≍` constants
`c_-, c_+` depend only on `α, ω, T` and are existential before all sequences. -/
theorem prop_app_phase_cutoff (α ω T : ℝ) (hα : 0 < α) (hα1 : α < 1) (hω : α < ω)
    (hω1 : ω < 1) (hT : 4 ≤ T) :
    Tendsto (fun N : ℕ => powerEps ω N * (N : ℝ)) atTop atTop ∧
    (∀ (Nseq Bseq : ℕ → ℕ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
      (QS QG : ∀ n, ℝ → ℝ),
      MatchedSeq α 1 Nseq Bseq (fun n => powerEps ω (Nseq n)) mS mG QS QG →
      Tendsto (fun n => (stepHit (mS n) (QS n) T (powerEps ω (Nseq n))).toReal /
          ((svdArrays α 1 (Nseq n) (Bseq n)).S * svdT0 (Nseq n) (Bseq n) *
            powerEps ω (Nseq n) ^ (-(1 / 2 : ℝ)) * Real.log (1 / powerEps ω (Nseq n)) /
            (4 * Real.sqrt (8 * (α / 2)))))
        atTop (𝓝 (α / ω))) ∧
    α / ω < 1 ∧
    ∃ cLo cHi : ℝ, 0 < cLo ∧ cLo ≤ cHi ∧
      ∀ (Nseq Bseq : ℕ → ℕ) (mS mG : ∀ n, RowModel (Fin (Nseq n)))
        (QS QG : ∀ n, ℝ → ℝ),
        MatchedSeq α 1 Nseq Bseq (fun n => powerEps ω (Nseq n)) mS mG QS QG →
        (∀ᶠ n in atTop,
          cLo * (Nseq n : ℝ) ^ (-(ω - α) / 2) ≤
              (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
                ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
                  powerEps ω (Nseq n) ^ (-(1 : ℝ))) ∧
              (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
                ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
                  powerEps ω (Nseq n) ^ (-(1 : ℝ))) ≤
              cHi * (Nseq n : ℝ) ^ (-(ω - α) / 2)) ∧
        Tendsto (fun n => (stepHit (mG n) (QG n) T (powerEps ω (Nseq n))).toReal /
            ((sgdArrays α 1 (Nseq n) (Bseq n)).S * sgdT0 α (Nseq n) (Bseq n) *
              powerEps ω (Nseq n) ^ (-(1 : ℝ))))
          atTop (𝓝 0) := by
  refine ⟨wh9_epsN ω hω1, ?_, (div_lt_one (lt_trans hα hω)).2 hω,
    wh9_sgd_comparison α ω T hα hω hT⟩
  intro Nseq Bseq mS mG QS QG hMS
  exact wh9_svd_limit α ω T hα hω hT Nseq Bseq mS mG QS QG hMS

end Muon.Phase

end
