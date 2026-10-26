import Muon.Dynamics.Basic

/-!
# Appendix E, work package L-E.3: uniformity over diffuse states

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `lem:app-dyn-uniform`
(ll. 2124–2134). Card: `sections/05-dynamics/CARD.md` §3 and the L-E.3 row of §5.

Reused, not redefined: `Muon.Dynamics.DynParams`, `Muon.Dynamics.DynHyp` (its (H1) fields are
restated here because no (H1)-only structure exists and `Basic` is frozen),
`Muon.Dynamics.NormStates`, `Muon.ProportionalRegime`, `Muon.Covariances`, `Muon.opNorm`,
`Muon.Setup.Batch`, `Muon.Setup.IIDBatch`,
`Muon.Setup.dataTarget`.
-/

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

/-- The supremum of `e` over the states `Â ∈ 𝒮_B` with `‖Â‖ ≤ δ`, i.e. the source's
`\bar e_B` (`lem:app-dyn-uniform`), over the normalized states `NormStates C`. Valued in `ℝ≥0∞` (the source allows `+∞` at finite `B`),
so the supremum always exists and the supremum of the empty set is `0`, as the source requires. -/
def dynUniformSup {m n : ℕ} (C : Covariances m n) (e : Mat m n → ℝ) (δ : ℝ) : ℝ≥0∞ :=
  ⨆ A ∈ {A : Mat m n | A ∈ NormStates C ∧ opNorm A ≤ δ}, ENNReal.ofReal (e A)

/-- `lem:app-dyn-uniform` (snapshot `cr-2026-10-23`), uniformity over diffuse states.
Source, `section.tex` ll. 2124–2134, verbatim:
```latex
\begin{lemma}[Uniformity over diffuse states]\label{lem:app-dyn-uniform}
Assume \ref{hyp:app-dyn-data}. For each dimension let $e_B\ge0$ be a function
on the set $\mathscr S_B$ of normalized states such that $e_B(\widehat A_B)\to0$
along every subsequence of dimensions and every choice of
$\widehat A_B\in\mathscr S_B$ along it with $\norm{\widehat A_B}\to0$. Then for every
sequence $\delta_B\to0$,
\[
\bar e_B\defeq\sup\big\{e_B(\widehat A):\ \widehat A\in\mathscr S_B,\ \norm{\widehat A}\le\delta_B\big\}\longrightarrow0 ,
\]
with the convention that the supremum of the empty set is zero.
\end{lemma}
```
Statement encoding: `e k` is `e_B` on the normalized states `NormStates (C k)` (only the values
there are constrained: `e_nonneg`, `e_to_zero`); the sup is `dynUniformSup`, in `ℝ≥0∞` so that
a `+∞` value at finite `B` (F11) is allowed and the empty sup is `0`; `‖·‖` is `opNorm`.
`(H1)` is restated field by field from `DynHyp` (`hyp:app-dyn-data`), as `DynHyp` bundles (H1)–(H4).
-/
theorem lem_app_dyn_uniform {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : DynParams) (m n B : ℕ → ℕ) (C : ∀ k : ℕ, Covariances (m k) (n k))
    -- (H1) `hyp:app-dyn-data`: assum:data-target, assum:proportional-regime
    (regime : ProportionalRegime m n B C)
    (dims : ∀ k : ℕ, ((max (m k) (n k) : ℕ) : ℝ) ≤ p.γstar * (B k : ℝ))
    (normBd : ∀ k : ℕ, opNorm (C k).Sin ≤ p.CSig ∧ opNorm (C k).Sout ≤ p.CSig)
    (x : ∀ k : ℕ, ℕ → Ω → Batch (m k) (n k) (B k))
    (iid : ∀ k t, IIDBatch P (dataTarget (C k)) (fun a ω => x k t ω a))
    (steps_indep : ∀ k : ℕ, iIndepFun (fun t => x k t) P)
    -- the family of error functions `e_B` on the normalized states
    (e : ∀ k : ℕ, Mat (m k) (n k) → ℝ)
    (e_nonneg : ∀ k : ℕ, ∀ A ∈ NormStates (C k), 0 ≤ e k A)
    (e_to_zero : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ A : ∀ j : ℕ, Mat (m (φ j)) (n (φ j)),
      (∀ j : ℕ, A j ∈ NormStates (C (φ j))) →
      Tendsto (fun j : ℕ => opNorm (A j)) atTop (𝓝 0) →
      Tendsto (fun j : ℕ => e (φ j) (A j)) atTop (𝓝 0))
    -- the sequence `δ_B → 0`
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun k : ℕ => dynUniformSup (C k) (e k) (δ k)) atTop (𝓝 0) := by
  classical
  have hevent : ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop,
      ∀ A ∈ NormStates (C k), opNorm A ≤ δ k → e k A ≤ ε := by
    intro ε hε
    by_contra h
    have hbad : ∃ᶠ k in atTop, ∃ A : Mat (m k) (n k),
        A ∈ NormStates (C k) ∧ opNorm A ≤ δ k ∧ ε < e k A := by
      simpa only [not_forall, not_imp, not_le, exists_prop, and_assoc] using
        (Filter.not_eventually.mp h)
    obtain ⟨φ, hφ, hbadφ⟩ := Filter.extraction_of_frequently_atTop hbad
    choose A hA hnorm he using hbadφ
    have hAz : Tendsto (fun j => opNorm (A j)) atTop (𝓝 0) :=
      squeeze_zero (fun j => by unfold opNorm; exact norm_nonneg _) hnorm
        (hδ.comp hφ.tendsto_atTop)
    have hez := e_to_zero φ hφ A hA hAz
    obtain ⟨j, hj⟩ := ((tendsto_order.mp hez).2 ε hε).exists
    exact (he j).not_gt hj
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hrε⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hε
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  filter_upwards [hevent r hrpos] with k hk
  unfold dynUniformSup
  refine iSup_le fun A => iSup_le fun hA => ?_
  exact (ENNReal.ofReal_le_ofReal (hk A hA.1 hA.2)).trans (by simpa using hrε.le)

/-- Eventual form of `lem:app-dyn-uniform` (snapshot `cr-2026-10-23`): the same claim as
`lem_app_dyn_uniform` read as `∀ ε > 0, eventually every normalized state with `‖Â‖ ≤ δ_B`
has `e_B(Â) ≤ ε` (card §6 F11). Source as in `lem_app_dyn_uniform`:
```latex
\begin{lemma}[Uniformity over diffuse states]\label{lem:app-dyn-uniform}
Assume \ref{hyp:app-dyn-data}. For each dimension let $e_B\ge0$ be a function
on the set $\mathscr S_B$ of normalized states such that $e_B(\widehat A_B)\to0$
along every subsequence of dimensions and every choice of
$\widehat A_B\in\mathscr S_B$ along it with $\norm{\widehat A_B}\to0$. Then for every
sequence $\delta_B\to0$,
\[
\bar e_B\defeq\sup\big\{e_B(\widehat A):\ \widehat A\in\mathscr S_B,\ \norm{\widehat A}\le\delta_B\big\}\longrightarrow0 ,
\]
with the convention that the supremum of the empty set is zero.
\end{lemma}
```
-/
theorem lem_app_dyn_uniform_eventual {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (p : DynParams) (m n B : ℕ → ℕ) (C : ∀ k : ℕ, Covariances (m k) (n k))
    -- (H1) `hyp:app-dyn-data`: assum:data-target, assum:proportional-regime
    (regime : ProportionalRegime m n B C)
    (dims : ∀ k : ℕ, ((max (m k) (n k) : ℕ) : ℝ) ≤ p.γstar * (B k : ℝ))
    (normBd : ∀ k : ℕ, opNorm (C k).Sin ≤ p.CSig ∧ opNorm (C k).Sout ≤ p.CSig)
    (x : ∀ k : ℕ, ℕ → Ω → Batch (m k) (n k) (B k))
    (iid : ∀ k t, IIDBatch P (dataTarget (C k)) (fun a ω => x k t ω a))
    (steps_indep : ∀ k : ℕ, iIndepFun (fun t => x k t) P)
    -- the family of error functions `e_B` on the normalized states
    (e : ∀ k : ℕ, Mat (m k) (n k) → ℝ)
    (e_nonneg : ∀ k : ℕ, ∀ A ∈ NormStates (C k), 0 ≤ e k A)
    (e_to_zero : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ A : ∀ j : ℕ, Mat (m (φ j)) (n (φ j)),
      (∀ j : ℕ, A j ∈ NormStates (C (φ j))) →
      Tendsto (fun j : ℕ => opNorm (A j)) atTop (𝓝 0) →
      Tendsto (fun j : ℕ => e (φ j) (A j)) atTop (𝓝 0))
    -- the sequence `δ_B → 0`
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ A ∈ NormStates (C k), opNorm A ≤ δ k → e k A ≤ ε := by
  intro ε hε
  have hsup := lem_app_dyn_uniform P p m n B C regime dims normBd x iid steps_indep
    e e_nonneg e_to_zero δ hδ
  have hbound := ENNReal.tendsto_nhds_zero.mp hsup (ENNReal.ofReal ε)
    (ENNReal.ofReal_pos.mpr hε)
  filter_upwards [hbound] with k hk A hA hδA
  apply (ENNReal.ofReal_le_ofReal_iff hε.le).mp
  unfold dynUniformSup at hk
  exact (le_iSup₂_of_le A ⟨hA, hδA⟩ le_rfl).trans hk

end Muon.Dynamics

end
