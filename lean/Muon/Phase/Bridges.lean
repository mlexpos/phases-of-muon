import Mathlib
import Muon.Phase.IsoRatio
import Muon.Isotropic.One
import Muon.Isotropic.MeasureExistence
import Muon.SignSGD.BatchConstant

/-!
# Appendix H: bridges to the isotropic (F) and batch-constant (I) sections
(task L-H.18)

Snapshot `cr-2026-10-23`. Source: `sections/07-phase-comparison/section.tex`, `cor:app-phase-iso-one`
(l.857–862; second label `rem:app-phase-iso-one` is an alias, one declaration). Card:
`sections/07-phase-comparison/CARD.md` §3 (row `cor:app-phase-iso-one`), §5 (L-H.18), §6 item 10.

This file is the only work package with cross-section prerequisites. It instantiates the
parametric isotropic results of `Muon.Phase.IsoRatio` (L-H.12) at the batch constant
`Muon.SignSGD.batchConst` (section I, `eqn:app-phase-NB`) and identifies the measure-free drift
constant `isoDriftConst` with the section-F drift `Cbeta 0` at aspect ratio one.

Reused, not redefined: `Muon.Phase.isoRho`, `Muon.Phase.isoDriftConst`,
`Muon.Phase.IsIsoSetting` (`IsoRatio`); `Muon.Isotropic.Cbeta` (`ZeroRidge`, `eqn:app-iso-C`); `Muon.Isotropic.thm_app_iso_one`,
`Muon.Isotropic.prop_app_iso_spectral_i`, `Muon.Isotropic.prop_app_iso_measure` (F);
`Muon.SignSGD.batchConst` and `Muon.SignSGD.prop_app_sgd_batch_coefficient_ii` (I).
-/

open MeasureTheory Set

noncomputable section

namespace Muon.Phase

/-- Bridge to F (helper, not a label of record): the measure-free drift constant at aspect ratio one
equals F's square-case constant `C_0(1,1) = Cbeta 0 1 1`, the identification of `CARD.md` §6.7
(`isoDriftConst` is the declaration of record of `C(γ)`; F's `eqn:app-iso-C` at `β = 0`).
Snapshot `cr-2026-10-23`. -/
theorem isoDriftConst_one_eq_Cbeta : isoDriftConst 1 = Muon.Isotropic.Cbeta 0 1 1 := by
  obtain ⟨⟨mo, mi⟩, hpair, _⟩ := Muon.Isotropic.prop_app_iso_measure (γin := 1) (γout := 1)
    one_pos one_pos
  have hmo : Muon.Isotropic.IsIsoMeasurePair 1 1 mo mo := by
    have heq : mo = mi := Muon.Isotropic.isoPair_square_eq hpair
    subst heq
    exact hpair
  have hdef : def_app_phase_scalar 1 mo := (Muon.Isotropic.isoPair_square_iff one_pos mo).2 hmo
  have hform := lem_app_phase_ratio_integral.2.2.2.2.2.2.2.2.1 1 one_pos mo hdef
  have hspec := (Muon.Isotropic.prop_app_iso_spectral_i hmo).1
  rw [← hform.2, hspec]
  norm_num

/-- **cor:app-phase-iso-one**, snapshot `cr-2026-10-23` (declaration of record of the label
`cor:app-phase-iso-one`; `rem:app-phase-iso-one` is an alias). The source environment, verbatim
(`sections/07-phase-comparison/section.tex`, l.857–862):
```
\begin{corollary}[The value at $\gamma=1$]\label{cor:app-phase-iso-one}\label{rem:app-phase-iso-one}
The function $\rho$ of \cref{prop:app-phase-iso-ratio} satisfies
\[
\rho(1)=\frac14\Big(1+\frac{\log(1+\sqrt2)}{\sqrt2}\Big)^2\approx0.6587 .
\]
\end{corollary}
```
The numerical value `≈0.6587` in the display is not part of the statement (CARD §3). -/
theorem cor_app_phase_iso_one :
    isoRho 1 = (1 / 4 : ℝ) * (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2) ^ 2 := by
  have h1 : isoDriftConst 1 = Muon.Isotropic.Cbeta 0 1 1 := isoDriftConst_one_eq_Cbeta
  have h2 : Muon.Isotropic.Cbeta 0 1 1
      = (1 + Real.log (1 + Real.sqrt 2) / Real.sqrt 2) / (2 * Real.sqrt Real.pi) :=
    Muon.Isotropic.thm_app_iso_one.1
  have hs : Real.sqrt Real.pi ^ 2 = Real.pi := Real.sq_sqrt Real.pi_pos.le
  have key : (2 * Real.sqrt Real.pi) ^ 2 = 4 * Real.pi := by
    rw [mul_pow, hs]
    norm_num
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  unfold isoRho
  rw [h1, h2, max_self, div_pow, key, mul_one, mul_one]
  field_simp

/-- Bridge to I (helper): the isotropic setting `IsIsoSetting` of `eqn:app-phase-iso-arrays` and
`eqn:app-phase-NB` holds with `𝒩_B := Muon.SignSGD.batchConst B` (section I,
`prop:app-sgd-batch-coefficient`(ii)
gives the two-sided bound). All other clauses are the hypotheses of `IsIsoSetting`
supplied by the caller; no clause is weakened. -/
theorem isIsoSetting_batchConst (N B : ℕ) (ε T : ℝ) (mS mN : RowModel (Fin N))
    (hN : 1 ≤ N) (hB : 1 ≤ B) (hT : 1 < T) (hε : 0 < ε)
    (hμS : ∀ i, mS.μ i = 1) (hμN : ∀ i, mN.μ i = 1)
    (hdS : ∀ i, mS.d i = isoDriftConst ((N : ℝ) / B))
    (hdN : ∀ i, mN.d i = Muon.SignSGD.batchConst B / Real.sqrt Real.pi)
    (hvS : ∑ i, mS.v i = min (B : ℝ) (N : ℝ)) (hvN : ∑ i, mN.v i = (N : ℝ) ^ 2)
    (hQ : mS.Q0 = mN.Q0) (hF : T * ε < mS.F0)
    (hηS : mS.η = 2 * Real.sqrt ε / mS.S) (hηN : mN.η = 2 * Real.sqrt ε / mN.S) :
    IsIsoSetting N B (Muon.SignSGD.batchConst B) ε T mS mN :=
  ⟨hN, hB, (Muon.SignSGD.prop_app_sgd_batch_coefficient_ii B hB).1,
    (Muon.SignSGD.prop_app_sgd_batch_coefficient_ii B hB).2, hT, hε, hμS, hμN, hdS, hdN,
    hvS, hvN, hQ, hF, hηS, hηN⟩

end Muon.Phase

end
