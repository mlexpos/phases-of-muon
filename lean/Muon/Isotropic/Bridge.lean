import Muon.Isotropic.VolKernels
import Muon.Isotropic.ZeroRidge
import Muon.PowerLaw.ZeroRidge
import Muon.PowerLaw.Response
import Muon.Drift.Mean
import Muon.Volatility.Half
import Muon.Volatility.LagKernel
import Muon.Volatility.Defs
import Muon.Dynamics.Basic

/-!
# Appendix F, work package L-F.12: the isotropic bridge (interface draft)

Work package L-F.12 (interface draft). Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`.
Labels of this module: `def:app-iso-vol-zero`, `lem:app-iso-lag` (part (ii); part (i) is
`Muon.Isotropic.lem_app_iso_lag_i`, frozen in `VolKernels`), `prop:app-iso-vol-momentum`,
`prop:app-iso-volatility-zero` (alias `rem:app-iso-volatility-zero`), `thm:app-iso-drift`,
`thm:app-iso-volatility`. Card: `sections/05b-isotropic/CARD.md` §3, §5 (L-F.12), §8 (rulings).

Coordinator rulings applied:
* Q2: record statements quote the D and G objects directly (`Muon.Drift.*`, `Muon.Volatility.*`,
  `Muon.PowerLaw.*`); the explicit F objects (`dIso`, `psiIso`, `lagKernel`, `lagCoeff`, `isoVol`) appear
  through the bridge declarations.
* Q9: faithful route. `lem_app_iso_lag_ii` goes through G's `prop_app_pl_response_ii` and `eqn_app_pl_Cil_i`;
  the zero-ridge limits go through G's `prop_app_pl_vol_zero_i`/`_ii` and `cbarZero`, `vZero`.
* Certificates: `cert : Muon.External.GaussianOpNorm`, with `γstar`, `CSig`, as in `Muon.PowerLaw.ZeroRidge`.

Encoding decisions:
* Dimensions: `m` is the output dimension `N_out`, `n` the input dimension `N_in`, `B` the batch. The aspect
  ratios are `γout = m/B`, `γin = n/B` (real), matching `Muon.Isotropic.dIso` and `psiIso`.
* `isoVol cert γstar CSig β m n B ϱ` is `𝔳_iso(ϱ) = B Γ̄[Id, Id](ϱ,ϱ)` (`thm:app-iso-volatility`(ii)), with
  D's `lagGammaBar` at the unit spectrum and the identity test. It is a definition (the source's
  "there is a number … depending on the dimension"), not an existential.
* The limit of `def:app-iso-vol-zero` is `limUnder`; "whenever it exists" is `hasIsoZeroRidgeVol`.
* Hypotheses: standing assumptions of `assum:app-setup-regime` (through `Muon.Setup.SetupRegime`, or as
  `gammaOf N B ≤ γstar`, `1 ≤ CSig`), and `Σ_in = Σ_out = Id` (`hIso`). No other hypothesis is added.
* Every integral or sum carries its integrability or summability as a conclusion conjunct.
* Limits as `ϱ ↓ 0` are `Tendsto … (𝓝[>] 0)`.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open scoped Matrix

noncomputable section

namespace Muon.Isotropic

/-! ## Definitions -/

/-- `𝔳_iso(ϱ) = B Γ̄[Id_{N_out}, Id_{N_in}](ϱ,ϱ)` at momentum `β`, output dimension `m`, input dimension `n`,
batch `B` (`thm:app-iso-volatility`(ii); `eqn:app-vol-Gammabar` of D at `Σ_in = Σ_out = Id`). The row and
input data are the unit spectra and the identity tests. Helper for the volatility labels. -/
def isoVol (cert : Muon.External.GaussianOpNorm) (γstar CSig β : ℝ) (m n B : ℕ) (ϱ : ℝ) : ℝ :=
  (B : ℝ) * Muon.Volatility.lagGammaBar cert γstar CSig β B
    (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
    (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) ϱ ϱ

/-- `def:app-iso-vol-zero`: the zero-ridge isotropic volatility at fixed momentum `β`,
`𝔳_{iso,β} := lim_{ϱ↓0} 𝔳_iso(ϱ)`, as `limUnder` over `𝓝[>] 0`. The definition is partial: its existence is
recorded by `hasIsoZeroRidgeVol` and proved by `prop_app_iso_vol_momentum_ii` (`β > 0`) and
`prop_app_iso_volatility_zero` (`β = 0`). Declaration of record, `Muon.Isotropic.def_app_iso_vol_zero`. -/
def def_app_iso_vol_zero (cert : Muon.External.GaussianOpNorm) (γstar CSig β : ℝ) (m n B : ℕ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ϱ : ℝ => isoVol cert γstar CSig β m n B ϱ)

/-- The "whenever it exists" of `def:app-iso-vol-zero`: `𝔳_iso(ϱ) → v` as `ϱ ↓ 0`. -/
def hasIsoZeroRidgeVol (cert : Muon.External.GaussianOpNorm) (γstar CSig β : ℝ) (m n B : ℕ) (v : ℝ) :
    Prop :=
  Tendsto (fun ϱ : ℝ => isoVol cert γstar CSig β m n B ϱ) (𝓝[>] (0 : ℝ)) (𝓝 v)

/-! ## The lag response in the square case (`lem:app-iso-lag`) -/

private lemma bridge_branch {β γ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hs : 0 < s) {ν : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = isoSpecMeasure γ) :
    Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s) := by
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
    refine ⟨fun j => mul_nonneg (sub_nonneg.mpr hβ1.le) (pow_nonneg hβ0 j), ?_, ?_⟩
    · exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
    · exact ⟨0, by simp [Muon.emaW, sub_ne_zero.mpr hβ1.ne']⟩
  apply Muon.DetEquiv.branchSol_spec (Muon.DetEquiv.Fw_admissible hw) zero_lt_one hγ
  · simp [Muon.DetEquiv.classK, hν, isoSpecMeasure]
  · exact hs

private lemma bridge_coords {β γ s : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < γ) (hs : 0 < s) {ν : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = isoSpecMeasure γ) :
    let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s
    qIso β γ γ s = s * x.1 ^ 2 ∧ x.2.1 = x.1 ∧
      x.2.2.1 = x.2.2.2 ∧ s + x.2.2.1 = γ / x.1 ∧ 0 < x.1 := by
  dsimp only
  have hx := bridge_branch hβ0 hβ1 hγ hs hν
  obtain ⟨ha, hb, hc, hd, he, hf, hg, hh⟩ :=
    prop_app_iso_closure_i hβ0 hβ1 hγ hγ hs hν hν hx
  have hA : 0 ≤ (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).2.2.1 := hx.2.2.1
  have hσpos : 0 < (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).1 := by
    rw [ha]; exact div_pos hγ (by linarith)
  have hsig := hg
  simp only [sub_self, zero_div, sub_eq_zero] at hsig
  have hcoeff : (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).2.2.1 =
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).2.2.2 := by
    rw [hsig] at hd
    exact mul_right_cancel₀ hσpos.ne' (hc.trans hd.symm)
  refine ⟨?_, hsig, hcoeff, ?_, hσpos⟩
  · rw [qIso, lem_app_iso_comparison_iii hβ0 hβ1 hγ hγ hs hν hν hx]
    simp only [isoQ, hsig, pow_two, mul_assoc]
  · apply (eq_div_iff hσpos.ne').2
    rw [ha]
    exact mul_div_cancel₀ _ (by linarith : s +
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).2.2.1 ≠ 0)

private lemma bridge_formula {N B : ℕ} {β s t : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : 0 < Muon.PowerLaw.gammaOf N B) (hs : 0 < s) (ht : 0 < t)
    {ν : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure (Muon.PowerLaw.gammaOf N B))
    (ℓ : ℕ) (i : Fin N) :
    Muon.PowerLaw.respRHS β B (fun _ : Fin N => (1 : ℝ)) ν ν ℓ i s t =
      lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ s t := by
  obtain ⟨hq, hσ, ha, hd, hp⟩ := bridge_coords hβ0 hβ1 hγ hs hν
  obtain ⟨hq', hσ', ha', hd', hp'⟩ := bridge_coords hβ0 hβ1 hγ ht hν
  have hresp : ∀ u, 0 < u → Muon.PowerLaw.respQ β ν ν u =
      qIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) u := by
    intro u hu
    exact (lem_app_iso_comparison_iii hβ0 hβ1 hγ hγ hu hν hν
      (bridge_branch hβ0 hβ1 hγ hu hν)).symm
  have hU : Muon.PowerLaw.respU β B (fun _ : Fin N => (1 : ℝ)) ν ν s t =
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).1 *
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν t).1 /
        Muon.PowerLaw.gammaOf N B := by
    simp only [Muon.PowerLaw.respU, one_pow, mul_one, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hd, hd']
    rw [← mul_assoc, show (B : ℝ)⁻¹ * (N : ℝ) = Muon.PowerLaw.gammaOf N B by
      simp [Muon.PowerLaw.gammaOf, div_eq_mul_inv, mul_comm]]
    field_simp
  have hV : Muon.PowerLaw.respV β B N ν ν s t =
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν s).1 *
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν t).1 /
        Muon.PowerLaw.gammaOf N B := by
    simp only [Muon.PowerLaw.respV, ← ha, ← ha', hd, hd']
    field_simp
  have hD : Muon.PowerLaw.respDelta β B (fun _ : Fin N => (1 : ℝ)) ν ν ℓ s t =
      isoLagDelta β (Muon.PowerLaw.gammaOf N B) ℓ s t := by
    unfold Muon.PowerLaw.respDelta isoLagDelta isoLagX isoLagZ
    rw [hU, hV, hresp s hs, hresp t ht]
    change _ = (1 - _ * _ * Muon.PowerLaw.eLag β _ _ ℓ / _) ^ 2 -
      (Real.sqrt (_ * _) * Muon.PowerLaw.bLag β _ _ ℓ / _) ^ 2
    rw [div_pow, mul_pow, Real.sq_sqrt (by rw [hq, hq']; positivity), hq, hq', hσ, hσ']
    field_simp
  unfold Muon.PowerLaw.respRHS lagKernel
  rw [hD, hresp s hs, hresp t ht]
  change _ = Muon.PowerLaw.bLag β _ _ ℓ * _ * _ / _
  rw [mul_one, mul_one, mul_one, ← ha, ← ha', hd, hd', hq, hq']
  field_simp

private lemma bridge_square_integral (f : ℝ × ℝ → ℝ) (L : ℝ)
    (hpos : ∀ p, 0 ≤ f p)
    (hfi : ∀ T : ℝ, 1 ≤ T → IntegrableOn f (Icc 0 T ×ˢ Icc 0 T))
    (hlim : Tendsto (fun T : ℝ => (4 / Real.pi ^ 2) *
      ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f (x, y)) atTop (𝓝 L)) :
    IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
      (4 / Real.pi ^ 2) * (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y)) = L := by
  let R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  let φ : ℝ → Set (ℝ × ℝ) := fun T => Ioc 0 (max 1 T) ×ˢ Ioc 0 (max 1 T)
  have hsub (T : ℝ) : φ T ⊆ R := fun p hp => ⟨hp.1.1, hp.2.1⟩
  have hm (T : ℝ) : MeasurableSet (φ T) := measurableSet_Ioc.prod measurableSet_Ioc
  have hcov : AECover (volume.restrict R) atTop φ := by
    refine ⟨?_, hm⟩
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    filter_upwards [eventually_ge_atTop (max p.1 p.2)] with T hT
    exact ⟨⟨hp.1, (le_max_left _ _).trans (hT.trans (le_max_right _ _))⟩,
      ⟨hp.2, (le_max_right _ _).trans (hT.trans (le_max_right _ _))⟩⟩
  have hlocal (T : ℝ) : IntegrableOn f (φ T) :=
    (hfi (max 1 T) (le_max_left _ _)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hrestrict (T : ℝ) : (volume.restrict R).restrict (φ T) = volume.restrict (φ T) := by
    rw [Measure.restrict_restrict (hm T), inter_eq_left.mpr (hsub T)]
  have heq (T : ℝ) : (∫ p in φ T, f p ∂(volume.restrict R)) =
      ∫ x in (0 : ℝ)..(max 1 T), ∫ y in (0 : ℝ)..(max 1 T), f (x, y) := by
    rw [hrestrict]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    rw [setIntegral_prod f (by simpa only [← Measure.volume_eq_prod] using hlocal T)]
    simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ max 1 T by linarith [le_max_left 1 T])]
  have hc : (4 / Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hmax : Tendsto (fun T : ℝ => max 1 T) atTop atTop :=
    tendsto_atTop_mono (fun T => le_max_right 1 T) tendsto_id
  have hlim' : Tendsto (fun T : ℝ => ∫ p in φ T, f p ∂(volume.restrict R)) atTop
      (𝓝 (L / (4 / Real.pi ^ 2))) := by
    convert (hlim.comp hmax).div_const (4 / Real.pi ^ 2) using 1
    ext T
    rw [heq]
    exact (mul_div_cancel_left₀ _ hc).symm
  have hint : Integrable f (volume.restrict R) :=
    hcov.integrable_of_integral_tendsto_of_nonneg_ae _
      (fun T => by simpa only [IntegrableOn, hrestrict] using hlocal T)
      (ae_of_all _ hpos) hlim'
  refine ⟨hint, ?_⟩
  have hval := tendsto_nhds_unique (hcov.integral_tendsto_of_countably_generated hint) hlim'
  have hprod : (∫ p in R, f p) = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y) := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod f (by simpa only [IntegrableOn, ← Measure.volume_eq_prod, R] using hint)
  rw [← hprod, hval, mul_div_cancel₀ _ hc]

/-- `lem:app-iso-lag`(ii), snapshot `cr-2026-10-23`. Declaration of record for part (ii); part (i) is
`Muon.Isotropic.lem_app_iso_lag_i`. Square case `N_in = N_out = N`, `γ = N/B`, `β ∈ (0,1)`. Parts: (a) the row
lag kernel `eqn:app-pl-rowkernel` at `μ_1 = … = μ_N = 1` is `lagKernel` and dominates `b_ℓ q q'/γ³`
(G `prop_app_pl_response_ii`, F's `lem_app_iso_lag_i`); (b) for `ϱ > 0` the integrand is integrable on
`(0,∞)²` and the iterated integral `lagCoeff` equals G's row coefficient `C̄_{1,ℓ}(ϱ)` (G `eqn_app_pl_Cil_i`).
The value at `ϱ = 0` (conjunct (b) at zero) is G's `cbarZero`, with integrability of the kernel on `(0,∞)²` (G `prop_app_pl_vol_zero_iii_a`). LaTeX, verbatim:

\begin{lemma}[Isotropic lag response]\label{lem:app-iso-lag}
Let $\bmom\in(0,1)$, $\Nin=\Nout=N$ and $\gamma=N/B$. For $s,s'>0$ put
$q\defeq q(-s)$ and $q'\defeq q(-s')$, let $b_\ell$ and $e_\ell$ be the numbers of
\cref{eqn:app-pl-UV} for these roots, and put
\[
X_\ell\defeq\frac{q\,q'\,e_\ell}\gamma,\qquad Z_\ell\defeq\frac{\sqrt{qq'}\,b_\ell}\gamma,\qquad
\Delta_\ell\defeq(1-X_\ell)^2-Z_\ell^2\qquad(\ell\ge0).
\]
\begin{enumerate}[label=(\roman*)]
\item $0\le b_\ell\le\bmom^\ell\sw2$, $0\le e_\ell\le3\bmom^{2\ell}\sw4$, $0\le X_\ell<1$ and $0<\Delta_\ell\le1$.
\item The row lag kernel \cref{eqn:app-pl-rowkernel} at $\mu_1=\dots=\mu_N=1$ is the
same for every row and equals
\[
\mathfrak k_{1,\ell}(s,s')=\frac{b_\ell\,q\,q'}{\gamma^3\,\Delta_\ell}\ \ge\ \frac{b_\ell\,q\,q'}{\gamma^3},
\]
and for every $\ridge\ge0$ the row lag coefficient is
\begin{equation}\label{eqn:app-iso-lag-integral}
\overline C_{1,\ell}(\ridge)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{1,\ell}(\ridge+x^2,\ridge+y^2)\,\dif x\,\dif y ,
\end{equation}
where $\overline C_{1,\ell}(0)$ is the limit of \cref{prop:app-iso-vol-momentum}(ii).
\end{enumerate}
\end{lemma}
-/
theorem lem_app_iso_lag_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig) (i : Fin N) (ℓ : ℕ) :
    (∀ s s' : ℝ, 0 < s → 0 < s' →
      (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (Muon.Volatility.iotaF s) (Muon.Volatility.iotaF s') =
        lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ s s' ∧
      isoLagB β (Muon.PowerLaw.gammaOf N B) ℓ s s' * qIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) s *
          qIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) s' / (Muon.PowerLaw.gammaOf N B) ^ 3 ≤
        lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ s s') ∧
    (∀ ϱ : ℝ, 0 < ϱ →
      IntegrableOn (fun p : ℝ × ℝ => lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ (ϱ + p.1 ^ 2) (ϱ + p.2 ^ 2))
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
      lagCoeff β (Muon.PowerLaw.gammaOf N B) ϱ ℓ =
        Muon.Volatility.lagRowBar cert γstar CSig β ℓ B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) ∧
    (IntegrableOn (fun p : ℝ × ℝ => lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ (p.1 ^ 2) (p.2 ^ 2))
          (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
      lagCoeff β (Muon.PowerLaw.gammaOf N B) 0 ℓ =
        Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ℓ) := by
  classical
  have hγpos : 0 < Muon.PowerLaw.gammaOf N B :=
    div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  let ν : FiniteMeasure ℝ := ⟨isoSpecMeasure (Muon.PowerLaw.gammaOf N B), by
    unfold isoSpecMeasure
    exact (Measure.dirac (1 : ℝ)).smul_finite ENNReal.ofReal_ne_top⟩
  have hν : (ν : Measure ℝ) = isoSpecMeasure (Muon.PowerLaw.gammaOf N B) := rfl
  have hνpl : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) •
      ∑ _ : Fin N, Measure.dirac (1 : ℝ) := by
    ext A hA
    by_cases h : (1 : ℝ) ∈ A
    · simp [ν, isoSpecMeasure, Measure.smul_apply, hA, h,
        Muon.PowerLaw.gammaOf, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg B))]
    · simp [ν, isoSpecMeasure, Measure.smul_apply, hA, h]
  have hker (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
      (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B
        (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Muon.Volatility.iotaF s) (Muon.Volatility.iotaF t) =
      lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ s t := by
    rw [Muon.PowerLaw.prop_app_pl_response_ii cert γstar CSig hB hN _ (fun _ => zero_lt_one)
      hβ0.le hβ1 hγ (fun _ => hC1) hC1 hνpl hν ℓ hs ht i]
    exact bridge_formula hβ0.le hβ1 hγpos hs ht hν ℓ i
  have hqpos (s : ℝ) (hs : 0 < s) : 0 < qIso β (Muon.PowerLaw.gammaOf N B)
      (Muon.PowerLaw.gammaOf N B) s := by
    obtain ⟨hq, -, -, -, hp⟩ := bridge_coords hβ0.le hβ1 hγpos hs hν
    rw [hq]; positivity
  have hnonneg (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
      0 ≤ lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ s t := by
    have hb := (lem_app_iso_lag_i hβ0 hβ1 hγpos hs ht ℓ).1.1
    have hd := (lem_app_iso_lag_i hβ0 hβ1 hγpos hs ht ℓ).2.2.2.1
    unfold lagKernel
    exact div_nonneg (mul_nonneg (mul_nonneg hb (hqpos s hs).le) (hqpos t ht).le)
      (mul_nonneg (pow_nonneg hγpos.le _) hd.le)
  refine ⟨?_, ?_, ?_⟩
  · intro s t hs ht
    refine ⟨hker s t hs ht, ?_⟩
    obtain ⟨hb, -, -, hd⟩ := lem_app_iso_lag_i hβ0 hβ1 hγpos hs ht ℓ
    unfold lagKernel
    apply div_le_div_of_nonneg_left
      (mul_nonneg (mul_nonneg hb.1 (hqpos s hs).le) (hqpos t ht).le)
      (mul_pos (pow_pos hγpos _) hd.1)
    exact (mul_le_mul_of_nonneg_left hd.2 (pow_nonneg hγpos.le _)).trans_eq (mul_one _)
  · intro ϱ hϱ
    obtain ⟨-, -, hfi, hlim⟩ := Muon.PowerLaw.eqn_app_pl_Cil_i cert γstar CSig hB hN
      (fun _ : Fin N => (1 : ℝ)) (fun _ _ _ => le_rfl) (fun _ => zero_lt_one)
      hβ0 hβ1 hγ (fun _ => hC1) hC1 i ℓ hϱ
    have heq : ∀ x y : ℝ, (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B
        (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Muon.Volatility.iotaF (ϱ + x ^ 2)) (Muon.Volatility.iotaF (ϱ + y ^ 2)) =
        lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ (ϱ + x ^ 2) (ϱ + y ^ 2) :=
      fun x y => hker _ _ (by positivity) (by positivity)
    simp_rw [heq] at hfi hlim
    exact bridge_square_integral _ _ (fun p => hnonneg _ _ (by positivity) (by positivity)) hfi hlim
  · obtain ⟨-, -, hfi, hval⟩ := Muon.PowerLaw.prop_app_pl_vol_zero_iii_a cert γstar CSig
      hB hN (fun _ : Fin N => (1 : ℝ)) (fun _ _ _ => le_rfl) (fun _ => zero_lt_one)
      hβ0 hβ1 hγ (fun _ => hC1) hC1 i ℓ
    have heq : ∀ x ∈ Ioi (0 : ℝ), ∀ y ∈ Ioi (0 : ℝ),
        (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B
          (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (Muon.Volatility.iotaF (x ^ 2)) (Muon.Volatility.iotaF (y ^ 2)) =
        lagKernel β (Muon.PowerLaw.gammaOf N B) ℓ (x ^ 2) (y ^ 2) := by
      intro x hx y hy
      exact hker _ _ (sq_pos_of_pos hx) (sq_pos_of_pos hy)
    refine ⟨hfi.congr_fun (fun p hp => heq p.1 hp.1 p.2 hp.2)
      (measurableSet_Ioi.prod measurableSet_Ioi), ?_⟩
    unfold lagCoeff
    simp only [zero_add]
    rw [hval]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    exact setIntegral_congr_fun measurableSet_Ioi (fun y hy => (heq x hx y hy).symm)


/-! ## Zero-ridge limits with momentum (`prop:app-iso-vol-momentum`) -/

private lemma bridge_momentum_weightSeq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Muon.DetEquiv.WeightSeq (Muon.emaW β) := by
  refine ⟨fun j => mul_nonneg (sub_nonneg.mpr hβ1.le) (pow_nonneg hβ0 j), ?_, ?_⟩
  · exact (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - β)
  · exact ⟨0, by simp [Muon.emaW, sub_ne_zero.mpr hβ1.ne']⟩

private lemma bridge_momentum_link {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    IsIsoLink (Muon.DetEquiv.rW (Muon.emaW β)) := by
  have hw := bridge_momentum_weightSeq hβ0 hβ1
  refine ⟨ContinuousOn.mul continuousOn_id (Muon.DetEquiv.Fw_admissible hw).contOn,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.1,
    (Muon.DetEquiv.lem_app_de_scalar_iii hw).2.2.1⟩

private lemma bridge_momentum_root {β γin γout ϱ : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 < ϱ) :
    0 ≤ qIso β γin γout ϱ ∧ psiIso β γin γout ϱ < min γin γout ∧
      ϱ * qIso β γin γout ϱ =
        (γout - psiIso β γin γout ϱ) * (γin - psiIso β γin γout ϱ) := by
  have hr := bridge_momentum_link hβ0 hβ1
  obtain ⟨hD, hG⟩ := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 ϱ hϱ
  change 0 ≤ qIso β γin γout ϱ ∧ psiIso β γin γout ϱ < min γin γout at hD
  change ϱ * qIso β γin γout ϱ -
    (γout - psiIso β γin γout ϱ) * (γin - psiIso β γin γout ϱ) = 0 at hG
  exact ⟨hD.1, hD.2, by linarith⟩

private lemma bridge_momentum_K_spec {β γin γout : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    0 ≤ isoK β (min γin γout) ∧
      Muon.DetEquiv.rW (Muon.emaW β) (isoK β (min γin γout)) = min γin γout := by
  have hbij := (lem_app_iso_weights_i hβ0.le hβ1).2.2.1 hβ0
  have hex : ∃ q : ℝ, 0 ≤ q ∧
      Muon.DetEquiv.rW (Muon.emaW β) q = min γin γout := by
    obtain ⟨q, hq, hqeq⟩ := hbij.2.2.2
      (show min γin γout ∈ Ici (0 : ℝ) from mem_Ici.mpr (le_min hγin.le hγout.le))
    exact ⟨q, hq, hqeq⟩
  unfold isoK isoQlevel
  rw [if_neg hβ0.ne', dif_pos hex]
  exact hex.choose_spec

private lemma bridge_momentum_q_le_K {β γin γout ϱ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) (hϱ : 0 < ϱ) :
    qIso β γin γout ϱ ≤ isoK β (min γin γout) := by
  obtain ⟨hq, hψ, -⟩ := bridge_momentum_root hβ0.le hβ1 hγin hγout hϱ
  obtain ⟨hK, hKspec⟩ := bridge_momentum_K_spec hβ0 hβ1 hγin hγout
  by_contra h
  have hKq : isoK β (min γin γout) < qIso β γin γout ϱ := lt_of_not_ge h
  have hmono := (bridge_momentum_link hβ0.le hβ1).2.1
    (mem_Ici.mpr hK) (mem_Ici.mpr hq) hKq
  unfold psiIso at hψ
  rw [hKspec] at hmono
  linarith

private lemma bridge_momentum_sqrt_bound {β γin γout ϱ : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hγin : 0 < γin) (hγout : 0 < γout)
    (hϱ : 0 < ϱ) :
    min γin γout - psiIso β γin γout ϱ ≤
      Real.sqrt (ϱ * isoK β (min γin γout)) := by
  obtain ⟨hq, hψ, heq⟩ := bridge_momentum_root hβ0.le hβ1 hγin hγout hϱ
  have hqK := bridge_momentum_q_le_K hβ0 hβ1 hγin hγout hϱ
  have hδ : 0 ≤ min γin γout - psiIso β γin γout ϱ := by linarith
  have hout : min γin γout - psiIso β γin γout ϱ ≤
      γout - psiIso β γin γout ϱ := by linarith [min_le_right γin γout]
  have hin : min γin γout - psiIso β γin γout ϱ ≤
      γin - psiIso β γin γout ϱ := by linarith [min_le_left γin γout]
  have hout0 : 0 ≤ γout - psiIso β γin γout ϱ := hδ.trans hout
  have hsq : (min γin γout - psiIso β γin γout ϱ) ^ 2 ≤
      ϱ * isoK β (min γin γout) := by
    calc
      (min γin γout - psiIso β γin γout ϱ) ^ 2 =
          (min γin γout - psiIso β γin γout ϱ) *
            (min γin γout - psiIso β γin γout ϱ) := pow_two _
      _ ≤ (γout - psiIso β γin γout ϱ) *
          (γin - psiIso β γin γout ϱ) := mul_le_mul hout hin hδ hout0
      _ = ϱ * qIso β γin γout ϱ := heq.symm
      _ ≤ ϱ * isoK β (min γin γout) := mul_le_mul_of_nonneg_left hqK hϱ.le
  exact Real.le_sqrt_of_sq_le hsq

/-- `prop:app-iso-vol-momentum`(i), snapshot `cr-2026-10-23`. Declaration of record for part (i): the limit
`ψ(ϱ) → γ∧` (with the row and column versions `ψ/γout`, `ψ/γin`) and the two bounds for `ϱ > 0`, with
`K_β = isoK β γ∧` the unique `q > 0` with `q F_β(q) = γ∧`. Pure real analysis at real aspect ratios. LaTeX,
verbatim (the whole environment, which also contains parts (ii) and (iii)):

\begin{proposition}[Zero-ridge limits with momentum]\label{prop:app-iso-vol-momentum}
Let $\bmom\in(0,1)$ and $\gin,\gout>0$, put $\gamma_\wedge\defeq\min(\gin,\gout)$ and
$\gamma_\vee\defeq\max(\gin,\gout)$, and let $K_\bmom$ be the unique $q>0$ with
$q\Fw(q)=\gamma_\wedge$.
\begin{enumerate}[label=(\roman*)]
\item As $\ridge\downarrow0$, $\psi(\ridge)\to\gamma_\wedge$, and for every $\ridge>0$
\[
\gamma_\wedge-\psi(\ridge)\le\frac{\ridge\,K_\bmom}{\gamma_\vee-\gamma_\wedge}\quad(\gin\ne\gout),\qquad
\gamma_\wedge-\psi(\ridge)\le\sqrt{\ridge\,K_\bmom}\quad(\gin=\gout).
\]
In particular the same-time row and column coefficients $\psi(\ridge)/\gout$ and
$\psi(\ridge)/\gin$ of \cref{eqn:app-iso-vol-rows} tend to $\gamma_\wedge/\gout$ and
$\gamma_\wedge/\gin$, and the same-time total $B\psi(\ridge)$ of
\cref{eqn:app-iso-vol-total} tends to $\min\{\Nin,\Nout\}$.
\item Let $\Nin=\Nout=N$ and $\gamma=N/B$. For $\ell\ge0$ let $\overline C_{1,\ell}(\ridge)$ be the
row lag coefficient of \cref{eqn:app-pl-Cil} for the spectrum $\mu_1=\dots=\mu_N=1$,
which is the same for every row. Then $\overline C_{1,0}(\ridge)=\psi(\ridge)/\gamma$; for
every $\ell\ge0$ the limit $\overline C_{1,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{1,\ell}(\ridge)$
exists and is nonnegative, with $\overline C_{1,0}(0)=1$; and the limit of
\cref{def:app-iso-vol-zero} exists and equals
\[
\mathfrak v_{\mathrm{iso},\bmom}=N\Big(1+2\sum_{\ell\ge1}\overline C_{1,\ell}(0)\Big)\ge N .
\]
\item If moreover $N>B$, then $\mathfrak v_{\mathrm{iso},\bmom}\ge N>B=\mathfrak v_{\mathrm{iso},0}$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_iso_vol_momentum_i {β γin γout : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγin : 0 < γin) (hγout : 0 < γout) :
    Tendsto (fun ϱ : ℝ => psiIso β γin γout ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout)) ∧
    (∀ ϱ : ℝ, 0 < ϱ →
      (γin ≠ γout →
        min γin γout - psiIso β γin γout ϱ ≤
          ϱ * isoK β (min γin γout) / (max γin γout - min γin γout)) ∧
      (γin = γout →
        min γin γout - psiIso β γin γout ϱ ≤ Real.sqrt (ϱ * isoK β (min γin γout)))) ∧
    Tendsto (fun ϱ : ℝ => psiIso β γin γout ϱ / γout) (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout / γout)) ∧
    Tendsto (fun ϱ : ℝ => psiIso β γin γout ϱ / γin) (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout / γin)) ∧
    (∀ B Nin Nout : ℕ, 0 < B → γin = (Nin : ℝ) / (B : ℝ) → γout = (Nout : ℝ) / (B : ℝ) →
      Tendsto (fun ϱ : ℝ => (B : ℝ) * psiIso β γin γout ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (min (Nin : ℝ) (Nout : ℝ)))) := by
  have hsqrt : Tendsto (fun ϱ : ℝ => Real.sqrt (ϱ * isoK β (min γin γout)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous
        (fun ϱ : ℝ => Real.sqrt (ϱ * isoK β (min γin γout))) := by fun_prop
    have hc0 := hc.continuousAt.tendsto.mono_left
      (show (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) from inf_le_left)
    simpa only [zero_mul, Real.sqrt_zero] using hc0
  have hlim : Tendsto (fun ϱ : ℝ => psiIso β γin γout ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout)) := by
    have hlower : Tendsto
        (fun ϱ : ℝ => min γin γout - Real.sqrt (ϱ * isoK β (min γin γout)))
        (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout)) := by
      simpa only [sub_zero] using
        (tendsto_const_nhds.sub hsqrt : Tendsto
          (fun ϱ : ℝ => min γin γout - Real.sqrt (ϱ * isoK β (min γin γout)))
          (𝓝[>] (0 : ℝ)) (𝓝 (min γin γout - 0)))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower tendsto_const_nhds ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
      linarith [bridge_momentum_sqrt_bound hβ0 hβ1 hγin hγout hϱ]
    · filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
      exact (bridge_momentum_root hβ0.le hβ1 hγin hγout hϱ).2.1.le
  refine ⟨hlim, ?_, hlim.div_const γout, hlim.div_const γin, ?_⟩
  · intro ϱ hϱ
    refine ⟨?_, ?_⟩
    · intro hne
      obtain ⟨hq, hψ, heq⟩ := bridge_momentum_root hβ0.le hβ1 hγin hγout hϱ
      have hqK := bridge_momentum_q_le_K hβ0 hβ1 hγin hγout hϱ
      rcases lt_or_gt_of_ne hne with hio | hoi
      · rw [min_eq_left hio.le, max_eq_right hio.le, le_div_iff₀ (sub_pos.mpr hio)]
        simp only [min_eq_left hio.le] at hψ hqK
        have hfac : (γin - psiIso β γin γout ϱ) * (γout - γin) ≤
            (γout - psiIso β γin γout ϱ) * (γin - psiIso β γin γout ϱ) := by
          have hp : 0 ≤ γin - psiIso β γin γout ϱ := by linarith
          nlinarith [sq_nonneg (γin - psiIso β γin γout ϱ)]
        calc
          _ ≤ (γout - psiIso β γin γout ϱ) *
              (γin - psiIso β γin γout ϱ) := hfac
          _ = ϱ * qIso β γin γout ϱ := heq.symm
          _ ≤ ϱ * isoK β γin := mul_le_mul_of_nonneg_left hqK hϱ.le
      · rw [min_eq_right hoi.le, max_eq_left hoi.le, le_div_iff₀ (sub_pos.mpr hoi)]
        simp only [min_eq_right hoi.le] at hψ hqK
        have hfac : (γout - psiIso β γin γout ϱ) * (γin - γout) ≤
            (γout - psiIso β γin γout ϱ) * (γin - psiIso β γin γout ϱ) := by
          have hp : 0 ≤ γout - psiIso β γin γout ϱ := by linarith
          nlinarith [sq_nonneg (γout - psiIso β γin γout ϱ)]
        calc
          _ ≤ (γout - psiIso β γin γout ϱ) *
              (γin - psiIso β γin γout ϱ) := hfac
          _ = ϱ * qIso β γin γout ϱ := heq.symm
          _ ≤ ϱ * isoK β γout := mul_le_mul_of_nonneg_left hqK hϱ.le
    · intro heq
      exact bridge_momentum_sqrt_bound hβ0 hβ1 hγin hγout hϱ
  · intro B Nin Nout hB hgin hgout
    have hBreal : 0 < (B : ℝ) := by exact_mod_cast hB
    have ht := hlim.const_mul (B : ℝ)
    convert ht using 1
    rw [hgin, hgout]
    rcases le_total Nin Nout with hNO | hON
    · have hNO' : (Nin : ℝ) ≤ (Nout : ℝ) := by exact_mod_cast hNO
      rw [min_eq_left hNO', min_eq_left (div_le_div_of_nonneg_right hNO' hBreal.le)]
      field_simp
    · have hON' : (Nout : ℝ) ≤ (Nin : ℝ) := by exact_mod_cast hON
      rw [min_eq_right hON', min_eq_right (div_le_div_of_nonneg_right hON' hBreal.le)]
      field_simp

private lemma bridge_unit_diagonal_bound {N : ℕ} (d : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : Muon.opNorm (Matrix.diagonal d) ≤ C := by
  open scoped Matrix.Norms.L2Operator in
  rw [Muon.opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by
    simpa [Real.norm_eq_abs] using hd i

private lemma bridge_unit_setup {N B : ℕ} (hB : 0 < B) {β γstar CSig : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar)
    (hC1 : 1 ≤ CSig) (i : Fin N) :
    ∃ (Fp : Muon.Setup.FrozenParams N N B) (S : Muon.Setup.SpectralData Fp.C),
      Fp.β = β ∧ S.μ = (fun _ => (1 : ℝ)) ∧ S.lam = (fun _ => (1 : ℝ)) ∧
      Muon.Volatility.SizeFin Fp.C B γstar CSig ∧ Fp.C.Sin = 1 ∧ Fp.C.Sout = 1 := by
  classical
  let C : Muon.Covariances N N :=
    { Sout := Matrix.diagonal (fun _ => 1)
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun _ => zero_le_one)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams N N B :=
    { C := C
      A := Pi.single i (Pi.single i 1)
      hA := by simp [Muon.fro, Pi.single_apply, ite_apply]
      β := β
      hβ := ⟨hβ0, hβ1⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := fun _ => 1
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by intro j; simp [Fp, C]
      eigIn := by intro j; simp [Fp, C] }
  refine ⟨Fp, S, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simpa [Muon.PowerLaw.gammaOf,
        div_le_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)] using hγ
    · exact bridge_unit_diagonal_bound (fun _ : Fin N => (1 : ℝ)) CSig
        (by linarith) (fun _ => by simpa using hC1)
    · exact bridge_unit_diagonal_bound (fun _ : Fin N => (1 : ℝ)) CSig
        (by linarith) (fun _ => by simpa using hC1)
  · simp [Fp, C]
  · simp [Fp, C]

private lemma bridge_lagResp_unit_sum (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (Fp : Muon.Setup.FrozenParams N N B) (S : Muon.Setup.SpectralData Fp.C)
    (hS : Muon.Volatility.SizeFin Fp.C B γstar CSig) (hC1 : 1 ≤ CSig)
    (ℓ : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun _ : Fin N => (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
      ∑ i : Fin N, Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
        (Pi.single i 1) (fun _ : Fin N => (1 : ℝ))
        (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
  obtain ⟨-, hlin, -⟩ := Muon.Volatility.thm_app_vol_lag_kernel_bilinear_bound_replication
    cert γstar CSig Fp S hS hC1 ℓ (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)
      (Muon.Volatility.lem_app_vol_sharp_ii hϱ hϱ).2.1
      (Muon.Volatility.lem_app_vol_sharp_ii hϱ hϱ).2.1
  set G : Fin N → ℝ := fun _ => (1 : ℝ) with hG
  have hzero : Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
      (fun _ => (0 : ℝ)) G (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) = 0 := by
    have h := hlin 1 (fun _ => 0) (fun _ => 0) G
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have hsum : ∀ s : Finset (Fin N),
      Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (fun j => ∑ i ∈ s, (Pi.single i 1 : Fin N → ℝ) j) G
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
        ∑ i ∈ s, Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (Pi.single i 1) G (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert k s hk ih =>
        have h := hlin 1 (Pi.single k 1)
          (fun j => ∑ i ∈ s, (Pi.single i 1 : Fin N → ℝ) j) G
        simp only [Finset.sum_insert hk]
        rw [← ih]
        simpa only [one_mul] using h
  have h := hsum Finset.univ
  have hfun : (fun j => ∑ i ∈ (Finset.univ : Finset (Fin N)),
      (Pi.single i 1 : Fin N → ℝ) j) = (fun _ => (1 : ℝ)) := by
    funext j
    simp [Pi.single_apply]
  simpa only [hfun, hG] using h

private lemma bridge_isoVol_eq_row (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig)
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    isoVol cert γstar CSig β N N B ϱ =
      (N : ℝ) * Muon.Volatility.rowVBar cert γstar CSig β B
        (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
  classical
  obtain ⟨Fp, S, hFp, hμ, hlam, hS, hId, hOut⟩ :=
    bridge_unit_setup hB hβ0 hβ1 hγ hC1 i
  have hroweq (j : Fin N) (ℓ : ℕ) :
      Muon.Volatility.lagRowBar cert γstar CSig β ℓ B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) j ϱ ϱ =
        Muon.Volatility.lagRowBar cert γstar CSig β ℓ B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
    have h := (Muon.Volatility.thm_app_vol_mode_kernels_iv_mu cert γstar CSig Fp S hS hC1
      hId ℓ ϱ ϱ hϱ hϱ j i (by rw [hμ])).1
    simpa only [hFp, hμ, hlam] using h
  have hcoef (ℓ : ℕ) :
      (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B
          (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
        (N : ℝ) * Muon.Volatility.lagRowBar cert γstar CSig β ℓ B
          (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
    have hlin := bridge_lagResp_unit_sum cert γstar CSig Fp S hS hC1 ℓ ϱ hϱ
    simp only [hFp, hμ, hlam] at hlin
    rw [hlin, Finset.mul_sum]
    simp_rw [show ∀ j : Fin N,
        (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B
          (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (Pi.single j 1) (fun _ : Fin N => (1 : ℝ))
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
            Muon.Volatility.lagRowBar cert γstar CSig β ℓ B
              (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) j ϱ ϱ from
      fun _ => rfl]
    simp_rw [hroweq]
    simp
  have hsum : Summable (fun ℓ : ℕ =>
      Muon.Volatility.lagRowBar cert γstar CSig β (ℓ + 1) B
        (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) := by
    have hs := (Muon.Volatility.thm_app_vol_mode_kernels_iii_series cert γstar CSig
      Fp S hS hC1 hId ϱ ϱ ⟨hϱ, le_rfl⟩).1 i ϱ ⟨le_rfl, le_rfl⟩ ϱ ⟨le_rfl, le_rfl⟩
    simp only [hFp, hμ, hlam] at hs
    refine Summable.of_norm ((hs.mul_left (1 / 2)).congr fun ℓ => ?_)
    rw [Real.norm_eq_abs, ← two_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  unfold isoVol Muon.Volatility.lagGammaBar Muon.Volatility.rowVBar
  rw [mul_add, ← tsum_mul_left, hcoef 0]
  have htail : ∑' ℓ : ℕ, (B : ℝ) *
        (Muon.Volatility.lagResp cert γstar CSig β (ℓ + 1) B
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
            (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) +
          Muon.Volatility.lagResp cert γstar CSig β (ℓ + 1) B
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
            (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)) =
      (N : ℝ) * ∑' ℓ : ℕ,
        (Muon.Volatility.lagRowBar cert γstar CSig β (ℓ + 1) B
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ +
          Muon.Volatility.lagRowBar cert γstar CSig β (ℓ + 1) B
            (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro ℓ
    rw [mul_add, hcoef (ℓ + 1)]
    ring
  rw [htail]
  ring

private lemma bridge_diag_diracs {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (d : Fin N → ℝ) (hd : A = Matrix.diagonal d) :
    ∑ i, Measure.dirac (hA.eigenvalues i) = ∑ i, Measure.dirac (d i) := by
  have hr := hA.roots_charpoly_eq_eigenvalues
  have hp : A.charpoly.roots = (Matrix.diagonal d).charpoly.roots :=
    congrArg (fun M => M.charpoly.roots) hd
  rw [hp, Matrix.charpoly_diagonal, Polynomial.roots_prod] at hr
  · have he : Multiset.map hA.eigenvalues Finset.univ.val =
        Multiset.map d Finset.univ.val := by
      simpa using hr.symm
    have h := congrArg (fun z : Multiset ℝ => (z.map Measure.dirac).sum) he
    simpa [Finset.sum_eq_multiset_sum, Function.comp_def] using h
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private lemma bridge_nuOut_unit {N B : ℕ} (C : Muon.Covariances N N) (hB : 0 < B)
    (hC : C.Sout = Matrix.diagonal (fun _ : Fin N => (1 : ℝ))) :
    Muon.nuOut C B = ENNReal.ofReal ((B : ℝ)⁻¹) •
      ∑ _ : Fin N, Measure.dirac (1 : ℝ) := by
  unfold Muon.nuOut
  rw [bridge_diag_diracs C.Sout C.psdOut.isHermitian (fun _ : Fin N => (1 : ℝ)) hC]
  congr 1
  simp [ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma bridge_nuIn_unit {N B : ℕ} (C : Muon.Covariances N N) (hB : 0 < B)
    (hC : C.Sin = 1) :
    Muon.nuIn C B = ENNReal.ofReal (Muon.PowerLaw.gammaOf N B) • Measure.dirac (1 : ℝ) := by
  unfold Muon.nuIn
  rw [bridge_diag_diracs C.Sin C.psdIn.isHermitian (fun _ : Fin N => (1 : ℝ))
    (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul]
  congr 1
  simp [Muon.PowerLaw.gammaOf, div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma bridge_row_zero_iso (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig) (i : Fin N)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Volatility.lagRowBar cert γstar CSig β 0 B (fun _ : Fin N => (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      psiIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) ϱ /
        Muon.PowerLaw.gammaOf N B := by
  classical
  have hγpos : 0 < Muon.PowerLaw.gammaOf N B :=
    div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  obtain ⟨Fp, S, hFp, hμ, hlam, hS, hId, hOut⟩ :=
    bridge_unit_setup hB hβ0 hβ1 hγ hC1 i
  let ν : FiniteMeasure ℝ := ⟨isoSpecMeasure (Muon.PowerLaw.gammaOf N B), by
    unfold isoSpecMeasure
    exact (Measure.dirac (1 : ℝ)).smul_finite ENNReal.ofReal_ne_top⟩
  have hν : (ν : Measure ℝ) = isoSpecMeasure (Muon.PowerLaw.gammaOf N B) := rfl
  have hνout : (ν : Measure ℝ) = Muon.nuOut Fp.C B := by
    rw [bridge_nuOut_unit Fp.C hB (by simpa using hOut)]
    ext A hA
    by_cases h : (1 : ℝ) ∈ A
    · simp [ν, isoSpecMeasure, Measure.smul_apply, hA, h,
        Muon.PowerLaw.gammaOf, div_eq_inv_mul,
        ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg B))]
    · simp [ν, isoSpecMeasure, Measure.smul_apply, hA, h]
  have hνin : (ν : Measure ℝ) = Muon.nuIn Fp.C B := by
    rw [bridge_nuIn_unit Fp.C hB hId]
    exact hν
  have hz := Muon.Volatility.thm_app_vol_mode_kernels_iv_zero_lag cert γstar CSig
    Fp S hS hC1 hId ν ν hνout hνin i ϱ hϱ
  simp only [hFp, hμ, hlam] at hz
  rw [hz]
  let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ
  have hx := bridge_branch hβ0 hβ1 hγpos hϱ hν
  obtain ⟨hsigma, -, ha, -, -, -, -, -⟩ :=
    prop_app_iso_closure_i hβ0 hβ1 hγpos hγpos hϱ hν hν hx
  have hq := lem_app_iso_comparison_iii hβ0 hβ1 hγpos hγpos hϱ hν hν hx
  have hden : 0 < ϱ +
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1 := by
    have ha0 : 0 ≤
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1 := hx.2.2.1
    linarith
  have hxeq :
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).1 *
        (ϱ + (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1) =
          Muon.PowerLaw.gammaOf N B :=
    (eq_div_iff hden.ne').mp hsigma
  have hpsi : psiIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) ϱ =
      isoPsi β ϱ x := by
    unfold psiIso isoPsi qIso
    rw [hq]
  unfold Muon.Volatility.volraw
  simp only [mul_one]
  change (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1 /
      (ϱ + (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1) = _
  rw [hpsi]
  have hane : ϱ +
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β)) ν ν ϱ).2.2.1 ≠ 0 := hden.ne'
  have hgne : Muon.PowerLaw.gammaOf N B ≠ 0 := hγpos.ne'
  rw [← ha]
  field_simp
  nlinarith [hxeq]

/-- `prop:app-iso-vol-momentum`(ii), snapshot `cr-2026-10-23`. Declaration of record for part (ii), square case
`Σ_in = Σ_out = Id_N`, `γ = N/B`, `β ∈ (0,1)`, row `i`. (a) `C̄_{1,0}(ϱ) = ψ(ϱ)/γ` for `ϱ > 0`; (b) for each
`ℓ` the row coefficient `C̄_{1,ℓ}(ϱ)` converges as `ϱ ↓ 0` to G's `cbarZero`, which is nonnegative with
`C̄_{1,0}(0) = 1`; (c) `𝔳_iso(ϱ) → N · 𝔳_1(0)` with `𝔳_1(0) = vZero ≥ 1` (G), so `𝔳_{iso,β} = N(1+2∑C̄_{1,ℓ}(0)) ≥ N`.
Existence of the limits is part of each conclusion. LaTeX, verbatim:

\begin{proposition}[Zero-ridge limits with momentum]\label{prop:app-iso-vol-momentum}
Let $\bmom\in(0,1)$ and $\gin,\gout>0$, put $\gamma_\wedge\defeq\min(\gin,\gout)$ and
$\gamma_\vee\defeq\max(\gin,\gout)$, and let $K_\bmom$ be the unique $q>0$ with
$q\Fw(q)=\gamma_\wedge$.
\begin{enumerate}[label=(\roman*)]
\item As $\ridge\downarrow0$, $\psi(\ridge)\to\gamma_\wedge$, and for every $\ridge>0$
\[
\gamma_\wedge-\psi(\ridge)\le\frac{\ridge\,K_\bmom}{\gamma_\vee-\gamma_\wedge}\quad(\gin\ne\gout),\qquad
\gamma_\wedge-\psi(\ridge)\le\sqrt{\ridge\,K_\bmom}\quad(\gin=\gout).
\]
In particular the same-time row and column coefficients $\psi(\ridge)/\gout$ and
$\psi(\ridge)/\gin$ of \cref{eqn:app-iso-vol-rows} tend to $\gamma_\wedge/\gout$ and
$\gamma_\wedge/\gin$, and the same-time total $B\psi(\ridge)$ of
\cref{eqn:app-iso-vol-total} tends to $\min\{\Nin,\Nout\}$.
\item Let $\Nin=\Nout=N$ and $\gamma=N/B$. For $\ell\ge0$ let $\overline C_{1,\ell}(\ridge)$ be the
row lag coefficient of \cref{eqn:app-pl-Cil} for the spectrum $\mu_1=\dots=\mu_N=1$,
which is the same for every row. Then $\overline C_{1,0}(\ridge)=\psi(\ridge)/\gamma$; for
every $\ell\ge0$ the limit $\overline C_{1,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{1,\ell}(\ridge)$
exists and is nonnegative, with $\overline C_{1,0}(0)=1$; and the limit of
\cref{def:app-iso-vol-zero} exists and equals
\[
\mathfrak v_{\mathrm{iso},\bmom}=N\Big(1+2\sum_{\ell\ge1}\overline C_{1,\ell}(0)\Big)\ge N .
\]
\item If moreover $N>B$, then $\mathfrak v_{\mathrm{iso},\bmom}\ge N>B=\mathfrak v_{\mathrm{iso},0}$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_iso_vol_momentum_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig) (i : Fin N) :
    (∀ ϱ : ℝ, 0 < ϱ →
      Muon.Volatility.lagRowBar cert γstar CSig β 0 B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
        psiIso β (Muon.PowerLaw.gammaOf N B) (Muon.PowerLaw.gammaOf N B) ϱ / Muon.PowerLaw.gammaOf N B) ∧
    (∀ ℓ : ℕ,
      Tendsto (fun ϱ : ℝ => Muon.Volatility.lagRowBar cert γstar CSig β ℓ B (fun _ : Fin N => (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) (𝓝[>] (0 : ℝ))
        (𝓝 (Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ℓ)) ∧
      0 ≤ Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ℓ) ∧
    Summable (fun ℓ : ℕ => Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i (ℓ + 1)) ∧
    Muon.PowerLaw.cbarZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i 0 = 1 ∧
    hasIsoZeroRidgeVol cert γstar CSig β N N B
        ((N : ℝ) * Muon.PowerLaw.vZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i) ∧
    1 ≤ Muon.PowerLaw.vZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ∧
    (N : ℝ) ≤ (N : ℝ) * Muon.PowerLaw.vZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i ∧
    def_app_iso_vol_zero cert γstar CSig β N N B =
      (N : ℝ) * Muon.PowerLaw.vZero cert γstar CSig β B (fun _ : Fin N => (1 : ℝ)) i := by
  let μ : Fin N → ℝ := fun _ => 1
  have hm : Muon.PowerLaw.partMN B μ 1 ∈
      Ioo 0 (Muon.PowerLaw.gammaOf N B) :=
    (Muon.PowerLaw.def_app_pl_participation_bij μ hB hN
      (fun _ => zero_lt_one)).1.1 (Set.mem_Ioi.mpr (by norm_num))
  have hz0 : 0 < Muon.PowerLaw.plZ1 β B μ := by
    exact (Muon.PowerLaw.prop_app_pl_branch_i μ hβ0 hβ1 hB hN
      (fun _ _ _ => le_rfl) (fun _ => zero_lt_one)).2.2.1.1 hm
  have hi := Muon.PowerLaw.prop_app_pl_vol_zero_i cert γstar CSig hB hN μ
    (fun _ _ _ => le_rfl) (fun _ => zero_lt_one) hβ0 hβ1 hγ (fun _ => hC1) hC1 i
    hz0 (le_refl _)
  have hii := Muon.PowerLaw.prop_app_pl_vol_zero_ii cert γstar CSig hB hN μ
    (fun _ _ _ => le_rfl) (fun _ => zero_lt_one) hβ0 hβ1 hγ (fun _ => hC1) hC1 i
    hz0 (le_refl _)
  have hiii := Muon.PowerLaw.prop_app_pl_vol_zero_iii_c cert γstar CSig hB hN μ
    (fun _ _ _ => le_rfl) (fun _ => zero_lt_one) hβ0 hβ1 hγ (fun _ => hC1) hC1 i
  have hiso : hasIsoZeroRidgeVol cert γstar CSig β N N B
      ((N : ℝ) * Muon.PowerLaw.vZero cert γstar CSig β B μ i) := by
    have hlim := hii.2.2.2.1.const_mul (N : ℝ)
    have heq : ∀ᶠ ϱ in 𝓝[>] (0 : ℝ),
        isoVol cert γstar CSig β N N B ϱ =
          (N : ℝ) * Muon.Volatility.rowVBar cert γstar CSig β B μ
            (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
      filter_upwards [Ioc_mem_nhdsGT hz0] with ϱ hϱ
      exact bridge_isoVol_eq_row cert γstar CSig hB hβ0.le hβ1 hγ hC1 i hϱ.1
    exact hlim.congr' (heq.mono fun _ h => h.symm)
  have hs : Summable (fun ℓ : ℕ =>
      Muon.PowerLaw.cbarZero cert γstar CSig β B μ i (ℓ + 1)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using hii.2.2.1)
  have hv := hiii.2.2
  have hNv : (N : ℝ) ≤ (N : ℝ) *
      Muon.PowerLaw.vZero cert γstar CSig β B μ i := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ N by positivity) (sub_nonneg.mpr hv)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ϱ hϱ
    simpa only [μ] using bridge_row_zero_iso cert γstar CSig hB hN hβ0.le hβ1 hγ hC1 i hϱ
  · intro ℓ
    exact ⟨by simpa only [μ] using hi.2.1 ℓ, by simpa only [μ] using hiii.1 ℓ⟩
  · simpa only [μ] using hs
  · simpa only [μ] using hi.2.2.1
  · simpa only [μ] using hiso
  · simpa only [μ] using hv
  · simpa only [μ] using hNv
  · unfold def_app_iso_vol_zero
    simpa only [μ] using hiso.limUnder_eq

private lemma bridge_beta0_psi_limit {γ : ℝ} (hγ : 1 < γ) :
    Tendsto (fun ϱ : ℝ => psiIso 0 γ γ ϱ) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hγpos : 0 < γ := zero_lt_one.trans hγ
  have hqtop : Tendsto (fun ϱ : ℝ => qIso 0 γ γ ϱ) (𝓝[>] (0 : ℝ)) atTop := by
    refine tendsto_atTop_mono' _ ?_
      (tendsto_inv_nhdsGT_zero.const_mul_atTop (sq_pos_of_pos (sub_pos.mpr hγ)))
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    obtain ⟨hq, -, heq⟩ := bridge_momentum_root (le_refl 0) zero_lt_one hγpos hγpos hϱ
    have hpsi : psiIso 0 γ γ ϱ < 1 := by
      have hm := (((lem_app_iso_weights_i (le_refl 0) zero_lt_one).2.2.2 rfl).2.2.mapsTo
        (Set.mem_Ici.mpr hq)).2
      simpa only [psiIso] using hm
    have hsq : (γ - 1) ^ 2 ≤ (γ - psiIso 0 γ γ ϱ) ^ 2 := by
      nlinarith
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ hϱ).2
    calc
      (γ - 1) ^ 2 ≤ (γ - psiIso 0 γ γ ϱ) ^ 2 := hsq
      _ = qIso 0 γ γ ϱ * ϱ := by rw [pow_two, ← heq, mul_comm]
  have hcomp := lem_app_iso_gaussian_iv.2.comp hqtop
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
  obtain ⟨hq, -, -⟩ := bridge_momentum_root (le_refl 0) zero_lt_one hγpos hγpos hϱ
  have heq := ((lem_app_iso_weights_i (le_refl 0) zero_lt_one).2.2.2 rfl).1
    (qIso 0 γ γ ϱ) hq
  simpa only [Function.comp_apply, psiIso] using heq.symm

private lemma bridge_rowVBar_beta0 (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar)
    (hC1 : 1 ≤ CSig) (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Volatility.rowVBar cert γstar CSig 0 B (fun _ : Fin N => (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      Muon.Volatility.lagRowBar cert γstar CSig 0 0 B (fun _ : Fin N => (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
  obtain ⟨Fp, S, hFp, hμ, hlam, hS, hId, -⟩ :=
    bridge_unit_setup hB (le_refl 0) zero_lt_one hγ hC1 i
  have hz (ℓ : ℕ) : Muon.Volatility.lagRowBar cert γstar CSig 0 (ℓ + 1) B
      (fun _ : Fin N => (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ = 0 := by
    have h := Muon.Volatility.thm_app_vol_mode_kernels_iv_beta0 cert γstar CSig
      Fp S hS hC1 hId hFp i (ℓ + 1) (by omega) ϱ ϱ hϱ hϱ
    simpa only [hFp, hμ, hlam] using h
  unfold Muon.Volatility.rowVBar
  simp_rw [hz]
  simp

private lemma bridge_beta0_iso_limit (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (hBN : B < N)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig) :
    hasIsoZeroRidgeVol cert γstar CSig 0 N N B (B : ℝ) := by
  let i : Fin N := ⟨0, hN⟩
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hBNreal : (B : ℝ) < N := by exact_mod_cast hBN
  have hγone : 1 < Muon.PowerLaw.gammaOf N B := by
    rw [Muon.PowerLaw.gammaOf]
    exact (one_lt_div hBreal).2 (by simpa using hBNreal)
  have hlim := (bridge_beta0_psi_limit hγone).const_mul (B : ℝ)
  have heq : ∀ᶠ ϱ in 𝓝[>] (0 : ℝ),
      isoVol cert γstar CSig 0 N N B ϱ =
        (B : ℝ) * psiIso 0 (Muon.PowerLaw.gammaOf N B)
          (Muon.PowerLaw.gammaOf N B) ϱ := by
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    rw [bridge_isoVol_eq_row cert γstar CSig hB (le_refl 0) zero_lt_one hγ hC1 i hϱ]
    rw [bridge_rowVBar_beta0 cert γstar CSig hB hγ hC1 i hϱ]
    rw [bridge_row_zero_iso cert γstar CSig hB hN (le_refl 0) zero_lt_one hγ hC1 i hϱ]
    rw [Muon.PowerLaw.gammaOf]
    field_simp
  have hlim' : Tendsto
      (fun ϱ : ℝ => (B : ℝ) * psiIso 0 (Muon.PowerLaw.gammaOf N B)
        (Muon.PowerLaw.gammaOf N B) ϱ) (𝓝[>] (0 : ℝ)) (𝓝 (B : ℝ)) := by
    simpa using hlim
  exact hlim'.congr' (heq.mono fun _ h => h.symm)

/-- `prop:app-iso-vol-momentum`(iii), snapshot `cr-2026-10-23`. Declaration of record for part (iii): if `N > B`
then `𝔳_{iso,β} ≥ N > B = 𝔳_{iso,0}`, where the zero-momentum limit is `min{B,N,N} = B` from
`prop_app_iso_volatility_zero` (its hypotheses are those of the square regime `hγ`, `hC1`). LaTeX, verbatim:

\begin{proposition}[Zero-ridge limits with momentum]\label{prop:app-iso-vol-momentum}
Let $\bmom\in(0,1)$ and $\gin,\gout>0$, put $\gamma_\wedge\defeq\min(\gin,\gout)$ and
$\gamma_\vee\defeq\max(\gin,\gout)$, and let $K_\bmom$ be the unique $q>0$ with
$q\Fw(q)=\gamma_\wedge$.
\begin{enumerate}[label=(\roman*)]
\item As $\ridge\downarrow0$, $\psi(\ridge)\to\gamma_\wedge$, and for every $\ridge>0$
\[
\gamma_\wedge-\psi(\ridge)\le\frac{\ridge\,K_\bmom}{\gamma_\vee-\gamma_\wedge}\quad(\gin\ne\gout),\qquad
\gamma_\wedge-\psi(\ridge)\le\sqrt{\ridge\,K_\bmom}\quad(\gin=\gout).
\]
In particular the same-time row and column coefficients $\psi(\ridge)/\gout$ and
$\psi(\ridge)/\gin$ of \cref{eqn:app-iso-vol-rows} tend to $\gamma_\wedge/\gout$ and
$\gamma_\wedge/\gin$, and the same-time total $B\psi(\ridge)$ of
\cref{eqn:app-iso-vol-total} tends to $\min\{\Nin,\Nout\}$.
\item Let $\Nin=\Nout=N$ and $\gamma=N/B$. For $\ell\ge0$ let $\overline C_{1,\ell}(\ridge)$ be the
row lag coefficient of \cref{eqn:app-pl-Cil} for the spectrum $\mu_1=\dots=\mu_N=1$,
which is the same for every row. Then $\overline C_{1,0}(\ridge)=\psi(\ridge)/\gamma$; for
every $\ell\ge0$ the limit $\overline C_{1,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{1,\ell}(\ridge)$
exists and is nonnegative, with $\overline C_{1,0}(0)=1$; and the limit of
\cref{def:app-iso-vol-zero} exists and equals
\[
\mathfrak v_{\mathrm{iso},\bmom}=N\Big(1+2\sum_{\ell\ge1}\overline C_{1,\ell}(0)\Big)\ge N .
\]
\item If moreover $N>B$, then $\mathfrak v_{\mathrm{iso},\bmom}\ge N>B=\mathfrak v_{\mathrm{iso},0}$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_iso_vol_momentum_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (hBN : B < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : Muon.PowerLaw.gammaOf N B ≤ γstar) (hC1 : 1 ≤ CSig) :
    (∃ v : ℝ, hasIsoZeroRidgeVol cert γstar CSig β N N B v ∧ (N : ℝ) ≤ v) ∧
    hasIsoZeroRidgeVol cert γstar CSig 0 N N B (B : ℝ) ∧
    (B : ℝ) < (N : ℝ) := by
  let i : Fin N := ⟨0, hN⟩
  obtain ⟨-, -, -, -, hiso, -, hNv, -⟩ :=
    prop_app_iso_vol_momentum_ii cert γstar CSig hB hN hβ0 hβ1 hγ hC1 i
  refine ⟨⟨(N : ℝ) * Muon.PowerLaw.vZero cert γstar CSig β B
    (fun _ : Fin N => (1 : ℝ)) i, hiso, hNv⟩, ?_, ?_⟩
  · exact bridge_beta0_iso_limit cert γstar CSig hB hN hBN hγ hC1
  · exact_mod_cast hBN

/-! ## The zero-ridge isotropic volatility without momentum (`prop:app-iso-volatility-zero`) -/

/-! ### Rectangular zero-momentum helpers for `prop_app_iso_volatility_zero` -/

private lemma bridgeR_branch {γin γout s : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) (hs : 0 < s)
    {ν ν' : FiniteMeasure ℝ} (hν : (ν : Measure ℝ) = isoSpecMeasure γout)
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure γin) :
    Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' s
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' s) := by
  have hw : Muon.DetEquiv.WeightSeq (Muon.emaW 0) := by
    refine ⟨fun j => mul_nonneg (sub_nonneg.mpr zero_lt_one.le) (pow_nonneg le_rfl j), ?_, ?_⟩
    · exact (summable_geometric_of_lt_one le_rfl zero_lt_one).mul_left (1 - 0)
    · exact ⟨0, by simp [Muon.emaW]⟩
  apply Muon.DetEquiv.branchSol_spec (Muon.DetEquiv.Fw_admissible hw) zero_lt_one
    (lt_max_of_lt_left hγin : 0 < max γin γout)
  · have h1 : (0 : ℝ) ≤ 1 := zero_le_one
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [hν, isoSpecMeasure, ENNReal.ofReal_le_ofReal (le_max_right γin γout)]
    · simp [hν, isoSpecMeasure]
    · simp [hν', isoSpecMeasure, ENNReal.ofReal_le_ofReal (le_max_left γin γout)]
    · simp [hν', isoSpecMeasure]
  · exact hs

private lemma bridgeR_nuOut {m n B : ℕ} (C : Muon.Covariances m n) (hB : 0 < B)
    (hC : C.Sout = 1) :
    Muon.nuOut C B = isoSpecMeasure ((m : ℝ) / (B : ℝ)) := by
  unfold Muon.nuOut
  rw [bridge_diag_diracs C.Sout C.psdOut.isHermitian (fun _ : Fin m => (1 : ℝ))
    (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, isoSpecMeasure]
  congr 1
  simp [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg B)),
    ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma bridgeR_nuIn {m n B : ℕ} (C : Muon.Covariances m n) (hB : 0 < B)
    (hC : C.Sin = 1) :
    Muon.nuIn C B = isoSpecMeasure ((n : ℝ) / (B : ℝ)) := by
  unfold Muon.nuIn
  rw [bridge_diag_diracs C.Sin C.psdIn.isHermitian (fun _ : Fin n => (1 : ℝ))
    (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul, isoSpecMeasure]
  congr 1
  simp [div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.mpr (Nat.cast_nonneg B)),
    ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma bridgeR_setup {m n B : ℕ} (hB : 0 < B) (hm : 0 < m) (hn : 0 < n)
    {γstar CSig : ℝ} (hγ : ((max m n : ℕ) : ℝ) ≤ γstar * (B : ℝ)) (hC1 : 1 ≤ CSig) :
    ∃ (Fp : Muon.Setup.FrozenParams m n B) (S : Muon.Setup.SpectralData Fp.C),
      Fp.β = 0 ∧ S.μ = (fun _ => (1 : ℝ)) ∧ S.lam = (fun _ => (1 : ℝ)) ∧
      Muon.Volatility.SizeFin Fp.C B γstar CSig ∧ Fp.C.Sin = 1 ∧ Fp.C.Sout = 1 := by
  classical
  let C : Muon.Covariances m n :=
    { Sout := Matrix.diagonal (fun _ => 1)
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun _ => zero_le_one)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams m n B :=
    { C := C
      A := Pi.single ⟨0, hm⟩ (Pi.single ⟨0, hn⟩ 1)
      hA := by simp [Muon.fro, Pi.single_apply, ite_apply]
      β := 0
      hβ := ⟨le_rfl, zero_lt_one⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := fun _ => 1
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by intro j; simp [Fp, C]
      eigIn := by intro j; simp [Fp, C] }
  refine ⟨Fp, S, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · refine ⟨hγ, ?_, ?_⟩
    · exact bridge_unit_diagonal_bound (fun _ : Fin m => (1 : ℝ)) CSig
        (by linarith) (fun _ => by simpa using hC1)
    · exact bridge_unit_diagonal_bound (fun _ : Fin n => (1 : ℝ)) CSig
        (by linarith) (fun _ => by simpa using hC1)
  · simp [Fp, C]
  · simp [Fp, C]

private lemma bridgeR_lagResp_sum (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (Fp : Muon.Setup.FrozenParams m n B) (S : Muon.Setup.SpectralData Fp.C)
    (hS : Muon.Volatility.SizeFin Fp.C B γstar CSig) (hC1 : 1 ≤ CSig)
    (ℓ : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam (fun _ : Fin m => (1 : ℝ))
        (fun _ : Fin n => (1 : ℝ)) (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
      ∑ i : Fin m, Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
        (Pi.single i 1) (fun _ : Fin n => (1 : ℝ))
        (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
  obtain ⟨-, hlin, -⟩ := Muon.Volatility.thm_app_vol_lag_kernel_bilinear_bound_replication
    cert γstar CSig Fp S hS hC1 ℓ (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)
      (Muon.Volatility.lem_app_vol_sharp_ii hϱ hϱ).2.1
      (Muon.Volatility.lem_app_vol_sharp_ii hϱ hϱ).2.1
  set G : Fin n → ℝ := fun _ => (1 : ℝ) with hG
  have hzero : Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
      (fun _ => (0 : ℝ)) G (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) = 0 := by
    have h := hlin 1 (fun _ => 0) (fun _ => 0) G
    simp only [mul_zero, zero_add, one_mul] at h
    linarith
  have hsum : ∀ s : Finset (Fin m),
      Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (fun j => ∑ i ∈ s, (Pi.single i 1 : Fin m → ℝ) j) G
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
        ∑ i ∈ s, Muon.Volatility.lagResp cert γstar CSig Fp.β ℓ B S.μ S.lam
          (Pi.single i 1) G (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hzero
    | insert k s hk ih =>
        have h := hlin 1 (Pi.single k 1)
          (fun j => ∑ i ∈ s, (Pi.single i 1 : Fin m → ℝ) j) G
        simp only [Finset.sum_insert hk]
        rw [← ih]
        simpa only [one_mul] using h
  have h := hsum Finset.univ
  have hfun : (fun j => ∑ i ∈ (Finset.univ : Finset (Fin m)),
      (Pi.single i 1 : Fin m → ℝ) j) = (fun _ => (1 : ℝ)) := by
    funext j
    simp [Pi.single_apply]
  simpa only [hfun, hG] using h

private lemma bridgeR_isoVol_zero (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (hB : 0 < B) (hm : 0 < m) (hn : 0 < n)
    (hγ : ((max m n : ℕ) : ℝ) ≤ γstar * (B : ℝ)) (hC1 : 1 ≤ CSig)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    isoVol cert γstar CSig 0 m n B ϱ =
      (B : ℝ) * psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ := by
  classical
  obtain ⟨Fp, S, hFp, hμ, hlam, hS, hId, hOut⟩ := bridgeR_setup hB hm hn hγ hC1
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hγout : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) hBreal
  have hγin : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) hBreal
  let i0 : Fin m := ⟨0, hm⟩
  -- zero-lag row value
  have hrow0 : Muon.Volatility.lagRowBar cert γstar CSig 0 0 B (fun _ : Fin m => (1 : ℝ))
      (fun _ : Fin n => (1 : ℝ)) i0 ϱ ϱ =
        psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ / ((m : ℝ) / (B : ℝ)) := by
    let ν : FiniteMeasure ℝ := ⟨isoSpecMeasure ((m : ℝ) / (B : ℝ)), by
      unfold isoSpecMeasure
      exact (Measure.dirac (1 : ℝ)).smul_finite ENNReal.ofReal_ne_top⟩
    let ν' : FiniteMeasure ℝ := ⟨isoSpecMeasure ((n : ℝ) / (B : ℝ)), by
      unfold isoSpecMeasure
      exact (Measure.dirac (1 : ℝ)).smul_finite ENNReal.ofReal_ne_top⟩
    have hν : (ν : Measure ℝ) = isoSpecMeasure ((m : ℝ) / (B : ℝ)) := rfl
    have hν' : (ν' : Measure ℝ) = isoSpecMeasure ((n : ℝ) / (B : ℝ)) := rfl
    have hz := Muon.Volatility.thm_app_vol_mode_kernels_iv_zero_lag cert γstar CSig
      Fp S hS hC1 hId ν ν' (hν.trans (bridgeR_nuOut Fp.C hB hOut).symm)
      (hν'.trans (bridgeR_nuIn Fp.C hB hId).symm) i0 ϱ hϱ
    simp only [hFp, hμ, hlam] at hz
    rw [hz]
    have hx := bridgeR_branch hγin hγout hϱ hν hν'
    obtain ⟨hs1, -, ha, -, hpsi1, -, -, -⟩ :=
      prop_app_iso_closure_i (le_refl 0) zero_lt_one hγin hγout hϱ hν hν' hx
    have hq := lem_app_iso_comparison_iii (le_refl 0) zero_lt_one hγin hγout hϱ hν hν' hx
    have hpsi : psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ =
        isoPsi 0 ϱ (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' ϱ) := by
      unfold psiIso isoPsi qIso
      rw [hq]
    have hA0 : 0 ≤ (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' ϱ).2.2.1 :=
      hx.2.2.1
    have hden : 0 < ϱ +
        (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' ϱ).2.2.1 := by linarith
    unfold Muon.Volatility.volraw
    simp only [mul_one]
    rw [hpsi, ← ha]
    rw [hs1]
    field_simp
  have hroweq (j : Fin m) (ℓ : ℕ) :
      Muon.Volatility.lagRowBar cert γstar CSig 0 ℓ B (fun _ : Fin m => (1 : ℝ))
          (fun _ : Fin n => (1 : ℝ)) j ϱ ϱ =
        Muon.Volatility.lagRowBar cert γstar CSig 0 ℓ B (fun _ : Fin m => (1 : ℝ))
          (fun _ : Fin n => (1 : ℝ)) i0 ϱ ϱ := by
    have h := (Muon.Volatility.thm_app_vol_mode_kernels_iv_mu cert γstar CSig Fp S hS hC1
      hId ℓ ϱ ϱ hϱ hϱ j i0 (by rw [hμ])).1
    simpa only [hFp, hμ, hlam] using h
  have hcoef (ℓ : ℕ) :
      (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig 0 ℓ B
          (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
          (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
        (m : ℝ) * Muon.Volatility.lagRowBar cert γstar CSig 0 ℓ B
          (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) i0 ϱ ϱ := by
    have hlin := bridgeR_lagResp_sum cert γstar CSig Fp S hS hC1 ℓ ϱ hϱ
    simp only [hFp, hμ, hlam] at hlin
    rw [hlin, Finset.mul_sum]
    simp_rw [show ∀ j : Fin m,
        (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig 0 ℓ B
          (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
          (Pi.single j 1) (fun _ : Fin n => (1 : ℝ))
          (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
            Muon.Volatility.lagRowBar cert γstar CSig 0 ℓ B
              (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ)) j ϱ ϱ from
      fun _ => rfl]
    simp_rw [hroweq]
    simp
  have hz1 (ℓ : ℕ) : Muon.Volatility.lagResp cert γstar CSig 0 (ℓ + 1) B
      (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
      (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) = 0 := by
    have h := Muon.Volatility.thm_app_vol_mode_kernels_iv_beta0 cert γstar CSig
      Fp S hS hC1 hId hFp i0 (ℓ + 1) (by omega) ϱ ϱ hϱ hϱ
    simp only [hFp, hμ, hlam] at h
    have h2 := hcoef (ℓ + 1)
    rw [h, mul_zero] at h2
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact absurd h3 hBreal.ne'
    · exact h3
  unfold isoVol Muon.Volatility.lagGammaBar
  simp_rw [hz1]
  simp only [add_zero, tsum_zero]
  have h0 := hcoef 0
  rw [hrow0] at h0
  rw [h0]
  have hmne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

private lemma bridgeR_psi_limit {γin γout : ℝ} (hγin : 0 < γin) (hγout : 0 < γout) :
    Tendsto (fun ϱ : ℝ => psiIso 0 γin γout ϱ) (𝓝[>] (0 : ℝ))
      (𝓝 (min 1 (min γin γout))) := by
  have hmpos : 0 < min 1 (min γin γout) := lt_min zero_lt_one (lt_min hγin hγout)
  have hpsi_eq : ∀ ϱ : ℝ, 0 < ϱ → 0 ≤ qIso 0 γin γout ϱ ∧
      psiIso 0 γin γout ϱ < min γin γout ∧ psiIso 0 γin γout ϱ < 1 ∧
      ϱ * qIso 0 γin γout ϱ =
        (γout - psiIso 0 γin γout ϱ) * (γin - psiIso 0 γin γout ϱ) ∧
      psiIso 0 γin γout ϱ = isoPhi (qIso 0 γin γout ϱ) := by
    intro ϱ hϱ
    obtain ⟨hq, hlt, heq⟩ := bridge_momentum_root (le_refl 0) zero_lt_one hγin hγout hϱ
    have hW := (lem_app_iso_weights_i (le_refl 0) zero_lt_one).2.2.2 rfl
    have hm1 : psiIso 0 γin γout ϱ < 1 := by
      have hm := (hW.2.2.mapsTo (Set.mem_Ici.mpr hq)).2
      simpa only [psiIso] using hm
    refine ⟨hq, hlt, hm1, heq, ?_⟩
    have h := hW.1 (qIso 0 γin γout ϱ) hq
    simpa only [psiIso] using h
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · -- lower bound
    have hδ : 0 < min 1 (min γin γout) - a := sub_pos.mpr ha
    have ha1 : a < 1 := lt_of_lt_of_le ha (min_le_left _ _)
    have hev := ((tendsto_order.1 lem_app_iso_gaussian_iv.2).1 a ha1).and
      (Filter.eventually_gt_atTop (0 : ℝ))
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 hev
    have hTpos : 0 < T := (hT T le_rfl).2
    have hmem : Set.Ioo (0 : ℝ) ((min 1 (min γin γout) - a) ^ 2 / T) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (div_pos (pow_pos hδ 2) hTpos)
    filter_upwards [hmem] with ϱ hϱ
    obtain ⟨hϱ0, hϱ1⟩ := hϱ
    obtain ⟨hq, hlt, hm1, heq, hphi⟩ := hpsi_eq ϱ hϱ0
    by_contra hcon
    push_neg at hcon
    set δ := min 1 (min γin γout) - a with hδdef
    have h1 : δ ≤ γout - psiIso 0 γin γout ϱ := by
      have : min 1 (min γin γout) ≤ γout := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    have h2 : δ ≤ γin - psiIso 0 γin γout ϱ := by
      have : min 1 (min γin γout) ≤ γin := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hprod : δ ^ 2 ≤ ϱ * qIso 0 γin γout ϱ := by
      rw [heq, pow_two]
      exact mul_le_mul h1 h2 hδ.le (hδ.le.trans h1)
    have hqT : T < qIso 0 γin γout ϱ := by
      by_contra hn
      push_neg at hn
      have : ϱ * qIso 0 γin γout ϱ ≤ ϱ * T := mul_le_mul_of_nonneg_left hn hϱ0.le
      have h3 : ϱ * T < δ ^ 2 := by
        have := (lt_div_iff₀ hTpos).1 hϱ1
        linarith
      linarith
    have := (hT _ hqT.le).1
    rw [hphi] at hcon
    linarith
  · -- upper bound
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    obtain ⟨hq, hlt, hm1, heq, hphi⟩ := hpsi_eq ϱ hϱ
    exact (lt_min hm1 hlt).trans ha

/-- `prop:app-iso-volatility-zero`, snapshot `cr-2026-10-23` (also `rem:app-iso-volatility-zero`). Declaration of
record. Fixed dimensions `m, n, B` at `β = 0`, under the standing regime `max(m,n) ≤ γ⋆B`, `1 ≤ C_Σ`: `ψ(ϱ) → m_γ`
with `m_γ = min{1, γin, γout}`, and `𝔳_iso(ϱ) → B m_γ = min{B, N_in, N_out}`. LaTeX, verbatim:

\begin{proposition}[Zero-ridge isotropic volatility without momentum]\label{prop:app-iso-volatility-zero}\label{rem:app-iso-volatility-zero}
Let $\bmom=0$ and $m_\gamma\defeq\min\{1,\gin,\gout\}$. Then
$\psi(\ridge)\to m_\gamma$ as $\ridge\downarrow0$, and
\[
\lim_{\ridge\downarrow0}\mathfrak v_{\mathrm{iso}}(\ridge)=B\,m_\gamma=\min\{B,\Nin,\Nout\}.
\]
\end{proposition}
-/
theorem prop_app_iso_volatility_zero (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (hB : 0 < B) (hm : 0 < m) (hn : 0 < n)
    (hγ : ((max m n : ℕ) : ℝ) ≤ γstar * (B : ℝ)) (hC1 : 1 ≤ CSig) :
    Tendsto (fun ϱ : ℝ => psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ) (𝓝[>] (0 : ℝ))
      (𝓝 (min 1 (min ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ))))) ∧
    hasIsoZeroRidgeVol cert γstar CSig 0 m n B ((B : ℝ) * min 1 (min ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)))) ∧
    (B : ℝ) * min 1 (min ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ))) = min (B : ℝ) (min (n : ℝ) (m : ℝ)) := by
  have hBreal : (0 : ℝ) < B := by exact_mod_cast hB
  have hγout : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) hBreal
  have hγin : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) hBreal
  have hpsi := bridgeR_psi_limit hγin hγout
  refine ⟨hpsi, ?_, ?_⟩
  · unfold hasIsoZeroRidgeVol
    refine (hpsi.const_mul (B : ℝ)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    exact (bridgeR_isoVol_zero cert γstar CSig hB hm hn hγ hC1 hϱ).symm
  · rw [mul_min_of_nonneg _ _ hBreal.le, mul_min_of_nonneg _ _ hBreal.le]
    rw [mul_one, mul_div_cancel₀ _ hBreal.ne', mul_div_cancel₀ _ hBreal.ne']

/-! ## The drift (`thm:app-iso-drift`) -/

private lemma bridge_drift_dims_pos {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) :
    0 < m ∧ 0 < n := by
  constructor
  · by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hA := F.hA
    simp [Muon.fro] at hA
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hA := F.hA
    simp [Muon.fro] at hA

private lemma bridge_drift_eigenvalues {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) :
    (∀ i, S.μ i = 1) ∧ ∀ j, S.lam j = 1 := by
  constructor
  · intro i
    have h := Muon.Setup.eig_u S i
    rw [hIso.2, Matrix.one_mulVec] at h
    have hn := Muon.Setup.sum_col_sq_eq_one S.uOut S.huOut i
    have huu : S.u i ⬝ᵥ S.u i = 1 := by
      simpa [dotProduct, Muon.Setup.SpectralData.u, sq] using hn
    have h2 := congrArg (fun w => S.u i ⬝ᵥ w) h
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [huu] at h2
    linarith
  · intro j
    have h := Muon.Setup.eig_v S j
    rw [hIso.1, Matrix.one_mulVec] at h
    have hn := Muon.Setup.sum_col_sq_eq_one S.vIn S.hvIn j
    have hvv : S.v j ⬝ᵥ S.v j = 1 := by
      simpa [dotProduct, Muon.Setup.SpectralData.v, sq] using hn
    have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [hvv] at h2
    linarith

private lemma bridge_drift_hermitian_eig_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
    (hA : A.IsHermitian) (h1 : A = 1) (i : Fin k) : hA.eigenvalues i = 1 := by
  subst h1
  have hv := hA.mulVec_eigenvectorBasis i
  rw [Matrix.one_mulVec] at hv
  have hn := hA.eigenvectorBasis.orthonormal.1 i
  by_contra hne
  have h0 : (1 - hA.eigenvalues i) • (⇑(hA.eigenvectorBasis i)) = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero.2 hv
  rcases smul_eq_zero.1 h0 with h | h
  · exact hne (by linarith)
  · have h2 : hA.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h j
    rw [h2, norm_zero] at hn
    norm_num at hn

private lemma bridge_drift_spec_measures {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) :
    ((Muon.Drift.specOutFM F : FiniteMeasure ℝ) : Measure ℝ) =
        isoSpecMeasure ((m : ℝ) / (B : ℝ)) ∧
      ((Muon.Drift.specInFM F : FiniteMeasure ℝ) : Measure ℝ) =
        isoSpecMeasure ((n : ℝ) / (B : ℝ)) := by
  have hout : ∀ i, F.C.psdOut.isHermitian.eigenvalues i = 1 :=
    bridge_drift_hermitian_eig_one F.C.Sout F.C.psdOut.isHermitian hIso.2
  have hin : ∀ i, F.C.psdIn.isHermitian.eigenvalues i = 1 :=
    bridge_drift_hermitian_eig_one F.C.Sin F.C.psdIn.isHermitian hIso.1
  constructor <;> ext A hA <;>
    simp [Muon.Drift.specOutFM, Muon.Drift.specInFM, Muon.Oversampled.nuOutFM,
      Muon.nuOut, Muon.nuIn, isoSpecMeasure, hout, hin, Measure.smul_apply, hA,
      ENNReal.ofReal_div_of_pos (by exact_mod_cast F.hB : (0 : ℝ) < (B : ℝ))] <;>
    simp only [div_eq_mul_inv] <;> ac_rfl

private lemma bridge_drift_branch {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {β s : ℝ} (hβ : 0 ≤ β ∧ β < 1) (hs : 0 < s) :
    Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β))
        (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s) := by
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  obtain ⟨hout, hin⟩ := bridge_drift_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
  apply Muon.DetEquiv.branchSol_spec
    (Muon.DetEquiv.Fw_admissible (Muon.Drift.emaW_weightClass β hβ).1) (Cs := 1)
    (γ := max ((m : ℝ) / (B : ℝ)) ((n : ℝ) / (B : ℝ))) zero_lt_one
    (lt_max_of_lt_left hgm)
  · unfold Muon.DetEquiv.classK
    change (Muon.Drift.specOutFM F : Measure ℝ) (Icc 0 1) ≤ _ ∧
      (Muon.Drift.specOutFM F : Measure ℝ) (Icc 0 1)ᶜ = 0 ∧
      (Muon.Drift.specInFM F : Measure ℝ) (Icc 0 1) ≤ _ ∧
      (Muon.Drift.specInFM F : Measure ℝ) (Icc 0 1)ᶜ = 0
    rw [show (Muon.Drift.specOutFM F : Measure ℝ) =
        isoSpecMeasure ((m : ℝ) / (B : ℝ)) from hout,
      show (Muon.Drift.specInFM F : Measure ℝ) =
        isoSpecMeasure ((n : ℝ) / (B : ℝ)) from hin]
    constructor
    · simpa [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply] using
        ENNReal.ofReal_le_ofReal
          (le_max_left ((m : ℝ) / (B : ℝ)) ((n : ℝ) / (B : ℝ)))
    · constructor
      · simp [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply]
      · constructor
        · simpa [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply] using
            ENNReal.ofReal_le_ofReal
              (le_max_right ((m : ℝ) / (B : ℝ)) ((n : ℝ) / (B : ℝ)))
        · simp [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply]
  · exact hs

private lemma bridge_drift_kernel {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {β ϱ : ℝ} (hβ : 0 ≤ β ∧ β < 1)
    (hϱ : 0 < ϱ) :
    Muon.Drift.kernel (Muon.emaW β) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ 1 1 =
      dIso β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ := by
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  obtain ⟨hout, hin⟩ := bridge_drift_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
  unfold Muon.Drift.kernel dIso
  rw [← integral_const_mul, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  let s := ϱ + u ^ 2
  let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β))
    (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s
  have hs : 0 < s := by dsimp [s]; positivity
  have hx : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s x :=
    bridge_drift_branch F hIso hβ hs
  have hcl := prop_app_iso_closure_i hβ.1 hβ.2 hgn hgm hs hout hin hx
  have hq := lem_app_iso_comparison_iii hβ.1 hβ.2 hgn hgm hs hout hin hx
  have hden := hcl.2.2.2.2.2.2.2
  simp only [mul_one]
  change (Real.sqrt 2 / Real.pi) *
      (s * Muon.DetEquiv.Lw (Muon.emaW β) (Muon.Drift.branchQ (Muon.emaW β)
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s) /
        ((s + x.2.2.1) * (s + x.2.2.2))) =
      (Real.sqrt 2 / (Real.pi * ((n : ℝ) / (B : ℝ)) * ((m : ℝ) / (B : ℝ)))) *
        isoGb β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) s
  have hbranch : Muon.Drift.branchQ (Muon.emaW β) (Muon.Drift.specOutFM F)
      (Muon.Drift.specInFM F) s = isoQ s x := rfl
  rw [hbranch, hden, ← hq]
  unfold isoGb qIso
  field_simp

private lemma bridge_drift_isoGb_integrable {β γin γout ϱ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hγin : 0 < γin) (hγout : 0 < γout)
    (hϱ : 0 ≤ ϱ) :
    IntegrableOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi (0 : ℝ)) := by
  have hr := bridge_momentum_link hβ0 hβ1
  have hqcont : ContinuousOn (qIso β γin γout) (Ioi 0) :=
    (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.1
  have hw := bridge_momentum_weightSeq hβ0 hβ1
  have hL := (Muon.DetEquiv.lem_app_de_scalar_ii hw).2.2.2.1
  have hcont : ContinuousOn (isoGb β γin γout) (Ioi 0) := by
    show ContinuousOn (fun s => qIso β γin γout s *
      Muon.DetEquiv.Lw (Muon.emaW β) (qIso β γin γout s)) (Ioi 0)
    refine hqcont.mul (hL.comp hqcont ?_)
    intro z hz
    exact Set.mem_Ici.2
      ((lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 z hz).1.1
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (volume.restrict (Ioi 0)) := by
    have hc : ContinuousOn (fun u : ℝ => isoGb β γin γout (ϱ + u ^ 2)) (Ioi 0) := by
      refine hcont.comp (by fun_prop) ?_
      intro u hu
      have hu0 : 0 < u := hu
      exact Set.mem_Ioi.2 (by nlinarith [sq_pos_of_pos hu0])
    exact hc.aestronglyMeasurable measurableSet_Ioi
  have hbase := (prop_app_iso_zero_i hβ0 hβ1 hγin hγout).2.1
  refine Integrable.mono' hbase hmeas ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun u hu => ?_)
  have hu0 : 0 < u := hu
  have hu2 : 0 < u ^ 2 := sq_pos_of_pos hu0
  have hshift : 0 < ϱ + u ^ 2 := by positivity
  have hq0 := ((lem_app_iso_comparison_i hr hγin hγout).2.2.2.1 (u ^ 2) hu2).1.1
  have hq1 := ((lem_app_iso_comparison_i hr hγin hγout).2.2.2.1
    (ϱ + u ^ 2) hshift).1.1
  have hqle := (lem_app_iso_comparison_i hr hγin hγout).2.2.2.2.2.antitoneOn
    (Set.mem_Ioi.2 hu2) (Set.mem_Ioi.2 hshift) (by linarith)
  have hmono := (lem_app_iso_weights_v hβ0 hβ1).2.2.monotoneOn
    (Set.mem_Ici.2 hq1) (Set.mem_Ici.2 hq0) hqle
  have hp1 := ((prop_app_iso_zero_i hβ0 hβ1 hγin hγout).1 _ hshift).1
  have hp0 := ((prop_app_iso_zero_i hβ0 hβ1 hγin hγout).1 _ hu2).1
  have hgb : isoGb β γin γout (ϱ + u ^ 2) ≤ isoGb β γin γout (u ^ 2) := by
    simpa [isoGb, qIso] using hmono
  calc
    ‖isoGb β γin γout (ϱ + u ^ 2)‖ = isoGb β γin γout (ϱ + u ^ 2) :=
      Real.norm_of_nonneg hp1.le
    _ ≤ isoGb β γin γout (u ^ 2) := hgb

private lemma bridge_drift_matrix_ext {m n : ℕ} {C : Muon.Covariances m n}
    (S : Muon.Setup.SpectralData C) (X Y : Matrix (Fin m) (Fin n) ℝ)
    (h : ∀ i j, dotProduct (S.u i) (X *ᵥ S.v j) = dotProduct (S.u i) (Y *ᵥ S.v j)) :
    X = Y := by
  have hP : S.uOutᵀ * X * S.vIn = S.uOutᵀ * Y * S.vIn := by
    ext i j
    simpa only [Muon.Setup.P_apply] using h i j
  have hu : S.uOut * S.uOutᵀ = 1 := mul_eq_one_comm.mp S.huOut
  have hv : S.vIn * S.vInᵀ = 1 := mul_eq_one_comm.mp S.hvIn
  calc
    X = (S.uOut * S.uOutᵀ) * X * (S.vIn * S.vInᵀ) := by rw [hu, hv, Matrix.one_mul, Matrix.mul_one]
    _ = S.uOut * (S.uOutᵀ * X * S.vIn) * S.vInᵀ := by simp only [Matrix.mul_assoc]
    _ = S.uOut * (S.uOutᵀ * Y * S.vIn) * S.vInᵀ := by rw [hP]
    _ = (S.uOut * S.uOutᵀ) * Y * (S.vIn * S.vInᵀ) := by simp only [Matrix.mul_assoc]
    _ = Y := by rw [hu, hv, Matrix.one_mul, Matrix.mul_one]

private lemma bridge_drift_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I))
    {s : ℝ} (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

private lemma bridge_drift_fro_risk {m n : ℕ} (C : Muon.Covariances m n)
    (D : Matrix (Fin m) (Fin n) ℝ) (hIso : C.Sin = 1 ∧ C.Sout = 1) :
    Muon.fro D = Real.sqrt (2 * Muon.Setup.riskSigma C D) := by
  have hrot : Muon.Setup.Arot C D = D := by
    simp [Muon.Setup.Arot, Muon.Setup.rOut, Muon.Setup.rIn, hIso.1, hIso.2]
  have hrisk : Muon.Setup.riskSigma C D = Muon.fro D ^ 2 / 2 := by
    rw [Muon.Setup.eqn_app_setup_whitened_risk, hrot]
  rw [hrisk, show 2 * (Muon.fro D ^ 2 / 2) = Muon.fro D ^ 2 by ring]
  exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm

private lemma bridge_drift_Fw_eq_Lw_zero (q : ℝ) :
    Muon.DetEquiv.Fw (Muon.emaW 0) q = Muon.DetEquiv.Lw (Muon.emaW 0) q := by
  unfold Muon.DetEquiv.Fw Muon.DetEquiv.Lw
  rw [tsum_eq_single 0, tsum_eq_single 0]
  · simp [Muon.emaW]
  · intro j hj
    simp [Muon.emaW, hj]
  · intro j hj
    simp [Muon.emaW, hj]

/-- `thm:app-iso-drift`, snapshot `cr-2026-10-23`. Declaration of record. Work under `assum:app-setup-regime`
(`R`, with the output and input covariances `Id`, `hIso`) and the frozen-state update `Q_ϱ(M_t)` (`Muon.Drift.EQ`).
Parts (i)–(iv) of the source, with the kernel `Muon.Drift.kernel` of `cor:app-drift-kernel`, the regularized
candidate `Muon.Drift.Gbar` of `eqn:app-drift-Gbar`, and `ε_B = Muon.Drift.epsB`. The standing normalization
`Â = Δ/‖Δ‖_F` and `R(t) = riskSigma` enter as `hDt`, `hRt`. LaTeX, verbatim:

\begin{theorem}[Isotropic drift]\label{thm:app-iso-drift}
Work under \cref{assum:app-setup-regime} with $\Sigmain=\Id_{\Nin}$ and
$\Sigmaout=\Id_{\Nout}$, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update, and let $\varepsilon_B\to0$ be the sequence of
\cref{thm:app-drift-mean}.
\begin{enumerate}[label=(\roman*)]
\item Every kernel $\mathfrak d_{ij}$ of \cref{cor:app-drift-kernel} equals
$\mathfrak d_{\mathrm{iso}}\defeq\mathfrak d(1,1)$, and, with
$z=\ridge+u^2$,
\begin{equation}\label{eqn:app-iso-drift}
\mathfrak d_{\mathrm{iso}}=\frac{\sqrt2}{\pi\,\gin\gout}\int_0^\infty q(-z)\,\Lw\big(q(-z)\big)\,du,
\qquad 0\le\mathfrak d_{\mathrm{iso}}\le\frac{1}{\sqrt{2\ridge}} .
\end{equation}
\item At $\bmom=0$, with $z=\ridge+u^2$,
\begin{equation}\label{eqn:app-iso-drift-nomomentum}
\mathfrak d_{\mathrm{iso}}=\frac{\sqrt2}{\pi\,\gin\gout}\int_0^\infty\psi(z)\,du
=\frac{\sqrt2}{\pi\,\gin\gout}\int_0^\infty\big(\gout-z\,\sigma(-z)\big)\,du .
\end{equation}
\item The candidate \cref{eqn:app-drift-Gbar} is a multiple of the error, and
the expected update is
\begin{equation}\label{eqn:app-iso-mean}
\Gtildebar_\ridge=\frac{\mathfrak d_{\mathrm{iso}}}{\sqrt{\cR(t)}}\,\Dt,\qquad
\EE\,\Gtilde=\frac{\mathfrak d_{\mathrm{iso}}}{\sqrt{\cR(t)}}\,\Dt+E_\ridge,\qquad
\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{E_\ridge}_\F=\varepsilon_B .
\end{equation}
\item The total drift is
\begin{equation}\label{eqn:app-iso-drift-total}
\begin{gathered}
\sum_{i,j}\cD_{ij}(t)=\big\langle\Dt,\EE\,\Gtilde\big\rangle_\F
=2\,\mathfrak d_{\mathrm{iso}}\sqrt{\cR(t)}+\langle\Dt,E_\ridge\rangle_\F,\\
\abs{\langle\Dt,E_\ridge\rangle_\F}\le\sqrt{2\cR(t)}\,\varepsilon_B .
\end{gathered}
\end{equation}
\end{enumerate}
\end{theorem}
-/
theorem thm_app_iso_drift (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (hIso : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1)
    (SD : ∀ k, Muon.Setup.SpectralData (R.F k).C)
    (Dt : ∀ k, Matrix (Fin (R.m k)) (Fin (R.n k)) ℝ)
    (hDt : ∀ k, (R.F k).A = Muon.Setup.Ahat (R.F k).C (Dt k))
    (hRt : ∀ k, 0 < Muon.Setup.riskSigma (R.F k).C (Dt k)) :
    -- (i) every kernel is `d_iso = d(1,1)`, with the bounds of the integral
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, 0 < ϱ →
      IntegrableOn (fun u : ℝ => isoGb R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) (ϱ + u ^ 2))
          (Ioi (0 : ℝ)) ∧
      (∀ i j, Muon.Drift.kernel (Muon.emaW R.β) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k))
          ϱ ((SD k).μ i) ((SD k).lam j) =
        Muon.Drift.kernel (Muon.emaW R.β) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ 1 1) ∧
      Muon.Drift.kernel (Muon.emaW R.β) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ 1 1 =
        dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ ∧
      0 ≤ dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ ∧
      dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ ≤ 1 / Real.sqrt (2 * ϱ)) ∧
    -- (ii) at zero momentum: the integral form with `ψ` and the integral form with `γout − z σ(−z)`,
    -- and the branch identity `ψ(z) = γout − z σ(−z)` at every `z > 0`
    (R.β = 0 → ∀ k, 0 < R.m k → 0 < R.n k →
      (∀ ϱ ∈ Icc R.ϱlo R.ϱhi, 0 < ϱ →
        IntegrableOn (fun u : ℝ => psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) (ϱ + u ^ 2))
            (Ioi (0 : ℝ)) ∧
        dIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ =
          Real.sqrt 2 / (Real.pi * ((R.n k : ℝ) / (R.B k : ℝ)) * ((R.m k : ℝ) / (R.B k : ℝ))) *
            (∫ u in Ioi (0 : ℝ),
              psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) (ϱ + u ^ 2)) ∧
        IntegrableOn (fun u : ℝ =>
            ((R.m k : ℝ) / (R.B k : ℝ)) - (ϱ + u ^ 2) *
              Muon.Drift.branchSigma (Muon.emaW 0) (Muon.Drift.specOutFM (R.F k))
                (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2)) (Ioi (0 : ℝ)) ∧
        (∫ u in Ioi (0 : ℝ),
            psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) (ϱ + u ^ 2)) =
          ∫ u in Ioi (0 : ℝ),
            (((R.m k : ℝ) / (R.B k : ℝ)) - (ϱ + u ^ 2) *
              Muon.Drift.branchSigma (Muon.emaW 0) (Muon.Drift.specOutFM (R.F k))
                (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2))) ∧
      (∀ z : ℝ, 0 < z → ∀ ν ν' : FiniteMeasure ℝ,
        (ν : Measure ℝ) = isoSpecMeasure ((R.m k : ℝ) / (R.B k : ℝ)) →
        (ν' : Measure ℝ) = isoSpecMeasure ((R.n k : ℝ) / (R.B k : ℝ)) →
        ∀ x : ℝ × ℝ × ℝ × ℝ, Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' z x →
          psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) z =
            (R.m k : ℝ) / (R.B k : ℝ) - z * x.1)) ∧
    -- (iii) expected update: `𝔼 G̃ = (d_iso/√R) Dt + E_ϱ`, `sup_ϱ ‖E_ϱ‖_F = ε_B → 0`
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∀ i j, IntegrableOn (fun u : ℝ => Muon.Drift.Tcand (Muon.emaW R.β) (R.F k)
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2) i j) (Ioi (0 : ℝ))) ∧
      Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ =
        (dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
            Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k))) • Dt k) ∧
    (∀ k, BddAbove ((fun ϱ => Muon.fro (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
        Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ)) ''
        Icc R.ϱlo R.ϱhi)) ∧
    (∀ k, (⨆ ϱ ∈ Icc R.ϱlo R.ϱhi, Muon.fro (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
        Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ)) =
      Muon.Drift.epsB (Muon.emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi) ∧
    Tendsto (fun k => Muon.Drift.epsB (Muon.emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
      (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi) atTop (𝓝 0) ∧
    -- (iv) total drift: `∑_{ij} 𝒟_ij(t) = ⟨Dt, 𝔼 G̃⟩_F = 2 d_iso √R + ⟨Dt, E_ϱ⟩_F`, `|⟨Dt,E_ϱ⟩_F| ≤ √(2R) ε_B`.
    -- The frozen-model `𝒟_ij` is rendered as in `cor_app_drift_kernel_i` (u_iᵀ Dt v_j times the integral).
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∑ i, ∑ j, dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
          ∫ ω, dotProduct ((SD k).u i)
            (Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)) =
        (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace ∧
      (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace =
        2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) +
          (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
            Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ)ᵀ).trace ∧
      |(Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
            Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ)ᵀ).trace| ≤
        Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)) *
          Muon.Drift.epsB (Muon.emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi) := by
  have hβ : 0 ≤ R.β ∧ R.β < 1 := by
    have h := (R.F 0).hβ
    rwa [R.hβ 0] at h
  have hC : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hγ : 0 < max R.γstar 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hw := Muon.Drift.emaW_weightClass_regime R
  have hDB : ∀ k, Muon.Drift.DriftBound (R.F k) R.CSig (max R.γstar 1) := by
    intro k
    refine ⟨R.normOut k, R.normIn k, ?_⟩
    exact (R.dims k).trans
      (mul_le_mul_of_nonneg_right (le_max_left R.γstar 1) (Nat.cast_nonneg _))
  have hdims : ∀ k, 0 < R.m k ∧ 0 < R.n k := fun k => bridge_drift_dims_pos (R.F k)
  have hrat : ∀ k,
      0 < (R.n k : ℝ) / (R.B k : ℝ) ∧ 0 < (R.m k : ℝ) / (R.B k : ℝ) := by
    intro k
    exact ⟨div_pos (by exact_mod_cast (hdims k).2) (by exact_mod_cast (R.F k).hB),
      div_pos (by exact_mod_cast (hdims k).1) (by exact_mod_cast (R.F k).hB)⟩
  have heigs : ∀ k, (∀ i, (SD k).μ i = 1) ∧ ∀ j, (SD k).lam j = 1 :=
    fun k => bridge_drift_eigenvalues (R.F k) (SD k) (hIso k)
  have hkern : ∀ k, ∀ ϱ : ℝ, 0 < ϱ →
      Muon.Drift.kernel (Muon.emaW R.β) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ 1 1 =
        dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ :=
    fun k ϱ hϱ => bridge_drift_kernel (R.F k) (hIso k) hβ hϱ
  have hmean := Muon.Drift.thm_app_drift_mean R P S t
  have hcor := Muon.Drift.cor_app_drift_kernel_i R P S t SD Dt hDt hRt
  have hgbar : ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) ϱ =
        (dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
          Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k))) • Dt k := by
    intro k ϱ hϱ
    have hϱpos : 0 < ϱ := R.hϱ.1.trans_le hϱ.1
    apply bridge_drift_matrix_ext (SD k)
    intro i j
    have hd := Muon.Drift.kernel_diag_gbar hC hγ hw (R.F k) (hDB k) (SD k)
      hϱpos i j
    rw [(heigs k).1 i, (heigs k).2 j, one_mul, Real.sqrt_one, one_mul,
      hkern k ϱ hϱpos] at hd
    have hA : (R.F k).A =
        (Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)))⁻¹ • Dt k := by
      rw [hDt k]
      unfold Muon.Setup.Ahat Muon.Setup.Arot
      simp [Muon.Setup.rOut, Muon.Setup.rIn, (hIso k).1, (hIso k).2]
    have hroot : Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)) =
        Real.sqrt 2 * Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hscale : Real.sqrt 2 *
          dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
          (Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)))⁻¹ =
        dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
          Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) := by
      rw [hroot]
      field_simp
    calc
      dotProduct ((SD k).u i)
          (Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) ϱ *ᵥ (SD k).v j) =
          Real.sqrt 2 *
            dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            dotProduct ((SD k).u i) ((R.F k).A *ᵥ (SD k).v j) := hd
      _ = (Real.sqrt 2 *
            dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            (Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)))⁻¹) *
          dotProduct ((SD k).u i) (Dt k *ᵥ (SD k).v j) := by
            rw [hA, Matrix.smul_mulVec, dotProduct_smul]
            simp only [smul_eq_mul]
            ring
      _ = dotProduct ((SD k).u i)
          (((dIso R.β ((R.n k : ℝ) / (R.B k : ℝ))
              ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
              Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k))) • Dt k) *ᵥ
                (SD k).v j) := by
            rw [hscale, Matrix.smul_mulVec, dotProduct_smul]
            simp only [smul_eq_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k ϱ hϱI hϱ
    refine ⟨bridge_drift_isoGb_integrable hβ.1 hβ.2 (hrat k).1 (hrat k).2 hϱ.le,
      ?_, hkern k ϱ hϱ, ?_⟩
    · intro i j
      rw [(heigs k).1 i, (heigs k).2 j]
    · obtain ⟨-, -, -, hbounds, -, -⟩ :=
        Muon.Drift.cor_app_drift_kernel_ii hC hγ hw (R.F k) (hDB k) hϱ
      simpa [hkern k ϱ hϱ] using hbounds 1 1 zero_le_one zero_le_one
  · intro hβzero k hm hn
    have hgn : 0 < (R.n k : ℝ) / (R.B k : ℝ) :=
      div_pos (by exact_mod_cast hn) (by exact_mod_cast (R.F k).hB)
    have hgm : 0 < (R.m k : ℝ) / (R.B k : ℝ) :=
      div_pos (by exact_mod_cast hm) (by exact_mod_cast (R.F k).hB)
    constructor
    · intro ϱ hϱI hϱ
      have hgb := bridge_drift_isoGb_integrable (β := 0) (γin := (R.n k : ℝ) / (R.B k : ℝ))
        (γout := (R.m k : ℝ) / (R.B k : ℝ)) (ϱ := ϱ) (le_refl 0) zero_lt_one hgn hgm hϱ.le
      have hpg : ∀ z : ℝ,
          psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) z =
            isoGb 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) z := by
        intro z
        unfold psiIso isoGb Muon.DetEquiv.rW
        rw [bridge_drift_Fw_eq_Lw_zero]
      have hpsi : IntegrableOn (fun u : ℝ =>
          psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ))
            (ϱ + u ^ 2)) (Ioi (0 : ℝ)) := by
        simpa only [hpg] using hgb
      obtain ⟨hout, hin⟩ := bridge_drift_spec_measures (R.F k) (hIso k)
      have hsig : ∀ u : ℝ,
          psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ))
              (ϱ + u ^ 2) =
            (R.m k : ℝ) / (R.B k : ℝ) - (ϱ + u ^ 2) *
              Muon.Drift.branchSigma (Muon.emaW 0) (Muon.Drift.specOutFM (R.F k))
                (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2) := by
        intro u
        have hz : 0 < ϱ + u ^ 2 := by positivity
        let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2)
        have hx : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0))
            (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2) x :=
          bridge_drift_branch (R.F k) (hIso k) ⟨le_refl 0, zero_lt_one⟩ hz
        have hq := lem_app_iso_comparison_iii (le_refl 0) zero_lt_one hgn hgm hz hout hin hx
        have hc := prop_app_iso_closure_i (le_refl 0) zero_lt_one hgn hgm hz hout hin hx
        unfold psiIso qIso
        rw [hq]
        exact hc.2.2.2.2.1
      have hsigint : IntegrableOn (fun u : ℝ =>
          (R.m k : ℝ) / (R.B k : ℝ) - (ϱ + u ^ 2) *
            Muon.Drift.branchSigma (Muon.emaW 0) (Muon.Drift.specOutFM (R.F k))
              (Muon.Drift.specInFM (R.F k)) (ϱ + u ^ 2)) (Ioi (0 : ℝ)) := by
        apply hpsi.congr
        exact ae_restrict_of_forall_mem measurableSet_Ioi (fun u _ => hsig u)
      refine ⟨hpsi, ?_, hsigint, ?_⟩
      · unfold dIso
        rw [show (fun u : ℝ =>
              isoGb 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ))
                (ϱ + u ^ 2)) =
            (fun u : ℝ =>
              psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ))
                (ϱ + u ^ 2)) by funext u; exact (hpg _).symm]
      · exact setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsig u)
    · intro z hz ν ν' hν hν' x hx
      have hq := lem_app_iso_comparison_iii (le_refl 0) zero_lt_one hgn hgm hz hν hν' hx
      have hc := prop_app_iso_closure_i (le_refl 0) zero_lt_one hgn hgm hz hν hν' hx
      unfold psiIso qIso
      rw [hq]
      exact hc.2.2.2.2.1
  · intro k ϱ hϱ
    exact ⟨(hmean.1 k ϱ hϱ).1, hgbar k ϱ hϱ⟩
  · exact hmean.2.1
  · intro k
    rfl
  · exact hmean.2.2.1
  · intro k ϱ hϱ
    have hϱpos : 0 < ϱ := R.hϱ.1.trans_le hϱ.1
    have hproj : ∀ i j,
        (∫ ω, dotProduct ((SD k).u i)
            (Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω) *ᵥ
              (SD k).v j) ∂(P k)) =
          dotProduct ((SD k).u i)
            (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ *ᵥ (SD k).v j) := by
      intro i j
      have hp := (hcor.1 k i j ϱ hϱ).2
      rw [(heigs k).1 i, (heigs k).2 j, hkern k ϱ hϱpos] at hp
      unfold Muon.Drift.Erho at hp
      simp only [Matrix.of_apply, Matrix.sub_mulVec, dotProduct_sub] at hp
      have hgc : dotProduct ((SD k).u i)
          (Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) ϱ *ᵥ (SD k).v j) =
          dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
              Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) *
            dotProduct ((SD k).u i) (Dt k *ᵥ (SD k).v j) := by
        rw [hgbar k ϱ hϱ, Matrix.smul_mulVec, dotProduct_smul]
        simp only [smul_eq_mul]
      rw [hgc] at hp
      linarith
    have hfirst :
        (∑ i, ∑ j, dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
            ∫ ω, dotProduct ((SD k).u i)
              (Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω) *ᵥ
                (SD k).v j) ∂(P k)) =
          (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace := by
      simp_rw [hproj]
      have hp := Muon.Setup.pairSigma_eq_sum (SD k) (Dt k)
        (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)
      unfold Muon.Setup.pairSigma at hp
      rw [(hIso k).1, (hIso k).2] at hp
      simp only [Matrix.one_mul, Matrix.mul_one] at hp
      simp_rw [(heigs k).1, (heigs k).2, one_mul] at hp
      exact hp.symm
    have hDD : (Dt k * (Dt k)ᵀ).trace =
        2 * Muon.Setup.riskSigma (R.F k).C (Dt k) := by
      unfold Muon.Setup.riskSigma Muon.Setup.pairSigma
      rw [(hIso k).1, (hIso k).2]
      simp only [Matrix.one_mul, Matrix.mul_one]
      ring
    have hsecond :
        (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace =
          2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
              Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) +
            (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ -
              Muon.Drift.Gbar (Muon.emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
                (Muon.Drift.specInFM (R.F k)) ϱ)ᵀ).trace := by
      let G := Muon.Drift.Gbar (Muon.emaW R.β) (R.F k)
        (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) ϱ
      let E := Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ - G
      change (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace =
        2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) + (Dt k * Eᵀ).trace
      have heq : Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ = G + E := by
        dsimp [E]
        abel
      have hmain : (Dt k * Gᵀ).trace =
          2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k)) := by
        dsimp [G]
        rw [hgbar k ϱ hϱ]
        simp only [Matrix.transpose_smul, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
        rw [hDD]
        let d := dIso R.β ((R.n k : ℝ) / (R.B k : ℝ))
          ((R.m k : ℝ) / (R.B k : ℝ)) ϱ
        let r := Muon.Setup.riskSigma (R.F k).C (Dt k)
        change d / Real.sqrt r * (2 * r) = 2 * d * Real.sqrt r
        have hspos : 0 < Real.sqrt r := Real.sqrt_pos.mpr (hRt k)
        have hs : Real.sqrt r ^ 2 = r := Real.sq_sqrt (hRt k).le
        have hcancel : d * r / Real.sqrt r = d * Real.sqrt r := by
          apply (div_eq_iff hspos.ne').2
          calc
            d * r = d * Real.sqrt r ^ 2 := congrArg (fun x => d * x) hs.symm
            _ = d * Real.sqrt r * Real.sqrt r := by ring
        calc
          d / Real.sqrt r * (2 * r) = 2 * (d * r / Real.sqrt r) := by ring
          _ = 2 * d * Real.sqrt r := by
            rw [hcancel]
            ring
      calc
        (Dt k * (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace =
            (Dt k * (G + E)ᵀ).trace := congrArg (fun X => (Dt k * Xᵀ).trace) heq
        _ = (Dt k * Gᵀ).trace + (Dt k * Eᵀ).trace := by
          rw [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]
        _ = _ := by rw [hmain]
    have hpair := hmean.2.2.2 k (Dt k)
    have herr0 := bridge_drift_le_biSup hpair.1 hϱ
    have herr1 := herr0.trans hpair.2
    have hfro := bridge_drift_fro_risk (R.F k).C (Dt k) (hIso k)
    rw [hfro] at herr1
    exact ⟨hfirst, hsecond, herr1⟩

/-! ## The volatility (`thm:app-iso-volatility`) -/

private lemma bridge_vol_abs_entry_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
    |K i j| ≤ Muon.fro K := by
  unfold Muon.fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma bridge_vol_summable_mat_of_fro {k l : ℕ} {ι : Type*} (f : ι → Mat k l)
    (hf : Summable fun j => Muon.fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun j => ?_
  refine Summable.of_norm_bounded hf (fun q => ?_)
  rw [Real.norm_eq_abs]
  exact bridge_vol_abs_entry_le_fro (f q) i j

private lemma bridge_vol_summand_cont {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B) :
    Continuous (fun p : Muon.Vec m × Muon.Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) •
        (Muon.Setup.rOut F.C * Muon.outer p.1 p.2 * Muon.Setup.rIn F.C)) := by
  fun_prop

private lemma bridge_vol_batch_sm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (Muon.Setup.frozenBatchG F S s) := by
  unfold Muon.Setup.frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (bridge_vol_summand_cont F).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private lemma bridge_vol_buf_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (t : ℤ) :
    AEStronglyMeasurable (Muon.Setup.frozenBuf F S t) P := by
  have : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hae := (Muon.Setup.lem_app_setup_ema_law_i F S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, Muon.emaW F.β j •
      Muon.Setup.frozenBatchG F S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (bridge_vol_batch_sm F S (t + 1 - (j : ℤ))).const_smul
        (Muon.emaW F.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    have hs : Summable (fun j : ℕ => Muon.emaW F.β j •
        Muon.Setup.frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      bridge_vol_summable_mat_of_fro _ (hω t)
    exact hs.hasSum.tendsto_sum_nat

private lemma bridge_vol_Q_meas {k l : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Measurable (fun K : Mat k l => Muon.Q ϱ K) :=
  (Muon.Setup.measurable_Q (m := k) (n := l)).comp
    ((measurable_const (a := (⟨ϱ, hϱ.le⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma bridge_vol_opNorm_transpose {k l : ℕ} (A : Mat k l) :
    Muon.opNorm Aᵀ = Muon.opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [Muon.opNorm_eq_norm, Muon.opNorm_eq_norm,
    ← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.l2_opNorm_conjTranspose]

private lemma bridge_vol_upd_aesm {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) :
    AEStronglyMeasurable (Muon.Setup.frozenUpd F S ϱ t) P := by
  exact ((bridge_vol_Q_meas ϱ hϱ).comp_aemeasurable
    (bridge_vol_buf_aesm F S t).aemeasurable).aestronglyMeasurable

private lemma bridge_vol_row_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (Sp : Muon.Setup.SpectralData F.C)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) (i : Fin m) :
    Integrable (fun ω => dotProduct ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
      ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)) P := by
  let u : EuclideanSpace ℝ (Fin m) := (EuclideanSpace.equiv (Fin m) ℝ).symm (Sp.u i)
  have hu : ‖u‖ = 1 := by
    have h := Muon.Setup.sum_col_sq_eq_one Sp.uOut Sp.huOut i
    rw [EuclideanSpace.norm_eq]
    simpa [u, Muon.Setup.SpectralData.u, Real.norm_eq_abs, sq_abs, sq] using h
  refine Integrable.of_bound (C := 1) ?_ ?_
  · have hc : Continuous (fun K : Mat m n => dotProduct (Kᵀ *ᵥ Sp.u i) (Kᵀ *ᵥ Sp.u i)) := by
      fun_prop
    exact hc.comp_aestronglyMeasurable (bridge_vol_upd_aesm F S hϱ t)
  · refine Filter.Eventually.of_forall fun ω => ?_
    let v : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm
      ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
    have hv := Matrix.l2_opNorm_mulVec (Muon.Setup.frozenUpd F S ϱ t ω)ᵀ u
    have hop : Muon.opNorm (Muon.Setup.frozenUpd F S ϱ t ω)ᵀ ≤ 1 := by
      rw [bridge_vol_opNorm_transpose]
      exact (Muon.Setup.lem_app_setup_filter_i ϱ hϱ.le (Muon.Setup.frozenBuf F S t ω)).1
    open scoped Matrix.Norms.L2Operator in
      rw [← Muon.opNorm_eq_norm, hu, mul_one] at hv
    have hv1 : ‖v‖ ≤ 1 := hv.trans hop
    have he : dotProduct ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
        ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [v, dotProduct, Real.norm_eq_abs, sq_abs, sq]
    rw [Real.norm_eq_abs, he, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg v]

private lemma bridge_vol_col_integrable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (Sp : Muon.Setup.SpectralData F.C)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) (j : Fin n) :
    Integrable (fun ω => dotProduct (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)
      (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)) P := by
  let u : EuclideanSpace ℝ (Fin n) := (EuclideanSpace.equiv (Fin n) ℝ).symm (Sp.v j)
  have hu : ‖u‖ = 1 := by
    have h := Muon.Setup.sum_col_sq_eq_one Sp.vIn Sp.hvIn j
    rw [EuclideanSpace.norm_eq]
    simpa [u, Muon.Setup.SpectralData.v, Real.norm_eq_abs, sq_abs, sq] using h
  refine Integrable.of_bound (C := 1) ?_ ?_
  · have hc : Continuous (fun K : Mat m n => dotProduct (K *ᵥ Sp.v j) (K *ᵥ Sp.v j)) := by
      fun_prop
    exact hc.comp_aestronglyMeasurable (bridge_vol_upd_aesm F S hϱ t)
  · refine Filter.Eventually.of_forall fun ω => ?_
    let v : EuclideanSpace ℝ (Fin m) := (EuclideanSpace.equiv (Fin m) ℝ).symm
      (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)
    have hv := Matrix.l2_opNorm_mulVec (Muon.Setup.frozenUpd F S ϱ t ω) u
    have hop : Muon.opNorm (Muon.Setup.frozenUpd F S ϱ t ω) ≤ 1 :=
      (Muon.Setup.lem_app_setup_filter_i ϱ hϱ.le (Muon.Setup.frozenBuf F S t ω)).1
    open scoped Matrix.Norms.L2Operator in
      rw [← Muon.opNorm_eq_norm, hu, mul_one] at hv
    have hv1 : ‖v‖ ≤ 1 := hv.trans hop
    have he : dotProduct (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)
        (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j) = ‖v‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [v, dotProduct, Real.norm_eq_abs, sq_abs, sq]
    rw [Real.norm_eq_abs, he, abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg v]

private lemma bridge_vol_raw_anchors {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (∀ i, Muon.Volatility.volraw F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F)
      (Sp.μ i) ϱ = psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ /
        ((m : ℝ) / (B : ℝ))) ∧
    (∀ j, Muon.Volatility.volTildeZero F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F)
      (Sp.lam j) ϱ = psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ /
        ((n : ℝ) / (B : ℝ))) := by
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  obtain ⟨hμ, hlam⟩ := bridge_drift_eigenvalues F Sp hIso
  obtain ⟨hout, hin⟩ := bridge_drift_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) :=
    div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
  let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW F.β))
    (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ
  have hx := bridge_drift_branch F hIso F.hβ hϱ
  obtain ⟨hsigma, hsigma', ha, hc, -, -, -, -⟩ :=
    prop_app_iso_closure_i F.hβ.1 F.hβ.2 hgn hgm hϱ hout hin hx
  change x.1 = (m : ℝ) / (B : ℝ) / (ϱ + x.2.2.1) at hsigma
  change x.2.1 = (n : ℝ) / (B : ℝ) / (ϱ + x.2.2.2) at hsigma'
  change x.2.2.1 * x.1 = isoPsi F.β ϱ x at ha
  change x.2.2.2 * x.2.1 = isoPsi F.β ϱ x at hc
  have hq := lem_app_iso_comparison_iii F.hβ.1 F.hβ.2 hgn hgm hϱ hout hin hx
  have hpsi : psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ =
      isoPsi F.β ϱ x := by
    unfold psiIso isoPsi qIso
    rw [hq]
  have hden : 0 < ϱ + x.2.2.1 := by
    have := hx.2.2.1
    change 0 ≤ x.2.2.1 at this
    linarith
  have hden' : 0 < ϱ + x.2.2.2 := by
    have := hx.2.2.2.1
    change 0 ≤ x.2.2.2 at this
    linarith
  constructor
  · intro i
    unfold Muon.Volatility.volraw
    rw [hμ i]
    simp only [mul_one]
    change x.2.2.1 / (ϱ + x.2.2.1) = _
    rw [hpsi, ← ha]
    rw [hsigma]
    field_simp [hden.ne', F.hB.ne']
  · intro j
    unfold Muon.Volatility.volTildeZero
    rw [hlam j]
    simp only [mul_one]
    change x.2.2.2 / (ϱ + x.2.2.2) = _
    rw [hpsi, ← hc]
    rw [hsigma']
    field_simp [hden'.ne', F.hB.ne']

private lemma bridge_vol_zbar {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Volatility.zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) Sp.μ ϱ =
      psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ := by
  obtain ⟨hm, -⟩ := bridge_drift_dims_pos F
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hμ := (bridge_drift_eigenvalues F Sp hIso).1
  have hraw := (bridge_vol_raw_anchors F Sp hIso hϱ).1
  unfold Muon.Volatility.zbarRaw
  simp_rw [hraw, hμ]
  simp only [one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

private lemma bridge_vol_opNorm_nonneg {m n : ℕ} (A : Mat m n) : 0 ≤ Muon.opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [Muon.opNorm_eq_norm]
  exact norm_nonneg _

private lemma bridge_vol_opNorm_one (d : ℕ) : Muon.opNorm (1 : Mat d d) ≤ 1 := by
  unfold Muon.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [Matrix.toEuclideanLin]

private lemma bridge_vol_size_one (R : Muon.Setup.SetupRegime) (k : ℕ)
    (hIso : (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1) :
    Muon.Volatility.SizeFin (R.F k).C (R.B k) R.γstar 1 := by
  refine ⟨R.dims k, ?_, ?_⟩
  · rw [hIso.2]
    exact bridge_vol_opNorm_one _
  · rw [hIso.1]
    exact bridge_vol_opNorm_one _

private lemma bridge_vol_zeta (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (ϱ : ℝ) :
    Muon.Volatility.measureZeta cert γstar CSig F Sp ϱ =
      Finsupp.single ((1 : ℝ), (1 : ℝ))
        (isoVol cert γstar CSig F.β m n B ϱ / (B : ℝ)) := by
  classical
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  let im : Fin m := ⟨0, hm⟩
  let jn : Fin n := ⟨0, hn⟩
  have hμ : Sp.μ = fun _ => (1 : ℝ) := funext (bridge_drift_eigenvalues F Sp hIso).1
  have hlam : Sp.lam = fun _ => (1 : ℝ) := funext (bridge_drift_eigenvalues F Sp hIso).2
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  unfold Muon.Volatility.measureZeta Muon.Volatility.muVals Muon.Volatility.lamVals
    Muon.Volatility.pairMeasure
  rw [hμ, hlam]
  have hmvals : Finset.image (fun _ : Fin m => (1 : ℝ)) Finset.univ = {1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨i, rfl⟩
      rfl
    · intro hx
      subst x
      exact ⟨im, rfl⟩
  have hnvals : Finset.image (fun _ : Fin n => (1 : ℝ)) Finset.univ = {1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨j, rfl⟩
      rfl
    · intro hx
      subst x
      exact ⟨jn, rfl⟩
  rw [hmvals, hnvals]
  simp only [Finset.sum_singleton]
  have hclassm : Muon.Volatility.classDiag (fun _ : Fin m => (1 : ℝ)) 1 = fun _ => 1 := by
    funext i
    simp [Muon.Volatility.classDiag]
  have hclassn : Muon.Volatility.classDiag (fun _ : Fin n => (1 : ℝ)) 1 = fun _ => 1 := by
    funext j
    simp [Muon.Volatility.classDiag]
  rw [hclassm, hclassn]
  unfold isoVol
  field_simp

private lemma bridge_vol_psi_zero {m n B : ℕ} (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ =
      isoPhi (qIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ) := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hgn : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) hBr
  have hgm : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) hBr
  have hq := (bridge_momentum_root (le_refl 0) zero_lt_one hgn hgm hϱ).1
  have hW := (lem_app_iso_weights_i (le_refl 0) zero_lt_one).2.2.2 rfl
  have h := hW.1 (qIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ) hq
  simpa only [psiIso] using h

private lemma bridge_vol_psi_branch {m n B : ℕ} (hm : 0 < m) (hn : 0 < n) (hB : 0 < B)
    {ϱ : ℝ} (hϱ : 0 < ϱ) (ν ν' : FiniteMeasure ℝ)
    (hν : (ν : Measure ℝ) = isoSpecMeasure ((m : ℝ) / (B : ℝ)))
    (hν' : (ν' : Measure ℝ) = isoSpecMeasure ((n : ℝ) / (B : ℝ)))
    (x : ℝ × ℝ × ℝ × ℝ)
    (hx : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' ϱ x) :
    psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ =
      (m : ℝ) / (B : ℝ) - ϱ * x.1 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hgn : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) hBr
  have hgm : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) hBr
  have hc := prop_app_iso_closure_i (le_refl 0) zero_lt_one hgn hgm hϱ hν hν' hx
  have hq := lem_app_iso_comparison_iii (le_refl 0) zero_lt_one hgn hgm hϱ hν hν' hx
  have hp : psiIso 0 ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ =
      isoPsi 0 ϱ x := by
    unfold psiIso isoPsi qIso
    rw [hq]
  exact hp.trans hc.2.2.2.2.1

private lemma bridge_vol_total
    (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (Sp : ∀ k, Muon.Setup.SpectralData (R.F k).C)
    (hIso : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1) :
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((Muon.Volatility.sameTimeZ (R.F k) (S k) ϱ t ω -
          psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  have h := Muon.Volatility.thm_app_vol_half_same_iii_raw R P S t Sp (fun k => (hIso k).1)
  convert h using 1
  funext k
  apply lintegral_congr
  intro ω
  apply iSup_congr
  intro ϱ
  apply iSup_congr
  intro hϱI
  rw [bridge_vol_zbar (R.F k) (Sp k) (hIso k) (R.hϱ.1.trans_le hϱI.1), R.hβ k]

private lemma bridge_vol_row_bound {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (Sp : Muon.Setup.SpectralData F.C)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (t : ℤ) {ϱlo ϱhi e : ℝ}
    (hlo : 0 < ϱlo)
    (he : ∀ s ∈ Icc ϱlo ϱhi, Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW F.β) F S t s -
      Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW F.β))
        (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ e)
    {ϱ : ℝ} (hϱI : ϱ ∈ Icc ϱlo ϱhi) (i : Fin m) :
    Integrable (fun ω => dotProduct ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
      ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)) P ∧
    |(∫ ω, dotProduct ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
        ((Muon.Setup.frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) ∂P) -
      psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ /
        ((m : ℝ) / (B : ℝ))| ≤ ϱhi * e := by
  have hϱ0 : 0 < ϱ := hlo.trans_le hϱI.1
  refine ⟨bridge_vol_row_integrable F S Sp hϱ0 t i, ?_⟩
  have h := Muon.Volatility.thm_app_vol_half_same_ii_rows F S t Sp
    ϱlo ϱhi e hlo he ϱ hϱI i
  rw [(bridge_vol_raw_anchors F Sp hIso hϱ0).1 i] at h
  exact h

private lemma bridge_vol_col_bound {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (Sp : Muon.Setup.SpectralData F.C)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (t : ℤ) {ϱlo ϱhi e : ℝ}
    (hlo : 0 < ϱlo)
    (he : ∀ s ∈ Icc ϱlo ϱhi, Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW F.β) F S t s -
      Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW F.β))
        (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ e)
    {ϱ : ℝ} (hϱI : ϱ ∈ Icc ϱlo ϱhi) (j : Fin n) :
    Integrable (fun ω => dotProduct (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)
      (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)) P ∧
    |(∫ ω, dotProduct (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j)
        (Muon.Setup.frozenUpd F S ϱ t ω *ᵥ Sp.v j) ∂P) -
      psiIso F.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ /
        ((n : ℝ) / (B : ℝ))| ≤ ϱhi * e := by
  have hϱ0 : 0 < ϱ := hlo.trans_le hϱI.1
  refine ⟨bridge_vol_col_integrable F S Sp hϱ0 t j, ?_⟩
  have h := Muon.Volatility.thm_app_vol_half_same_ii_cols F S t Sp
    ϱlo ϱhi e hlo he ϱ hϱI j
  rw [(bridge_vol_raw_anchors F Sp hIso hϱ0).2 j] at h
  exact h

private lemma bridge_vol_opNorm_le_fro {p q : ℕ} (K : Mat p q) :
    Muon.opNorm K ≤ Muon.fro K := by
  unfold Muon.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Muon.fro,
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2
      = ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 :=
        Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      (Finset.sum_mul _ _ _).symm

open scoped Matrix.Norms.L2Operator in
private lemma bridge_vol_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q)
    (i : Fin p) (j : Fin q) : |K i j| ≤ Muon.opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [Muon.opNorm_eq_norm]
  linarith

private lemma bridge_vol_fro_le_entries {p q : ℕ} (K : Mat p q) {c : ℝ} (hc : 0 ≤ c)
    (hK : ∀ i j, |K i j| ≤ c) :
    Muon.fro K ≤ Real.sqrt ((p : ℝ) * (q : ℝ) * c ^ 2) := by
  unfold Muon.fro
  refine Real.sqrt_le_sqrt ?_
  calc
    (∑ i, ∑ j, ‖K i j‖ ^ 2) ≤ ∑ _i : Fin p, ∑ _j : Fin q, c ^ 2 := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (hK i j) 2
    _ = (p : ℝ) * (q : ℝ) * c ^ 2 := by
      simp [Finset.sum_const, nsmul_eq_mul]
      ring

private lemma bridge_vol_expRes_op {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (t : ℤ) {s lo : ℝ} (hlo : 0 < lo)
    (hls : lo ≤ s) :
    Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW F.β) F S t s) ≤
      Real.sqrt ((m : ℝ) * (m : ℝ) * (1 / lo) ^ 2) := by
  refine (bridge_vol_opNorm_le_fro _).trans
    (bridge_vol_fro_le_entries _ (by positivity) fun i j => ?_)
  change |∫ ω, Muon.DetEquiv.Rs
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j ∂P| ≤ 1 / lo
  have hs : 0 < s := hlo.trans_le hls
  have hb : ∀ ω, |Muon.DetEquiv.Rs
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j| ≤ 1 / lo := by
    intro ω
    exact (bridge_vol_abs_entry_le_opNorm _ i j).trans
      ((Muon.DetEquiv.lem_app_de_resolvent _ s hs).1.trans
      (one_div_le_one_div_of_le hlo hls))
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => Muon.DetEquiv.Rs
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j) (C := 1 / lo)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  simpa [Real.norm_eq_abs] using h

private lemma bridge_vol_expResT_op {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (F : Muon.Setup.FrozenParams m n B)
    (S : Muon.Setup.FrozenSamples P m n B) (t : ℤ) {s lo : ℝ} (hlo : 0 < lo)
    (hls : lo ≤ s) :
    Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW F.β) F S t s) ≤
      Real.sqrt ((n : ℝ) * (n : ℝ) * (1 / lo) ^ 2) := by
  refine (bridge_vol_opNorm_le_fro _).trans
    (bridge_vol_fro_le_entries _ (by positivity) fun i j => ?_)
  change |∫ ω, Muon.DetEquiv.Rts
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j ∂P| ≤ 1 / lo
  have hs : 0 < s := hlo.trans_le hls
  have hb : ∀ ω, |Muon.DetEquiv.Rts
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j| ≤ 1 / lo := by
    intro ω
    exact (bridge_vol_abs_entry_le_opNorm _ i j).trans
      ((Muon.DetEquiv.lem_app_de_resolvent _ s hs).2.1.trans
      (one_div_le_one_div_of_le hlo hls))
  have h := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => Muon.DetEquiv.Rts
      (Muon.DetEquiv.WeightedBuf (Muon.emaW F.β) F S t ω) s i j) (C := 1 / lo)
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hb ω)
  simpa [Real.norm_eq_abs] using h

private lemma bridge_vol_opNorm_le_of_sq {a b : ℕ} (K : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Muon.Vec b, ∑ k, (K *ᵥ x) k ^ 2 ≤ c ^ 2 * ∑ i, x i ^ 2) :
    Muon.opNorm K ≤ c := by
  unfold Muon.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖Matrix.toEuclideanLin K x‖ ≤ c * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin K x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin K x), mul_nonneg hc (norm_nonneg x)]

private lemma bridge_vol_inv_opNorm_le {k : ℕ} (S : Mat k k) (hS : S.PosSemidef)
    {a s : ℝ} (ha : 0 ≤ a) (hs : 0 < s) :
    Muon.opNorm (s • (1 : Mat k k) + a • S)⁻¹ ≤ 1 / s := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hMy : ∀ (y : Muon.Vec k) (i : Fin k), (M *ᵥ y) i = s * y i + a * (S *ᵥ y) i := by
    intro y i
    simp [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have key : ∀ y : Muon.Vec k, s ^ 2 * ∑ i, y i ^ 2 ≤ ∑ i, (M *ᵥ y) i ^ 2 := by
    intro y
    have hYnn : 0 ≤ ∑ i, y i * (S *ᵥ y) i := by
      have h := hS.dotProduct_mulVec_nonneg y
      simpa [dotProduct, star_trivial] using h
    have hz : 0 ≤ ∑ i, (S *ᵥ y) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have e : ∑ i, (M *ᵥ y) i ^ 2 =
        ∑ i, (s ^ 2 * y i ^ 2 + 2 * s * a * (y i * (S *ᵥ y) i) +
          a ^ 2 * (S *ᵥ y) i ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hMy]
      ring
    rw [e]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hs.le) ha) hYnn,
      mul_nonneg (sq_nonneg a) hz]
  have hinj : Function.Injective (M *ᵥ ·) := by
    intro y y' h
    have h' : M *ᵥ y = M *ᵥ y' := h
    have h0 : M *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h', sub_self]
    have h1 := key (y - y')
    have h2 : ∑ i, (M *ᵥ (y - y')) i ^ 2 = 0 := by rw [h0]; simp
    have hnn : 0 ≤ ∑ i, (y - y') i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, (y - y') i ^ 2 = 0 := by
      have hs2 : 0 < s ^ 2 := pow_pos hs 2
      refine le_antisymm ?_ hnn
      nlinarith
    have hz : ∀ i, (y - y') i = 0 := fun i => by
      have hzero := (Finset.sum_eq_zero_iff_of_nonneg
        (fun i _ => sq_nonneg ((y - y') i))).mp hsum i (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).mp hzero
    exact sub_eq_zero.mp (funext hz)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hu)
  refine bridge_vol_opNorm_le_of_sq _ (one_div_nonneg.mpr hs.le) fun v => ?_
  have hv : M *ᵥ (M⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h := key (M⁻¹ *ᵥ v)
  rw [hv] at h
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  rw [div_pow, one_pow, one_div]
  calc
    ∑ i, (M⁻¹ *ᵥ v) i ^ 2 = (s ^ 2)⁻¹ * (s ^ 2 * ∑ i, (M⁻¹ *ᵥ v) i ^ 2) := by
      rw [← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
    _ ≤ (s ^ 2)⁻¹ * ∑ i, v i ^ 2 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs2.le)

open scoped Matrix.Norms.L2Operator in
private lemma bridge_vol_opNorm_sub_le {a b : ℕ} (A B : Mat a b) :
    Muon.opNorm (A - B) ≤ Muon.opNorm A + Muon.opNorm B := by
  rw [Muon.opNorm_eq_norm, Muon.opNorm_eq_norm, Muon.opNorm_eq_norm]
  exact norm_sub_le _ _

private lemma bridge_vol_Rbar_op {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {s : ℝ} (hs : 0 < s) :
    Muon.opNorm (Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW F.β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ 1 / s := by
  have hb := bridge_drift_branch F hIso F.hβ hs
  unfold Muon.DetEquiv.Rbar
  exact bridge_vol_inv_opNorm_le F.C.Sout F.C.psdOut hb.2.2.1 hs

private lemma bridge_vol_Rtbar_op {m n B : ℕ} (F : Muon.Setup.FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {s : ℝ} (hs : 0 < s) :
    Muon.opNorm (Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW F.β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ 1 / s := by
  have hb := bridge_drift_branch F hIso F.hβ hs
  unfold Muon.DetEquiv.Rtbar
  exact bridge_vol_inv_opNorm_le F.C.Sin F.C.psdIn hb.2.2.2.1 hs

private lemma bridge_vol_errors
    (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (hIso : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1) :
    ∃ e : ℕ → ℝ, Tendsto e atTop (𝓝 0) ∧
      ∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi,
        Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
            (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ e k ∧
        Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
            (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ e k := by
  let e : ℕ → ℝ := fun k => ⨆ s ∈ Icc R.ϱlo R.ϱhi,
    (Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t s -
        Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C s) +
      Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW R.β) (R.F k) (S k) t s -
        Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C s))
  have he : Tendsto e atTop (𝓝 0) := by
    exact Muon.DetEquiv.thm_app_de_gram R (Muon.emaW R.β)
      (Muon.Drift.emaW_weightClass_regime R) P S
      (fun k => Muon.Drift.specOutFM (R.F k)) (fun k => Muon.Drift.specInFM (R.F k))
      (fun _ => rfl) (fun _ => rfl) t (Icc R.ϱlo R.ϱhi) isCompact_Icc
      (fun s hs => R.hϱ.1.trans_le hs.1)
  refine ⟨e, he, ?_⟩
  intro k s hsI
  have hs : 0 < s := R.hϱ.1.trans_le hsI.1
  let g : ℝ → ℝ := fun x =>
    Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t x -
        Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C x) +
      Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW R.β) (R.F k) (S k) t x -
        Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW R.β))
          (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) (R.F k).C x)
  let c : ℝ := Real.sqrt ((R.m k : ℝ) * (R.m k : ℝ) * (1 / R.ϱlo) ^ 2) +
    1 / R.ϱlo + Real.sqrt ((R.n k : ℝ) * (R.n k : ℝ) * (1 / R.ϱlo) ^ 2) +
    1 / R.ϱlo
  have hg : ∀ x ∈ Icc R.ϱlo R.ϱhi, g x ≤ c := by
    intro x hx
    have hx0 : 0 < x := R.hϱ.1.trans_le hx.1
    have hE := bridge_vol_expRes_op (R.F k) (S k) t R.hϱ.1 hx.1
    have hET := bridge_vol_expResT_op (R.F k) (S k) t R.hϱ.1 hx.1
    have hR := bridge_vol_Rbar_op (R.F k) (hIso k) hx0
    have hRT := bridge_vol_Rtbar_op (R.F k) (hIso k) hx0
    have hlo : 1 / x ≤ 1 / R.ϱlo := one_div_le_one_div_of_le R.hϱ.1 hx.1
    dsimp [g, c]
    rw [R.hβ k] at hE hET hR hRT
    calc
      _ ≤ (Real.sqrt ((R.m k : ℝ) * (R.m k : ℝ) * (1 / R.ϱlo) ^ 2) +
          1 / R.ϱlo) +
          (Real.sqrt ((R.n k : ℝ) * (R.n k : ℝ) * (1 / R.ϱlo) ^ 2) +
          1 / R.ϱlo) := add_le_add
        ((bridge_vol_opNorm_sub_le _ _).trans (add_le_add hE (hR.trans hlo)))
        ((bridge_vol_opNorm_sub_le _ _).trans (add_le_add hET (hRT.trans hlo)))
      _ = _ := by ring
  have hc : 0 ≤ c := by
    dsimp [c]
    have hlo : 0 ≤ 1 / R.ϱlo := one_div_nonneg.mpr R.hϱ.1.le
    positivity
  have hb : BddAbove (g '' Icc R.ϱlo R.ϱhi) :=
    ⟨c, by rintro _ ⟨x, hx, rfl⟩; exact hg x hx⟩
  have hsup : g s ≤ e k := by
    simpa [e, g] using bridge_drift_le_biSup hb hsI
  dsimp [g] at hsup
  exact ⟨(le_add_of_nonneg_right (bridge_vol_opNorm_nonneg _)).trans hsup,
    (le_add_of_nonneg_left (bridge_vol_opNorm_nonneg _)).trans hsup⟩

private lemma bridge_vol_integrated {m n B : ℕ} (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C) (hSize : Muon.Volatility.SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    {ϱlo ϱhi ϱ : ℝ} (hI : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (hϱI : ϱ ∈ Icc ϱlo ϱhi) :
    0 ≤ isoVol cert γstar CSig F.β m n B ϱ ∧
    (∀ i j, Muon.Volatility.modeVij cert γstar CSig F Sp ϱ i j =
      isoVol cert γstar CSig F.β m n B ϱ / ((m : ℝ) * (n : ℝ))) ∧
    (∀ i, Muon.Volatility.rowVBar cert γstar CSig F.β B Sp.μ Sp.lam i ϱ ϱ =
      isoVol cert γstar CSig F.β m n B ϱ / (m : ℝ)) ∧
    Muon.Volatility.measureZeta cert γstar CSig F Sp ϱ =
      Finsupp.single ((1 : ℝ), (1 : ℝ))
        (isoVol cert γstar CSig F.β m n B ϱ / (B : ℝ)) := by
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  obtain ⟨hμ, hlam⟩ := bridge_drift_eigenvalues F Sp hIso
  have hϱ0 : 0 < ϱ := hI.1.trans_le hϱI.1
  have hz := bridge_vol_zeta cert γstar CSig F Sp hIso ϱ
  have hnon := (Muon.Volatility.thm_app_vol_joint_forcing_iii_nonneg cert γstar CSig F Sp
    hSize hCSig ϱlo ϱhi hI).1 ϱ hϱI 1 1
  rw [hz] at hnon
  have hdiv : 0 ≤ isoVol cert γstar CSig F.β m n B ϱ / (B : ℝ) := by
    simpa using hnon
  have hBr : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hvol : 0 ≤ isoVol cert γstar CSig F.β m n B ϱ := by
    rw [div_eq_mul_inv] at hdiv
    exact nonneg_of_mul_nonneg_left hdiv (inv_pos.mpr hBr)
  have hmode : ∀ i j, Muon.Volatility.modeVij cert γstar CSig F Sp ϱ i j =
      isoVol cert γstar CSig F.β m n B ϱ / ((m : ℝ) * (n : ℝ)) := by
    intro i j
    unfold Muon.Volatility.modeVij
    rw [hz]
    simp [hμ, hlam]
    field_simp
  have hrec := Muon.Volatility.prop_app_vol_half_recovery cert γstar CSig F Sp
    hSize hCSig hIso.1 ϱ hϱ0
  have hrow : ∀ i, Muon.Volatility.rowVBar cert γstar CSig F.β B Sp.μ Sp.lam i ϱ ϱ =
      isoVol cert γstar CSig F.β m n B ϱ / (m : ℝ) := by
    intro i
    let j : Fin n := ⟨0, hn⟩
    have h := hrec.2.1 i j
    rw [hmode i j] at h
    have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp at h ⊢
    nlinarith
  exact ⟨hvol, hmode, hrow, hz⟩

private lemma bridge_vol_repl_lag {m n B : ℕ} (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C)
    (hSize : Muon.Volatility.SizeFin F.C B γstar CSig) (hCSig : 1 ≤ CSig)
    (ℓ q : ℕ) (ϱ : ℝ) (hω : Muon.Volatility.IsOddBddLip (Muon.Volatility.omegaF ϱ)) :
    Muon.Volatility.lagResp cert γstar CSig F.β ℓ ((q + 1) * B)
      (Muon.Volatility.replVec (q + 1) Sp.μ)
      (Muon.Volatility.replVec (q + 1) Sp.lam)
      (Muon.Volatility.replVec (q + 1) (fun _ : Fin m => 1))
      (Muon.Volatility.replVec (q + 1) (fun _ : Fin n => 1))
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
      Muon.Volatility.lagResp cert γstar CSig F.β ℓ B Sp.μ Sp.lam
        (fun _ : Fin m => 1) (fun _ : Fin n => 1)
        (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
  exact (Muon.Volatility.thm_app_vol_lag_kernel_bilinear_bound_replication
    cert γstar CSig (m := m) (n := n) (B := B) F Sp hSize hCSig ℓ
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) hω hω).2.2.2.2.2
      (q + 1) (Nat.succ_pos q) (fun _ : Fin m => 1) (fun _ : Fin n => 1)

private lemma bridge_vol_lag_bound_one {m n B : ℕ} (cert : Muon.External.GaussianOpNorm)
    (γstar CSig : ℝ) (F : Muon.Setup.FrozenParams m n B)
    (Sp : Muon.Setup.SpectralData F.C) (hSize : Muon.Volatility.SizeFin F.C B γstar CSig)
    (hCSig : 1 ≤ CSig) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    {ϱlo ϱhi ϱ : ℝ} (hI : 0 < ϱlo ∧ ϱlo ≤ ϱhi) (hϱI : ϱ ∈ Icc ϱlo ϱhi)
    (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    |Muon.Volatility.lagResp cert γstar CSig F.β ℓ B
        (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
        (fun _ : Fin m => (1 : ℝ)) (fun _ : Fin n => (1 : ℝ))
        (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)| ≤
      Muon.Dynamics.kStar 1 γstar ϱlo * F.β ^ ℓ := by
  obtain ⟨hm, hn⟩ := bridge_drift_dims_pos F
  obtain ⟨hμ, hlam⟩ := bridge_drift_eigenvalues F Sp hIso
  have hOne : Muon.Volatility.SizeFin F.C B γstar 1 := by
    refine ⟨hSize.1, ?_, ?_⟩
    · rw [hIso.2]
      exact bridge_vol_opNorm_one _
    · rw [hIso.1]
      exact bridge_vol_opNorm_one _
  let rF : ∀ q : ℕ, Muon.Setup.FrozenParams ((q + 1) * m) ((q + 1) * n) ((q + 1) * B) :=
    fun q => Muon.Volatility.def_app_vol_replication F Sp (q + 1) (Nat.succ_pos q)
      (Muon.Volatility.def_app_vol_replication_vi F.C Sp (q + 1) hm hn (Nat.succ_pos q))
  let rSp : ∀ q : ℕ, Muon.Setup.SpectralData (rF q).C := fun q =>
    { uOut := 1
      vIn := 1
      μ := fun _ => 1
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro i
        simp [rF, Muon.Volatility.def_app_vol_replication, Muon.Volatility.replCov,
          hIso.2, Muon.Volatility.replMat, Muon.Volatility.repKron]
      eigIn := by
        intro i
        simp [rF, Muon.Volatility.def_app_vol_replication, Muon.Volatility.replCov,
          hIso.1, Muon.Volatility.replMat, Muon.Volatility.repKron] }
  have hRat : ∀ q : ℕ,
      (((((q + 1) * m : ℕ)) : ℝ) / ((((q + 1) * B : ℕ)) : ℝ) = (m : ℝ) / (B : ℝ)) ∧
      (((((q + 1) * n : ℕ)) : ℝ) / ((((q + 1) * B : ℕ)) : ℝ) = (n : ℝ) / (B : ℝ)) :=
    fun q => Muon.Volatility.def_app_vol_replication_v (q + 1) (Nat.succ_pos q) F.hB
  have hSeq : Muon.Volatility.SizeSeq (B := fun q => (q + 1) * B)
      (fun q => (rF q).C) γstar CSig ((m : ℝ) / B) ((n : ℝ) / B) := by
    refine ⟨fun q => ?_, ?_, ?_, ?_⟩
    · exact Muon.Volatility.def_app_vol_replication_iv F.C γstar CSig hSize
        (q + 1) (Nat.succ_pos q)
    · exact tendsto_atTop_mono (fun q : ℕ => le_trans (Nat.le_succ q)
        (Nat.le_mul_of_pos_right (q + 1) F.hB)) tendsto_id
    · exact Tendsto.congr (fun q => ((hRat q).2).symm) tendsto_const_nhds
    · exact Tendsto.congr (fun q => ((hRat q).1).symm) tendsto_const_nhds
  have hrβall : ∀ q, (rF q).β = F.β := fun _ => rfl
  have hclo := (Muon.Volatility.thm_app_vol_lag_kernel_closure_indep cert γstar CSig
    ((m : ℝ) / B) ((n : ℝ) / B) hCSig ϱlo ϱhi hI
    (fun q => (q + 1) * m) (fun q => (q + 1) * n) (fun q => (q + 1) * B)
    rF rSp hSeq F.β F.hβ.2 (fun q => (hrβall q).le) ℓ {1} isCompact_singleton
    (by intro x hx; rcases hx with rfl; norm_num)).2
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨q, hq⟩ := (hclo ε hε).exists
  have hrβ : (rF q).β = F.β := hrβall q
  have hrμ : (rSp q).μ = Muon.Volatility.replVec (q + 1) Sp.μ := by
    funext i
    simp only [rSp, Muon.Volatility.replVec, hμ]
  have hrlam : (rSp q).lam = Muon.Volatility.replVec (q + 1) Sp.lam := by
    funext i
    simp only [rSp, Muon.Volatility.replVec, hlam]
  have hreplM : Muon.Volatility.replVec (q + 1) (fun _ : Fin m => (1 : ℝ)) =
      (fun _ : Fin ((q + 1) * m) => 1) := by
    funext i
    rfl
  have hreplN : Muon.Volatility.replVec (q + 1) (fun _ : Fin n => (1 : ℝ)) =
      (fun _ : Fin ((q + 1) * n) => 1) := by
    funext i
    rfl
  have hω : Muon.Volatility.IsOddBddLip (Muon.Volatility.omegaF ϱ) :=
    (Muon.Volatility.lem_app_vol_sharp_ii
      (hI.1.trans_le hϱI.1) (hI.1.trans_le hϱI.1)).2.1
  have hw : Muon.Volatility.lagResp cert γstar CSig F.β ℓ ((q + 1) * B)
      (Muon.Volatility.replVec (q + 1) Sp.μ)
      (Muon.Volatility.replVec (q + 1) Sp.lam)
      (Muon.Volatility.replVec (q + 1) (fun _ : Fin m => 1))
      (Muon.Volatility.replVec (q + 1) (fun _ : Fin n => 1))
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) =
      Muon.Volatility.lagResp cert γstar CSig F.β ℓ B
        Sp.μ Sp.lam (fun _ : Fin m => 1) (fun _ : Fin n => 1)
        (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) := by
    exact bridge_vol_repl_lag (m := m) (n := n) (B := B)
      cert γstar CSig F Sp hSize hCSig ℓ q ϱ hω
  have key := hq 0 ϱ hϱI ϱ hϱI
    (Muon.Volatility.replVec (q + 1) (fun _ : Fin m => (1 : ℝ)))
    (Muon.Volatility.replVec (q + 1) (fun _ : Fin n => (1 : ℝ)))
    (1 : Mat ((q + 1) * m) ((q + 1) * m)) (1 : Mat ((q + 1) * n) ((q + 1) * n))
    (by simp [rSp, hreplM]) (by simp [rSp, hreplN])
    (bridge_vol_opNorm_one _) (bridge_vol_opNorm_one _)
  rw [hrβ, hrμ, hrlam, hw, funext hμ, funext hlam] at key
  have hOneQ : Muon.Volatility.SizeFin (rF q).C ((q + 1) * B) γstar 1 :=
    Muon.Volatility.def_app_vol_replication_iv F.C γstar 1 hOne
      (q + 1) (Nat.succ_pos q)
  let SG := (Muon.Setup.frozenSamples_nonempty ((q + 1) * m) ((q + 1) * n)
    ((q + 1) * B)).some
  have hb := (Muon.Volatility.thm_app_vol_lag_reduction_ii_indep (rF q) SG
    γstar 1 ϱlo ϱhi hOneQ (le_refl 1) hI (1 : Mat ((q + 1) * m) ((q + 1) * m))
    (1 : Mat ((q + 1) * n) ((q + 1) * n)) (by simp) (by simp)
    (bridge_vol_opNorm_one _) (bridge_vol_opNorm_one _) ϱ ϱ hϱI hϱI 0).2 ℓ hℓ
  have hb' :
      |((((q + 1) * B : ℕ) : ℝ))⁻¹ * ∫ ω, Matrix.trace
        ((1 : Mat ((q + 1) * m) ((q + 1) * m)) *
          Muon.Volatility.indepUpd (rF q) ϱ ω 0 *
          (1 : Mat ((q + 1) * n) ((q + 1) * n)) *
          (Muon.Volatility.indepUpd (rF q) ϱ ω (0 + (ℓ : ℤ)))ᵀ)
        ∂(Muon.Volatility.indepSpaceLaw ((q + 1) * m) ((q + 1) * n) ((q + 1) * B))| ≤
        Muon.Dynamics.kStar 1 γstar ϱlo * F.β ^ ℓ := by
    rw [hrβ] at hb
    exact hb
  have habs := abs_sub_abs_le_abs_sub
    (Muon.Volatility.lagResp cert γstar CSig F.β ℓ B
      (fun _ : Fin m => 1) (fun _ : Fin n => 1) (fun _ => 1) (fun _ => 1)
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ))
    (((((q + 1) * B : ℕ) : ℝ))⁻¹ * ∫ ω, Matrix.trace
      ((1 : Mat ((q + 1) * m) ((q + 1) * m)) *
        Muon.Volatility.indepUpd (rF q) ϱ ω 0 *
        (1 : Mat ((q + 1) * n) ((q + 1) * n)) *
        (Muon.Volatility.indepUpd (rF q) ϱ ω (0 + (ℓ : ℤ)))ᵀ)
      ∂(Muon.Volatility.indepSpaceLaw ((q + 1) * m) ((q + 1) * n) ((q + 1) * B)))
  rw [abs_sub_comm] at habs
  exact (show
    |Muon.Volatility.lagResp cert γstar CSig F.β ℓ B
      (fun _ : Fin m => 1) (fun _ : Fin n => 1) (fun _ => 1) (fun _ => 1)
      (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)| ≤
      Muon.Dynamics.kStar 1 γstar ϱlo * F.β ^ ℓ + ε by linarith)

/-- `thm:app-iso-volatility`, snapshot `cr-2026-10-23`. Declaration of record. Work under `assum:app-setup-regime`
with `Σ_in = Σ_out = Id` (`hIso`), `I = [R.ϱlo, R.ϱhi]`, the frozen update `S_t(ϱ) = Muon.Setup.frozenUpd`.
(i) same time: the row, column and total bounds with `ψ`, the sequences `e_B`, `e'_B` (existence, `→ 0`, as the
sequences of `thm:app-vol-half-same`), and the integrability of the expectations. (ii) integrated: `𝔳_iso(ϱ)`
(`isoVol`), its mode identities with D's `modeVij`, `rowVBar`, `measureZeta`, the lag expansion with
`Muon.Dynamics.kStar` at `C_Σ = 1`, and `𝔳_iso = Bψ` at `β = 0`. (iv) the actual coefficient `Γ(ϱ,ϱ)` of D's
`weightedGamma` converges to `𝔳_iso(ϱ)/B` uniformly on `I`. LaTeX, verbatim:

\begin{theorem}[Isotropic volatility]\label{thm:app-iso-volatility}
Work under \cref{assum:app-setup-regime} with $\Sigmain=\Id_{\Nin}$ and
$\Sigmaout=\Id_{\Nout}$, let $I=[\ridge_-,\ridge_+]$, let ${\mathsf S}_t(\ridge)=\Qridge\ridge(\Mt)$
be the frozen update of \cref{eqn:app-vol-U}, and let $e_B\to0$ be the
sequence of \cref{thm:app-vol-half-same}.
\begin{enumerate}[label=(\roman*)]
\item (Same time.) For every row $i$ and every column $j$,
\begin{equation}\label{eqn:app-iso-vol-rows}
\sup_{\ridge\in I}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\frac{\psi(\ridge)}{\gout}\Big|\le\ridge_+e_B,\qquad
\sup_{\ridge\in I}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\frac{\psi(\ridge)}{\gin}\Big|\le\ridge_+e_B',
\end{equation}
where $e_B'\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)}\to0$, and
\begin{equation}\label{eqn:app-iso-vol-total}
\EE\sup_{\ridge\in I}\Big|\frac1B\norm{{\mathsf S}_t(\ridge)}_\F^2-\psi(\ridge)\Big|^2\longrightarrow0 .
\end{equation}
\item (Integrated.) There is a number $\mathfrak v_{\mathrm{iso}}(\ridge)\ge0$,
depending on the dimension, $\bmom$ and $\ridge$, such that the mode
coefficients of \cref{prop:app-vol-disintegration} and the row coefficients
of \cref{thm:app-vol-mode-kernels} are
\begin{equation}\label{eqn:app-iso-vol-modes}
\mathfrak v_{ij}(\ridge)=\frac{\mathfrak v_{\mathrm{iso}}(\ridge)}{\Nout\Nin},\qquad
\mathfrak v_i(\ridge)=\frac{\mathfrak v_{\mathrm{iso}}(\ridge)}{\Nout},\qquad
\zeta_\ridge=\frac{\mathfrak v_{\mathrm{iso}}(\ridge)}{B}\,\delta_{(1,1)} ,
\end{equation}
for all $i,j$, and $\mathfrak v_{\mathrm{iso}}(\ridge)=\sum_{i,j}\mathfrak v_{ij}(\ridge)=B\,\overline\Gamma(\ridge,\ridge)$
with $\overline\Gamma=\overline\Gamma[\Id_{\Nout},\Id_{\Nin}]$ of \cref{eqn:app-vol-Gammabar}.
\item (Lag expansion.) With the deterministic lag covariances
$\overline C_\ell=\overline C_\ell[\Id_{\Nout},\Id_{\Nin}]$ of \cref{thm:app-vol-integrated},
\begin{equation}\label{eqn:app-iso-vol-lags}
\mathfrak v_{\mathrm{iso}}(\ridge)=B\,\psi(\ridge)+2B\sum_{\ell\ge1}\overline C_\ell(\ridge,\ridge),\qquad
\abs{\overline C_\ell(\ridge,\ridge)}\le\mathsf K_\star\bmom^\ell ,
\end{equation}
with $\mathsf K_\star$ of \cref{eqn:app-vol-K} at $C_\Sigma=1$. At $\bmom=0$,
\begin{equation}\label{eqn:app-iso-vol-nomomentum}
\mathfrak v_{\mathrm{iso}}(\ridge)=B\,\psi(\ridge)=B\,\Phi\big(q(-\ridge)\big)=B\big(\gout-\ridge\,\sigma(-\ridge)\big).
\end{equation}
\item (Actual coefficient.) The actual integrated covariance $\Gamma=\Gamma[\Id_{\Nout},\Id_{\Nin}]$
of \cref{eqn:app-vol-Gamma} satisfies
$\sup_{\ridge\in I}\abs{\Gamma(\ridge,\ridge)-\mathfrak v_{\mathrm{iso}}(\ridge)/B}\to0$.
\end{enumerate}
\end{theorem}
-/
theorem thm_app_iso_volatility (cert : Muon.External.GaussianOpNorm)
    (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (Sp : ∀ k, Muon.Setup.SpectralData (R.F k).C)
    (hIso : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1) :
    -- (i) same time: rows and columns, with the explicit dominating sup `e_B`, `e'_B` (universal form),
    -- their existence with limit 0, and the total.
    (∀ eB : ℕ → ℝ,
      (∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi, Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ eB k) →
      ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, ∀ i : Fin (R.m k),
        Integrable (fun ω => dotProduct ((Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω)ᵀ *ᵥ (Sp k).u i)
          ((Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω)ᵀ *ᵥ (Sp k).u i)) (P k) ∧
        |(∫ ω, dotProduct ((Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω)ᵀ *ᵥ (Sp k).u i)
            ((Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω)ᵀ *ᵥ (Sp k).u i) ∂(P k)) -
          psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
            ((R.m k : ℝ) / (R.B k : ℝ))| ≤ R.ϱhi * eB k) ∧
    (∃ eB : ℕ → ℝ, Tendsto eB atTop (𝓝 0) ∧
      ∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi, Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ eB k) ∧
    (∀ eB' : ℕ → ℝ,
      (∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi, Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ eB' k) →
      ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, ∀ j : Fin (R.n k),
        Integrable (fun ω => dotProduct (Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω *ᵥ (Sp k).v j)
          (Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω *ᵥ (Sp k).v j)) (P k) ∧
        |(∫ ω, dotProduct (Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω *ᵥ (Sp k).v j)
            (Muon.Setup.frozenUpd (R.F k) (S k) ϱ t ω *ᵥ (Sp k).v j) ∂(P k)) -
          psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ /
            ((R.n k : ℝ) / (R.B k : ℝ))| ≤ R.ϱhi * eB' k) ∧
    (∃ eB' : ℕ → ℝ, Tendsto eB' atTop (𝓝 0) ∧
      ∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi, Muon.opNorm (Muon.DetEquiv.expResT (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rtbar (Muon.DetEquiv.Fw (Muon.emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ eB' k) ∧
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((Muon.Volatility.sameTimeZ (R.F k) (S k) ϱ t ω -
          psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) ∧
    -- (ii) integrated: the mode, row and zeta identities at `𝔳_iso(ϱ)`, and nonnegativity
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      0 ≤ isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ ∧
      (∀ i j, Muon.Volatility.modeVij cert R.γstar R.CSig (R.F k) (Sp k) ϱ i j =
          isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ / ((R.m k : ℝ) * (R.n k : ℝ))) ∧
      (∀ i, Muon.Volatility.rowVBar cert R.γstar R.CSig R.β (R.B k) (Sp k).μ (Sp k).lam i ϱ ϱ =
          isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ / (R.m k : ℝ)) ∧
      Muon.Volatility.measureZeta cert R.γstar R.CSig (R.F k) (Sp k) ϱ =
          Finsupp.single ((1 : ℝ), (1 : ℝ)) (isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ / (R.B k : ℝ))) ∧
    -- (iii) lag expansion, with the absolute convergence and the bound `K⋆ β^ℓ` at `C_Σ = 1`
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ =
          (R.B k : ℝ) * psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ +
            2 * (R.B k : ℝ) * ∑' ℓ : ℕ, Muon.Volatility.lagResp cert R.γstar R.CSig R.β (ℓ + 1) (R.B k)
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ) ∧
      Summable (fun ℓ : ℕ => |Muon.Volatility.lagResp cert R.γstar R.CSig R.β (ℓ + 1) (R.B k)
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)|) ∧
      (∀ ℓ : ℕ, 1 ≤ ℓ → |Muon.Volatility.lagResp cert R.γstar R.CSig R.β ℓ (R.B k)
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
              (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)| ≤
            Muon.Dynamics.kStar 1 R.γstar R.ϱlo * R.β ^ ℓ)) ∧
    -- (iii, zero momentum) `𝔳_iso = B ψ = B Φ(q(−ϱ)) = B(γout − ϱ σ(−ϱ))`
    (R.β = 0 → ∀ k, 0 < R.m k → 0 < R.n k → ∀ ϱ ∈ Icc R.ϱlo R.ϱhi, 0 < ϱ →
      isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ =
          (R.B k : ℝ) * psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ ∧
      isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ =
          (R.B k : ℝ) * isoPhi (qIso 0 ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) ∧
      (∀ ν ν' : FiniteMeasure ℝ,
        (ν : Measure ℝ) = isoSpecMeasure ((R.m k : ℝ) / (R.B k : ℝ)) →
        (ν' : Measure ℝ) = isoSpecMeasure ((R.n k : ℝ) / (R.B k : ℝ)) →
        ∀ x : ℝ × ℝ × ℝ × ℝ, Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW 0)) ν ν' ϱ x →
          isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ =
            (R.B k : ℝ) * ((R.m k : ℝ) / (R.B k : ℝ) - ϱ * x.1))) ∧
    -- (iv) actual coefficient
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      |Muon.Volatility.weightedGamma (R.F k) (S k) t ϱ ϱ -
        isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ / (R.B k : ℝ)| ≤ ε) := by
  obtain ⟨e, he, heb⟩ := bridge_vol_errors R P S t hIso
  refine ⟨?_, ⟨e, he, ?_⟩, ?_, ⟨e, he, ?_⟩, bridge_vol_total R P S t Sp hIso,
    ?_, ?_, ?_, ?_⟩
  · intro eB heB k ϱ hϱI i
    have h := bridge_vol_row_bound (R.F k) (S k) (Sp k) (hIso k) t R.hϱ.1
      (fun s hs => by simpa [R.hβ k] using heB k s hs) hϱI i
    simpa [R.hβ k] using h
  · intro k s hs
    exact (heb k s hs).1
  · intro eB heB k ϱ hϱI j
    have h := bridge_vol_col_bound (R.F k) (S k) (Sp k) (hIso k) t R.hϱ.1
      (fun s hs => by simpa [R.hβ k] using heB k s hs) hϱI j
    simpa [R.hβ k] using h
  · intro k s hs
    exact (heb k s hs).2
  · intro k ϱ hϱI
    have h := bridge_vol_integrated cert R.γstar R.CSig (R.F k) (Sp k)
      ⟨R.dims k, R.normOut k, R.normIn k⟩ R.hC (hIso k) R.hϱ hϱI
    simpa [R.hβ k] using h
  · intro k ϱ hϱI
    have hϱ0 : 0 < ϱ := R.hϱ.1.trans_le hϱI.1
    have hU : (1 : Mat (R.m k) (R.m k)) =
        (Sp k).uOut * Matrix.diagonal (fun _ : Fin (R.m k) => (1 : ℝ)) * (Sp k).uOutᵀ := by
      simpa using (mul_eq_one_comm.mp (Sp k).huOut).symm
    have hV : (1 : Mat (R.n k) (R.n k)) =
        (Sp k).vIn * Matrix.diagonal (fun _ : Fin (R.n k) => (1 : ℝ)) * (Sp k).vInᵀ := by
      simpa using (mul_eq_one_comm.mp (Sp k).hvIn).symm
    have hSize : Muon.Volatility.SizeFin (R.F k).C (R.B k) R.γstar R.CSig :=
      ⟨R.dims k, R.normOut k, R.normIn k⟩
    have hiii := Muon.Volatility.thm_app_vol_integrated_iii cert R.γstar R.CSig
      (R.F k) (Sp k) hSize R.hC (1 : Mat (R.m k) (R.m k))
      (1 : Mat (R.n k) (R.n k)) (fun _ => 1) (fun _ => 1) hU hV
      R.ϱlo R.ϱhi R.hϱ ϱ ϱ hϱI hϱI
    let a : ℕ → ℝ := fun ℓ => Muon.Volatility.lagResp cert R.γstar R.CSig R.β (ℓ + 1)
      (R.B k) (fun _ : Fin (R.m k) => (1 : ℝ)) (fun _ : Fin (R.n k) => (1 : ℝ))
      (fun _ => 1) (fun _ => 1) (Muon.Volatility.omegaF ϱ) (Muon.Volatility.omegaF ϱ)
    have hs : Summable (fun ℓ : ℕ => |a ℓ + a ℓ|) := by
      simpa [a, R.hβ k, funext (bridge_drift_eigenvalues (R.F k) (Sp k) (hIso k)).1,
        funext (bridge_drift_eigenvalues (R.F k) (Sp k) (hIso k)).2] using hiii.1
    have hsa : Summable (fun ℓ : ℕ => |a ℓ|) := by
      have hm := hs.mul_left (1 / 2 : ℝ)
      refine hm.congr fun ℓ => ?_
      rw [show a ℓ + a ℓ = 2 * a ℓ by ring, abs_mul]
      rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    have hzero := (Muon.Volatility.thm_app_vol_integrated_v cert R Ω P S Sp).2 k
      (hIso k).1 (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k))
      rfl rfl ϱ hϱI
    obtain ⟨hμ, hlam⟩ := bridge_drift_eigenvalues (R.F k) (Sp k) (hIso k)
    have hzbar := bridge_vol_zbar (R.F k) (Sp k) (hIso k) hϱ0
    rw [funext hμ, R.hβ k] at hzbar
    rw [funext hμ, funext hlam, R.hβ k, hzbar] at hzero
    have hsum : tsum (fun q : ℕ => a q + a q) = 2 * tsum a := by
      rw [← tsum_mul_left]
      apply tsum_congr
      intro ℓ
      ring
    refine ⟨?_, ?_, ?_⟩
    · unfold isoVol Muon.Volatility.lagGammaBar
      rw [hzero]
      change (R.B k : ℝ) * (psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ))
        ((R.m k : ℝ) / (R.B k : ℝ)) ϱ + tsum (fun q : ℕ => a q + a q)) = _
      rw [hsum]
      ring
    · simpa [a] using hsa
    · intro ℓ hℓ
      have h := bridge_vol_lag_bound_one cert R.γstar R.CSig (R.F k) (Sp k)
        hSize R.hC (hIso k) R.hϱ hϱI ℓ hℓ
      simpa [R.hβ k] using h
  · intro hβ0 k hm hn ϱ hϱI hϱ0
    have hv := bridgeR_isoVol_zero cert R.γstar R.CSig (R.F k).hB hm hn
      (R.dims k) R.hC hϱ0
    have hv' : isoVol cert R.γstar R.CSig R.β (R.m k) (R.n k) (R.B k) ϱ =
        (R.B k : ℝ) * psiIso 0 ((R.n k : ℝ) / (R.B k : ℝ))
          ((R.m k : ℝ) / (R.B k : ℝ)) ϱ := by
      simpa [hβ0] using hv
    refine ⟨hv', ?_, ?_⟩
    · rw [hv', bridge_vol_psi_zero hm hn (R.F k).hB hϱ0]
    · intro ν ν' hν hν' x hx
      rw [hv', bridge_vol_psi_branch hm hn (R.F k).hB hϱ0 ν ν' hν hν' x hx]
  · intro ε hε
    have hv := (Muon.Volatility.thm_app_vol_integrated_v cert R Ω P S Sp).1 ε hε
    filter_upwards [hv] with k hk
    intro ϱ hϱI
    have h := hk t ϱ hϱI ϱ hϱI
    obtain ⟨hμ, hlam⟩ := bridge_drift_eigenvalues (R.F k) (Sp k) (hIso k)
    rw [R.hβ k, funext hμ, funext hlam] at h
    simpa [isoVol, (R.F k).hB.ne'] using h


end Muon.Isotropic
