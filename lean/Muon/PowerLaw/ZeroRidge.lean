import Muon.PowerLaw.VolMeso
import Muon.PowerLaw.VolKernel
import Muon.PowerLaw.BranchLink
import Muon.PowerLaw.Response
import Muon.PowerLaw.Weights
import Muon.PowerLaw.Participation
import Muon.PowerLaw.Continuum
import Muon.Volatility.LagKernel
import Muon.Volatility.HalfCandidates
import Muon.Volatility.OddSpectral
import Muon.Drift.Defs
import Muon.Foundations.Conventions

/-!
# Appendix G, work package L-G.13: volatility at zero ridge (interface draft)

Work package L-G.13 (interface draft). Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`:
`eqn:app-pl-Cil` (l.84–89, the displayed row coefficients), `lem:app-pl-two-ridge` (l.489–499),
`prop:app-pl-vol-zero` (l.573–594), `def:app-pl-coefficients` (l.705–713), `lem:app-pl-amplitude`
(l.723–731), `lem:app-pl-pieces` (l.1843–1845). Also the discharges of the part-form hypotheses
`volHBound`, `volHPSD`, `volHZero` of `Muon.PowerLaw.VolMeso` (card §5, notes of L-G.13).
Card: `sections/06-power-law/CARD.md` §2, §3, §5 (row L-G.13), §6 #1, #3, #5, #15, #16.

Reused, not redefined: `gammaOf`, `partMN`, `sN`, `dZero`, `dPart`, `Qm`, `Efun`, `emaW`, `sPow`, `Fw`
(Participation, Weights, Conventions, DetEquiv); `lagRowBar`, `lagResp`, `lagRespCut`, `rowVBar`,
`volraw`, `iotaF`, `omegaF` (D: `Muon.Volatility`); `Muon.Drift.kernel`; `CbarPart`, `vPart`, `vIJ`,
`lagTerm`, `lagIntegrand`, `deltaN`, `Wpart`, `TNpart` (`Muon.PowerLaw.VolKernel`); `volHBound`,
`volHPSD`, `volHZero` (`Muon.PowerLaw.VolMeso`); `assum_app_pl_regime`, `plSpec` (Continuum);
`prop_app_pl_response_*`, `respRHS` (L-G.10); `prop_app_pl_branch_iii_volraw`,
`prop_app_pl_drift_zero_ii_kernel`, `prop_app_pl_drift_zero_i_volraw` (L-G.12).

Encoding decisions:
* Momentum: `0 < β < 1` throughout. The source's standing setup fixes `β ∈ (0,1)` (l.47). The
  participation-form objects `Qm`, `dZero`, `CbarPart`, `vPart` are junk at `β = 0` for `m ≥ 1`
  (`r_0 < 1`), so `β = 0` is not claimed here. `L-G.14` treats `β = 0` on its own (Q5).
* Spectrum: `μ : Fin N → ℝ`, antitone and positive (standing, l.40–46). `γ = gammaOf N B` with `B > 0`.
* Row coefficients. `Σ_in = Id_N` is encoded by input eigenvalues `fun _ => 1` and input test `fun _ => 1`;
  `u_i ⊗ u_i` by `Pi.single i 1`. `C̄_{i,ℓ}(ϱ) := C̄_{i,ℓ}(ϱ,ϱ)` (`eqn:app-vol-rows`) is `lagRowBar … ϱ ϱ`,
  `𝔳_i(ϱ)` is `rowVBar … ϱ ϱ`. Constants `γ⋆`, `C_Σ` enter D's objects only through the admissibility
  hypotheses `γ⋆ ≥ γ`, `C_Σ ≥ max(μ_i, 1)` (as in L-G.10), quantified over all admissible values.
* Limits as ϱ↓0 are `limUnder (𝓝[>] 0)`, so every statement that uses a row coefficient at `ϱ > 0`
  carries the existence of its joint limit as an explicit conjunct: `plLagExists` (the content of D's
  `thm:app-vol-lag-kernel`) applied to `omegaF ϱ` (`plRowExists`) or `iotaF s` (`plKerExists`).
  No hypothesis asserts existence.
* Zero-ridge objects: `cbarZero` (`C̄_{i,ℓ}(0)`) and `vZero` (`𝔳_i(0) = 1 + 2∑_{ℓ≥1} C̄_{i,ℓ}(0)`) are the
  definitions of `def:app-pl-coefficients`. `dZero` is `𝔡_i(0)`.
* Finite constants `z_1`, `F⋆`, `D_i`, `A_N` (`eqn:app-pl-finite-constants`, `eqn:app-pl-A`) are defined
  here (`plZ1`, `plFstar`, `plDcoef`, `plAN`) since no earlier module defines them; `E_i` of the
  proposition is `plEi`.
* Volatility at zero ridge is stated for `CbarPart` and `vIJ` only through the bridge
  `prop_app_pl_vol_zero_iii_b`; `vPart` is not identified with `vZero` here (card §2 helper).
* Hypotheses `volHBound`, `volHPSD`, `volHZero` are discharged by the three theorems at the end.
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open Muon.Volatility (lagRowBar lagResp lagRespCut rowVBar volraw iotaF omegaF)
open Muon.DetEquiv (Fw)

noncomputable section

namespace Muon.PowerLaw

/-! ## Helper predicates (existence of the D-limits) and finite constants -/

/-- Existence of the joint limit defining `lagResp` (D's `thm:app-vol-lag-kernel`): the truncated
responses `lagRespCut` converge as `J, R → ∞` (`atTop ×ˢ atTop`) to the value `lagResp`. Helper; it
is the content of the existence clause of `Muon.Volatility.thm_app_vol_lag_kernel_exists`. -/
def plLagExists (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {m n : ℕ} (β : ℝ) (ℓ B : ℕ)
    (μ : Fin m → ℝ) (lam : Fin n → ℝ) (Fd : Fin m → ℝ) (Gd : Fin n → ℝ) (f g : ℝ → ℝ) : Prop :=
  Tendsto (fun p : ℕ × ℝ => lagRespCut cert γstar CSig β ℓ p.1 p.2 B μ lam Fd Gd f g)
    (atTop ×ˢ atTop : Filter (ℕ × ℝ)) (𝓝 (lagResp cert γstar CSig β ℓ B μ lam Fd Gd f g))

/-- Existence of the row limits `lagRowBar … ϱ ϱ` for every lag and every `ϱ > 0` (`Σ_in = Id`,
`u_i ⊗ u_i`). Helper. -/
def plRowExists (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {N : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin N → ℝ) (i : Fin N) : Prop :=
  ∀ (ℓ : ℕ) (ϱ : ℝ), 0 < ϱ →
    plLagExists cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ)

/-- Existence of the lag responses with filters `ι_s`, `s > 0`, for the row test `u_i ⊗ u_i` and `Id`
(the integrand of `eqn:app-pl-Cil` and of `eqn:app-pl-vol-zero`). Helper. -/
def plKerExists (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {N : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin N → ℝ) (i : Fin N) : Prop :=
  ∀ (ℓ : ℕ) (s s' : ℝ), 0 < s → 0 < s' →
    plLagExists cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) (iotaF s) (iotaF s')

/-- `z_1 = s_N(m_N(1))` (`eqn:app-pl-finite-constants`, `section.tex` l.363–370). -/
def plZ1 (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) : ℝ :=
  sN β B μ (partMN B μ 1)

/-- `F⋆ = F_β(Q_γ)` (`eqn:app-pl-finite-constants`). -/
def plFstar (β : ℝ) (B N : ℕ) : ℝ :=
  Fw (emaW β) (Qm β (gammaOf N B))

/-- `D_i = μ_i⁻¹ √((1+μ_1)/(γ F⋆))` (`eqn:app-pl-finite-constants`), with `μ_1 = μ ⟨0, hN⟩`. -/
def plDcoef (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N) (i : Fin N) : ℝ :=
  (μ i)⁻¹ * Real.sqrt ((1 + μ ⟨0, hN⟩) / (gammaOf N B * plFstar β B N))

/-- `A_N = (2γ 𝔰_2 ∑_j μ_j)^{1/2}` with `𝔰_2 = sPow β 2` (`eqn:app-pl-A`, l.486). -/
def plAN (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) : ℝ :=
  Real.sqrt (2 * gammaOf N B * sPow β 2 * ∑ j, μ j)

/-- `E_i = A_N z̄^{-1/2} + 2 √D_i z̄^{1/4}` of `prop:app-pl-vol-zero`(i) (`section.tex` l.575). Helper. -/
def plEi (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (hN : 0 < N) (i : Fin N) (zbar : ℝ) : ℝ :=
  plAN β B μ * zbar ^ (-(1 : ℝ) / 2) + 2 * Real.sqrt (plDcoef β B μ hN i) * zbar ^ ((1 : ℝ) / 4)

/-! ## Zero-ridge coefficients (`def:app-pl-coefficients`) -/

/-- `C̄_{i,ℓ}(0) = lim_{ϱ↓0} C̄_{i,ℓ}(ϱ)` (`def:app-pl-coefficients`, `section.tex` l.705–713). The limit
is the one of `prop:app-pl-vol-zero`(i); the value is junk without it. Constants `γ⋆`, `C_Σ` are those of
the row coefficient `lagRowBar`. -/
def cbarZero (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {N : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin N → ℝ) (i : Fin N) (ℓ : ℕ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ϱ : ℝ => lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)

/-- `𝔳_i(0) = 1 + 2 ∑_{ℓ≥1} C̄_{i,ℓ}(0)` (`def:app-pl-coefficients`, `prop:app-pl-vol-zero`(ii)). -/
def vZero (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ) {N : ℕ} (β : ℝ) (B : ℕ)
    (μ : Fin N → ℝ) (i : Fin N) : ℝ :=
  1 + 2 * ∑' ℓ : ℕ, cbarZero cert γstar CSig β B μ i (ℓ + 1)

private lemma zr_diagonal_bound {N : ℕ} (d : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : opNorm (Matrix.diagonal d) ≤ C := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by
    simpa [Real.norm_eq_abs] using hd i

private lemma zr_setup {N B : ℕ} (hB : 0 < B) (μ : Fin N → ℝ)
    (hpos : ∀ i, 0 < μ i) {β γstar CSig : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    ∃ (Fp : Muon.Setup.FrozenParams N N B) (S : Muon.Setup.SpectralData Fp.C),
      Fp.β = β ∧ S.μ = μ ∧ S.lam = (fun _ => (1 : ℝ)) ∧
      Muon.Volatility.SizeFin Fp.C B γstar CSig := by
  classical
  let C : Covariances N N :=
    { Sout := Matrix.diagonal μ
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun j => (hpos j).le)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams N N B :=
    { C := C
      A := Pi.single i (Pi.single i 1)
      hA := by simp [fro, Pi.single_apply, ite_apply]
      β := β
      hβ := ⟨hβ0.le, hβ1⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := μ
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro j; ext k
        by_cases h : k = j <;> simp [Fp, C, Matrix.mulVec, dotProduct,
          Matrix.diagonal, Matrix.one_apply, h]
      eigIn := by intro j; simp [Fp, C] }
  refine ⟨Fp, S, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · simpa [gammaOf, div_le_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)] using hγ
  · exact zr_diagonal_bound μ CSig (by linarith) (fun j => by
      rw [abs_of_pos (hpos j)]; exact hμC j)
  · exact zr_diagonal_bound (fun _ => 1) CSig (by linarith) (fun _ => by simpa using hC1)

/-! ## The row coefficients as a function of the ridge (`eqn:app-pl-Cil`) -/

/-- `eqn:app-pl-Cil`, first display (`C̄_{i,ℓ}(ϱ)` as the limit of the square integrals of the row
kernel), snapshot `cr-2026-10-23`. Declaration of record, part (i). The integrand of `eqn:app-pl-rowkernel`
is `B · lagResp … (ι_{ϱ+x²}) (ι_{ϱ+y²})`. Existence of the limits is part of the statement
(`plRowExists`, `plKerExists`); integrability on `[0,T]²` for `T ≥ 1` is `thm:app-vol-integrated`(i) of D.
LaTeX, verbatim from `section.tex`:

\begin{equation}\label{eqn:app-pl-Cil}
\overline C_{i,\ell}(\ridge)=\lim_{T\to\infty}\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_{i,\ell}(\ridge+x^2,\ridge+y^2)\,\dif x\,\dif y,
\qquad
\mathfrak v_i(\ridge)=\overline C_{i,0}(\ridge)+2\sum_{\ell\ge1}\overline C_{i,\ell}(\ridge).
\end{equation}
-/
theorem eqn_app_pl_Cil_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    plRowExists cert γstar CSig β B μ i ∧ plKerExists cert γstar CSig β B μ i ∧
    (∀ T : ℝ, 1 ≤ T →
      IntegrableOn (fun p : ℝ × ℝ => (B : ℝ) * lagResp cert γstar CSig β ℓ B μ
          (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (iotaF (ϱ + p.1 ^ 2)) (iotaF (ϱ + p.2 ^ 2)))
        (Icc 0 T ×ˢ Icc 0 T)) ∧
    Tendsto (fun T : ℝ => (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
        (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)))
      atTop (𝓝 (lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)) := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS⟩ := zr_setup hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  let Fm := S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * (Matrix.transpose S.uOut)
  let Gm := S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * (Matrix.transpose S.vIn)
  have hex (k : ℕ) (f g : ℝ → ℝ) (hf : Muon.Volatility.IsOddBddLip f)
      (hg : Muon.Volatility.IsOddBddLip g) :
      plLagExists cert γstar CSig β k B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g := by
    simpa only [plLagExists, hβ, hμ, hlam] using
      Muon.Volatility.thm_app_vol_lag_kernel_exists cert γstar CSig Fp S hS hC1 k
        Fm Gm (Pi.single i 1) (fun _ => 1) rfl rfl f g hf hg
  have hsq (T : ℝ) (hT : 1 ≤ T) :=
    Muon.Volatility.thm_app_vol_integrated_i cert γstar CSig Fp S hS hC1 ℓ T hT
      Fm Gm (Pi.single i 1) (fun _ => 1) rfl rfl ϱ ϱ hϱ hϱ
  simp only [hβ, hμ, hlam] at hsq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k r hr
    exact hex k _ _ (Muon.Volatility.lem_app_vol_sharp_ii hr hr).2.1
      (Muon.Volatility.lem_app_vol_sharp_ii hr hr).2.1
  · intro k s t hs ht
    exact hex k _ _ (Muon.Volatility.lem_app_vol_sharp_ii hs hs).1
      (Muon.Volatility.lem_app_vol_sharp_ii ht ht).1
  · intro T hT
    exact (hsq T hT).1.const_mul (B : ℝ)
  · have hlim : Tendsto (fun T : ℝ => (4 / Real.pi ^ 2) *
        (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
            (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
            (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2)))) atTop
        (𝓝 (lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (g := fun T : ℝ =>
        4 * CSig * (γstar * Real.sqrt γstar) * opNorm Fm * opNorm Gm / (Real.pi * T))
        (Eventually.of_forall fun T => norm_nonneg _) ?_ ?_
      · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T hT
        simpa only [Real.norm_eq_abs, abs_sub_comm] using (hsq T hT).2
      · simpa only [div_mul_eq_div_div, id_eq] using
          (tendsto_const_nhds (x :=
            4 * CSig * (γstar * Real.sqrt γstar) * opNorm Fm * opNorm Gm / Real.pi)).div_atTop
              (tendsto_id : Tendsto (fun T : ℝ => T) atTop atTop)
    convert hlim.const_mul (B : ℝ) using 1
    · funext T
      simp only [intervalIntegral.integral_const_mul]
      ring
    · rfl

/-- `eqn:app-pl-Cil`, second display (`𝔳_i(ϱ) = C̄_{i,0}(ϱ) + 2∑_{ℓ≥1} C̄_{i,ℓ}(ϱ)`), snapshot
`cr-2026-10-23`. Declaration of record, part (ii). The series is summable (conjunct). LaTeX, verbatim:

\begin{equation}\label{eqn:app-pl-Cil}
\overline C_{i,\ell}(\ridge)=\lim_{T\to\infty}\frac4{\pi^2}\int_0^T\!\!\int_0^T\mathfrak k_{i,\ell}(\ridge+x^2,\ridge+y^2)\,\dif x\,\dif y,
\qquad
\mathfrak v_i(\ridge)=\overline C_{i,0}(\ridge)+2\sum_{\ell\ge1}\overline C_{i,\ell}(\ridge).
\end{equation}
-/
theorem eqn_app_pl_Cil_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    plRowExists cert γstar CSig β B μ i ∧
    Summable (fun ℓ : ℕ => lagRowBar cert γstar CSig β (ℓ + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) ∧
    rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ +
        2 * ∑' ℓ : ℕ, lagRowBar cert γstar CSig β (ℓ + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS⟩ := zr_setup hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  let Fm := S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * (Matrix.transpose S.uOut)
  let Gm := S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * (Matrix.transpose S.vIn)
  have habs := (Muon.Volatility.thm_app_vol_integrated_iii cert γstar CSig Fp S hS hC1
    Fm Gm (Pi.single i 1) (fun _ => 1) rfl rfl ϱ ϱ ⟨hϱ, le_rfl⟩
    ϱ ϱ ⟨le_rfl, le_rfl⟩ ⟨le_rfl, le_rfl⟩).1
  simp only [hβ, hμ, hlam] at habs
  have hsum : Summable (fun k : ℕ =>
      lagResp cert γstar CSig β (k + 1) B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) +
      lagResp cert γstar CSig β (k + 1) B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  refine ⟨(eqn_app_pl_Cil_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i 0 hϱ).1, ?_, ?_⟩
  · refine (hsum.mul_left ((B : ℝ) / 2)).congr fun k => ?_
    dsimp only [lagRowBar]
    ring
  · simp only [rowVBar, ← two_mul, tsum_mul_left]

/-! ## Two ridges and the lag envelope (`lem:app-pl-two-ridge`) -/

private lemma zr_row_exists (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) : plRowExists cert γstar CSig β B μ i := by
  exact (eqn_app_pl_Cil_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1
    i 0 (ϱ := 1) zero_lt_one).1

private lemma zr_branch_nonneg (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    0 ≤ (Muon.DetEquiv.branchSol F ν ν' s).2.2.1 ∧
      0 ≤ (Muon.DetEquiv.branchSol F ν ν' s).2.2.2 := by
  classical
  unfold Muon.DetEquiv.branchSol
  split_ifs with h
  · have hx := h.choose_spec
    generalize h.choose = x at hx
    obtain ⟨σ, σ', a, c⟩ := x
    exact ⟨hx.2.2.1, hx.2.2.2.1⟩
  · simp

private lemma zr_volraw_bounds {β x ϱ : ℝ} (ν ν' : FiniteMeasure ℝ)
    (hx : 0 ≤ x) (hϱ : 0 < ϱ) : 0 ≤ volraw β ν ν' x ϱ ∧ volraw β ν ν' x ϱ ≤ 1 := by
  have ha := (zr_branch_nonneg (Fw (Muon.emaW β)) ν ν' ϱ).1
  unfold volraw
  have hp : 0 ≤ (Muon.DetEquiv.branchSol (Fw (Muon.emaW β)) ν ν' ϱ).2.2.1 * x :=
    mul_nonneg ha hx
  constructor
  · exact div_nonneg hp (by positivity)
  · exact (div_le_one (by positivity)).2 (by linarith)

private lemma zr_zero_lag_bound (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    |lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤ 1 := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS⟩ :=
    zr_setup hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  have hId : Fp.C.Sin = 1 := by
    rw [Muon.Setup.Sin_eq_spectral S, hlam]
    simpa using (mul_eq_one_comm.mp S.hvIn)
  have hz := Muon.Volatility.thm_app_vol_mode_kernels_iv_zero_lag cert γstar CSig
    Fp S hS hC1 hId (Muon.Drift.specOutFM Fp) (Muon.Drift.specInFM Fp) rfl rfl i ϱ hϱ
  simp only [hβ, hμ, hlam] at hz
  rw [hz, abs_of_nonneg (zr_volraw_bounds (Muon.Drift.specOutFM Fp)
    (Muon.Drift.specInFM Fp) (hpos i).le hϱ).1]
  exact (zr_volraw_bounds (Muon.Drift.specOutFM Fp) (Muon.Drift.specInFM Fp)
    (hpos i).le hϱ).2

private lemma zr_lag_nonneg (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    0 ≤ lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS⟩ :=
    zr_setup hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  let Fm := S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * Matrix.transpose S.uOut
  let Gm := S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * Matrix.transpose S.vIn
  have hF : Fm.PosSemidef := by
    have hd : (Matrix.diagonal (Pi.single i 1 : Fin N → ℝ)).PosSemidef := by
      rw [Matrix.posSemidef_diagonal_iff]
      intro j
      by_cases hj : j = i <;> simp [Pi.single_apply, hj]
    simpa only [Fm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hd.mul_mul_conjTranspose_same S.uOut
  have hG : Gm.PosSemidef := by
    have hd : (Matrix.diagonal (fun _ : Fin N => (1 : ℝ))).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun _ => zero_le_one)
    simpa only [Gm, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hd.mul_mul_conjTranspose_same S.vIn
  have hk (s u : ℝ) (hs : 0 < s) (hu : 0 < u) :
      0 ≤ (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF s) (iotaF u) := by
    have h := (Muon.Volatility.cor_app_vol_closed_bounds_i cert γstar CSig Fp S hS hC1 ℓ
      Fm Gm (Pi.single i 1) (fun _ => 1) rfl rfl).2.1 hF hG s u hs hu
    simpa only [hβ, hμ, hlam] using mul_nonneg (Nat.cast_nonneg B) h
  have hlim := (eqn_app_pl_Cil_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i ℓ hϱ).2.2.2
  refine ge_of_tendsto hlim ((eventually_ge_atTop (1 : ℝ)).mono fun T hT => ?_)
  refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith) fun x hx => ?_)
  refine intervalIntegral.integral_nonneg (by linarith) fun y hy => ?_
  exact hk (ϱ + x ^ 2) (ϱ + y ^ 2) (by positivity) (by positivity)

section ZrAlg
open scoped Matrix
open Matrix

/-- Frobenius pairing as a trace. -/
private def zr_ip {m n : ℕ} (U V : Mat m n) : ℝ := Matrix.trace (U * Vᵀ)

private lemma zr_ip_eq {m n : ℕ} (U V : Mat m n) : zr_ip U V = ∑ a, ∑ b, U a b * V a b := by
  simp [zr_ip, Matrix.trace, Matrix.mul_apply, Matrix.transpose_apply]

private lemma zr_ip_comm {m n : ℕ} (U V : Mat m n) : zr_ip U V = zr_ip V U := by
  rw [zr_ip_eq, zr_ip_eq]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => mul_comm _ _

private lemma zr_ip_self_nonneg {m n : ℕ} (U : Mat m n) : 0 ≤ zr_ip U U := by
  rw [zr_ip_eq]
  exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => mul_self_nonneg _

private lemma zr_ip_abs_le {m n : ℕ} (U V : Mat m n) :
    |zr_ip U V| ≤ (zr_ip U U + zr_ip V V) / 2 := by
  rw [zr_ip_eq, zr_ip_eq, zr_ip_eq, ← Finset.sum_add_distrib, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (U a b - V a b), sq_nonneg (U a b + V a b)]

private lemma zr_ip_sub_left {m n : ℕ} (U U' V : Mat m n) :
    zr_ip (U - U') V = zr_ip U V - zr_ip U' V := by
  simp [zr_ip, Matrix.sub_mul, Matrix.trace_sub]

private lemma zr_ip_sub_right {m n : ℕ} (U V V' : Mat m n) :
    zr_ip U (V - V') = zr_ip U V - zr_ip U V' := by
  simp [zr_ip, Matrix.mul_sub, Matrix.trace_sub]

private lemma zr_ip_smul_left {m n : ℕ} (s : ℝ) (U V : Mat m n) :
    zr_ip (s • U) V = s * zr_ip U V := by
  simp [zr_ip, Matrix.smul_mul, Matrix.trace_smul]

private lemma zr_ip_smul_right {m n : ℕ} (s : ℝ) (U V : Mat m n) :
    zr_ip U (s • V) = s * zr_ip U V := by
  simp [zr_ip, Matrix.mul_smul, Matrix.trace_smul]

/-- For a symmetric idempotent `P`: `tr(P X Yᵀ) = ⟨PX, PY⟩`. -/
private lemma zr_trace_proj {m n : ℕ} (P : Mat m m) (hs : Pᵀ = P) (hi : P * P = P)
    (X Y : Mat m n) : Matrix.trace (P * X * Yᵀ) = zr_ip (P * X) (P * Y) := by
  unfold zr_ip
  have h : P * (P * X * Yᵀ) = P * X * Yᵀ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hi]
  rw [Matrix.transpose_mul, hs, ← Matrix.mul_assoc (P * X) Yᵀ P,
    Matrix.trace_mul_comm (P * X * Yᵀ) P, h]

/-- Bessel for the rows. -/
private lemma zr_bessel {n r : ℕ} (q : Fin r → Vec n)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) (x : Vec n) :
    ∑ k, (q k ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set y : Vec n := x - ∑ k, (q k ⬝ᵥ x) • q k with hy
  have h0 : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct, ← sq]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hx1 : x ⬝ᵥ (∑ k, (q k ⬝ᵥ x) • q k) = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_smul, dotProduct_comm x (q k), smul_eq_mul, sq]
  have hx2 : (∑ k, (q k ⬝ᵥ x) • q k) ⬝ᵥ (∑ k, (q k ⬝ᵥ x) • q k) = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_sum]
    simp only [smul_dotProduct, dotProduct_smul, hq, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hexp : y ⬝ᵥ y = x ⬝ᵥ x - ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    have hx1' : (∑ k, (q k ⬝ᵥ x) • q k) ⬝ᵥ x = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
      rw [dotProduct_comm]; exact hx1
    rw [hy, sub_dotProduct, dotProduct_sub, dotProduct_sub, hx1, hx2, hx1']
    ring
  linarith

/-- `‖∑ c_k w_k ⊗ q_k‖²` for orthonormal `q`. -/
private lemma zr_ip_outer_sum {m n r : ℕ} (c : Fin r → ℝ) (w : Fin r → Vec m) (q : Fin r → Vec n)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) :
    zr_ip (∑ k, c k • outer (w k) (q k)) (∑ k, c k • outer (w k) (q k)) =
      ∑ k, c k ^ 2 * (w k ⬝ᵥ w k) := by
  rw [zr_ip_eq]
  have hrow : ∀ i : Fin m, ∑ j : Fin n, (∑ k, c k • outer (w k) (q k)) i j *
      (∑ k, c k • outer (w k) (q k)) i j = ∑ k, c k ^ 2 * w k i ^ 2 := by
    intro i
    have h1 : ∀ j, (∑ k, c k • outer (w k) (q k)) i j = (∑ k, (c k * w k i) • q k) j := by
      intro j
      simp [Matrix.sum_apply, Finset.sum_apply, Matrix.vecMulVec_apply, mul_assoc]
    have h2 : (∑ k, (c k * w k i) • q k) ⬝ᵥ (∑ k, (c k * w k i) • q k) = ∑ k, c k ^ 2 * w k i ^ 2 := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dotProduct_sum]
      simp only [smul_dotProduct, dotProduct_smul, hq, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    rw [← h2]
    simp only [dotProduct, h1]
  simp only [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [dotProduct, ← Finset.mul_sum, sq]

private lemma zr_cfc_mulVec_eq_smul {n : ℕ} (f : ℝ → ℝ) (A : Mat n n) (c : ℝ) (x : Vec n)
    (hA : IsSelfAdjoint A) (hx : A *ᵥ x = c • x) : cfc f A *ᵥ x = f c • x := by
  classical
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  set T : Finset ℝ := insert c hfin.toFinset with hT
  have hinj : Set.InjOn (id : ℝ → ℝ) (T : Set ℝ) := Set.injOn_id _
  set p : Polynomial ℝ := Lagrange.interpolate T id f with hp
  have hcongr : cfc f A = cfc p.eval A := by
    refine cfc_congr' fun y hy => ?_
    have hyT : y ∈ T := Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hy)
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj hyT
    simpa [hp] using this.symm
  have hc : p.eval c = f c := by
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj
      (Finset.mem_insert_self c _)
    simpa [hp] using this
  have hpow : ∀ i : ℕ, (A ^ i) *ᵥ x = c ^ i • x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hcongr, cfc_polynomial p A hA, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, hpow, smul_smul]
  rw [← Finset.sum_smul, ← hc, Polynomial.eval_eq_sum_range]

private lemma zr_svd_mulVec {m n r : ℕ} (K : Mat m n) (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) (l : Fin r) :
    K *ᵥ q l = s l • p l ∧ Kᵀ *ᵥ p l = s l • q l := by
  constructor
  · rw [hK, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hq, smul_smul]
    simp [Finset.sum_ite_eq', mul_comm]
  · rw [hK, Matrix.transpose_sum, Matrix.sum_mulVec]
    simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.transpose_vecMulVec,
      Matrix.vecMulVec_mulVec, hp, smul_smul]
    simp [Finset.sum_ite_eq', mul_comm]

private lemma zr_Q_eq_svd {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) {r : ℕ} (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n) (hs : ∀ k, 0 < s k)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (q k) := by
  have hsa : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set φ : ℝ → ℝ := fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ)) with hφ
  set C := cfc φ (Kᵀ * K) with hC
  have hCt : Cᵀ = C := by
    have h : IsSelfAdjoint C := cfc_predicate φ (Kᵀ * K)
    have h2 := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hvec : ∀ l, vecMul (q l) C = φ (s l ^ 2) • q l := by
    intro l
    obtain ⟨h1, h2⟩ := zr_svd_mulVec K s p q hp hq hK l
    have hev : (Kᵀ * K) *ᵥ q l = (s l ^ 2) • q l := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul, sq]
    rw [← Matrix.mulVec_transpose, hCt]
    exact zr_cfc_mulVec_eq_smul φ _ _ _ hsa hev
  unfold Q
  rw [← hC, hK]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.vecMulVec_mul, hvec k, Matrix.vecMulVec_smul, smul_smul]
  congr 1
  have hpos : 0 ≤ s k ^ 2 + ϱ := by positivity
  simp only [hφ]
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow, div_eq_mul_inv]

/-- Key matrix inequality: `‖P(Q_η K − Q_ϱ K)‖² + ‖P Q_ϱ K‖² ≤ ‖P‖²` for `0 < η ≤ ϱ`. -/
private lemma zr_key {m n : ℕ} (P : Mat m m) {η ϱ : ℝ} (hη : 0 < η) (hηϱ : η ≤ ϱ) (K : Mat m n) :
    zr_ip (P * (Q η K - Q ϱ K)) (P * (Q η K - Q ϱ K)) + zr_ip (P * Q ϱ K) (P * Q ϱ K) ≤
      zr_ip P P := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  have hs : ∀ k : Fin K.rank, 0 < (Matrix.toEuclideanLin K).singularValues (k : ℕ) :=
    fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.2
  set sv : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hsv
  have hQ : ∀ ϱ' : ℝ, 0 ≤ ϱ' → Q ϱ' K = ∑ k : Fin K.rank,
      (sv k / Real.sqrt (sv k ^ 2 + ϱ')) • outer (p k) (r k) :=
    fun ϱ' h => zr_Q_eq_svd ϱ' h K sv p r hs hp hr hK
  set cη : Fin K.rank → ℝ := fun k => sv k / Real.sqrt (sv k ^ 2 + η) with hcη
  set cϱ : Fin K.rank → ℝ := fun k => sv k / Real.sqrt (sv k ^ 2 + ϱ) with hcϱ
  have hPQ : ∀ (c : Fin K.rank → ℝ), P * ∑ k, c k • outer (p k) (r k) =
      ∑ k, c k • outer (P *ᵥ p k) (r k) := by
    intro c
    rw [Matrix.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_smul, Matrix.mul_vecMulVec]
  have hdiff : Q η K - Q ϱ K = ∑ k, (cη k - cϱ k) • outer (p k) (r k) := by
    rw [hQ η hη.le, hQ ϱ (hη.le.trans hηϱ), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_smul]
  rw [hdiff, hPQ, hQ ϱ (hη.le.trans hηϱ), hPQ,
    zr_ip_outer_sum _ _ _ hr, zr_ip_outer_sum _ _ _ hr, ← Finset.sum_add_distrib]
  have hrow : ∑ k, (P *ᵥ p k) ⬝ᵥ (P *ᵥ p k) ≤ zr_ip P P := by
    rw [zr_ip_eq]
    have e : ∀ k, (P *ᵥ p k) ⬝ᵥ (P *ᵥ p k) = ∑ a, (p k ⬝ᵥ (fun b => P a b)) ^ 2 := by
      intro k
      simp only [dotProduct, Matrix.mulVec, sq]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1 <;> exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    have := zr_bessel p hp (fun b => P a b)
    simpa [dotProduct, sq] using this
  refine le_trans (Finset.sum_le_sum fun k _ => ?_) hrow
  have hw : 0 ≤ (P *ᵥ p k) ⬝ᵥ (P *ᵥ p k) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  have hpos : 0 < sv k := hs k
  have hη' : 0 < sv k ^ 2 + η := by positivity
  have hϱ' : 0 < sv k ^ 2 + ϱ := by nlinarith [sq_nonneg (sv k)]
  have hc1 : cϱ k ≤ cη k := by
    simp only [hcη, hcϱ]
    exact div_le_div_of_nonneg_left hpos.le (Real.sqrt_pos.mpr hη')
      (Real.sqrt_le_sqrt (by linarith))
  have hc0 : 0 ≤ cϱ k := div_nonneg hpos.le (Real.sqrt_nonneg _)
  have hc2 : cη k ≤ 1 := by
    simp only [hcη]
    rw [div_le_one (Real.sqrt_pos.mpr hη')]
    calc sv k = Real.sqrt (sv k ^ 2) := (Real.sqrt_sq hpos.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have : (cη k - cϱ k) ^ 2 + cϱ k ^ 2 ≤ 1 := by nlinarith
  calc (cη k - cϱ k) ^ 2 * ((P *ᵥ p k) ⬝ᵥ (P *ᵥ p k)) + cϱ k ^ 2 * ((P *ᵥ p k) ⬝ᵥ (P *ᵥ p k))
      = ((cη k - cϱ k) ^ 2 + cϱ k ^ 2) * ((P *ᵥ p k) ⬝ᵥ (P *ᵥ p k)) := by ring
    _ ≤ 1 * ((P *ᵥ p k) ⬝ᵥ (P *ᵥ p k)) := mul_le_mul_of_nonneg_right this hw
    _ = _ := one_mul _

end ZrAlg

section ZrProb

private lemma zr_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma zr_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma zr_ip_cont {m n : ℕ} : Continuous (fun p : Mat m n × Mat m n => zr_ip p.1 p.2) := by
  unfold zr_ip
  fun_prop

private lemma zr_meas_ip {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} {U V : Ω → Mat m n}
    (hU : Measurable U) (hV : Measurable V) : Measurable (fun ω => zr_ip (U ω) (V ω)) := by
  haveI := zr_borel m n
  haveI := zr_sc m n
  exact (zr_ip_cont.measurable).comp (hU.prodMk hV)

private lemma zr_int_ip {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : ℕ} {U V : Ω → Mat m n} (hU : Measurable U) (hV : Measurable V) (ρ : ℝ)
    (hUb : ∀ ω, zr_ip (U ω) (U ω) ≤ ρ) (hVb : ∀ ω, zr_ip (V ω) (V ω) ≤ ρ) :
    Integrable (fun ω => zr_ip (U ω) (V ω)) μ := by
  refine Integrable.of_bound (C := ρ) (zr_meas_ip hU hV).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (zr_ip_abs_le _ _).trans ?_
  linarith [hUb ω, hVb ω]

private lemma zr_int_cs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : ℕ} {U V : Ω → Mat m n} (hU : Measurable U) (hV : Measurable V) (ρ : ℝ)
    (hUb : ∀ ω, zr_ip (U ω) (U ω) ≤ ρ) (hVb : ∀ ω, zr_ip (V ω) (V ω) ≤ ρ) :
    (∫ ω, zr_ip (U ω) (V ω) ∂μ) ^ 2 ≤
      (∫ ω, zr_ip (U ω) (U ω) ∂μ) * ∫ ω, zr_ip (V ω) (V ω) ∂μ := by
  have iUU := zr_int_ip (μ := μ) hU hU ρ hUb hUb
  have iVV := zr_int_ip (μ := μ) hV hV ρ hVb hVb
  have iUV := zr_int_ip (μ := μ) hU hV ρ hUb hVb
  set A := ∫ ω, zr_ip (U ω) (U ω) ∂μ
  set C := ∫ ω, zr_ip (V ω) (V ω) ∂μ
  set T := ∫ ω, zr_ip (U ω) (V ω) ∂μ
  have key : ∀ x : ℝ, 0 ≤ A * (x * x) + (-2 * T) * x + C := by
    intro x
    have h : 0 ≤ ∫ ω, zr_ip (x • U ω - V ω) (x • U ω - V ω) ∂μ :=
      integral_nonneg fun ω => zr_ip_self_nonneg _
    have e : (fun ω => zr_ip (x • U ω - V ω) (x • U ω - V ω)) =
        fun ω => (x * x) * zr_ip (U ω) (U ω) - (2 * x) * zr_ip (U ω) (V ω) + zr_ip (V ω) (V ω) := by
      funext ω
      rw [zr_ip_sub_left, zr_ip_sub_right, zr_ip_sub_right, zr_ip_smul_left, zr_ip_smul_right,
        zr_ip_smul_left, zr_ip_smul_right, zr_ip_comm (V ω) (U ω)]
      ring
    have i1 : Integrable (fun ω => (x * x) * zr_ip (U ω) (U ω)) μ := iUU.const_mul _
    have i2 : Integrable (fun ω => (2 * x) * zr_ip (U ω) (V ω)) μ := iUV.const_mul _
    have e2 : ∫ ω, ((x * x) * zr_ip (U ω) (U ω) - (2 * x) * zr_ip (U ω) (V ω)
        + zr_ip (V ω) (V ω)) ∂μ = (x * x) * A - (2 * x) * T + C := by
      rw [integral_add (f := fun ω => (x * x) * zr_ip (U ω) (U ω) - (2 * x) * zr_ip (U ω) (V ω))
        (g := fun ω => zr_ip (V ω) (V ω)) (i1.sub i2) iVV,
        integral_sub i1 i2, integral_const_mul, integral_const_mul]
    rw [e, e2] at h
    linarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

private lemma zr_cs_abs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {m n : ℕ} {U V : Ω → Mat m n} (hU : Measurable U) (hV : Measurable V) (ρ : ℝ)
    (hUb : ∀ ω, zr_ip (U ω) (U ω) ≤ ρ) (hVb : ∀ ω, zr_ip (V ω) (V ω) ≤ ρ) (a b : ℝ)
    (ha : ∫ ω, zr_ip (U ω) (U ω) ∂μ ≤ a) (hb : ∫ ω, zr_ip (V ω) (V ω) ∂μ ≤ b) :
    |∫ ω, zr_ip (U ω) (V ω) ∂μ| ≤ Real.sqrt (a * b) := by
  refine Real.abs_le_sqrt ((zr_int_cs (μ := μ) hU hV ρ hUb hVb).trans ?_)
  have hA : 0 ≤ ∫ ω, zr_ip (U ω) (U ω) ∂μ := integral_nonneg fun ω => zr_ip_self_nonneg _
  have hC : 0 ≤ ∫ ω, zr_ip (V ω) (V ω) ∂μ := integral_nonneg fun ω => zr_ip_self_nonneg _
  exact mul_le_mul ha hb hC (hA.trans ha)

end ZrProb

section ZrFin
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_prob (m n B : ℕ) : IsProbabilityMeasure (indepSpaceLaw m n B) := by
  unfold indepSpaceLaw indepSlotLaw
  infer_instance

private lemma zr_tsum_meas {m n : ℕ} {Ω' : Type*} (m1 : MeasurableSpace Ω') (f : ℕ → Ω' → Mat m n)
    (hf : ∀ j, Measurable[m1] (f j)) : Measurable[m1] (fun ω => ∑' j, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum hf

private lemma zr_prod_meas {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω s) := by
  haveI := zr_borel m n
  haveI := zr_sc m n
  unfold def_app_vol_product
  refine zr_tsum_meas _ _ fun j => ?_
  refine Measurable.const_smul ?_ (emaW F.β j)
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s + 1 - (j : ℤ), a))

private lemma zr_Q_meas {m n : ℕ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (Muon.Setup.measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma zr_upd_meas {m n B : ℕ} (F : FrozenParams m n B) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (t : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepUpd F ϱ ω t) :=
  (zr_Q_meas hϱ).comp (zr_prod_meas F t)

private lemma zr_fin {m n B : ℕ} (Fp : FrozenParams m n B) (P : Mat m m) (hs : Pᵀ = P)
    (hi : P * P = P) (T : ℝ → ℝ → ℤ → ℤ → ℝ)
    (hT : ∀ ϱ ϱ' t t', T ϱ ϱ' t t' = ∫ ω, Matrix.trace (P * indepUpd Fp ϱ ω t * (1 : Mat n n) *
      (indepUpd Fp ϱ' ω t')ᵀ) ∂(indepSpaceLaw m n B)) :
    (∀ ϱ ϱ' t t', 0 < ϱ → 0 < ϱ' → T ϱ ϱ' t t' ^ 2 ≤ T ϱ ϱ t t * T ϱ' ϱ' t' t') ∧
    (∀ ϱ t, 0 < ϱ → 0 ≤ T ϱ ϱ t t ∧ T ϱ ϱ t t ≤ zr_ip P P) ∧
    (∀ η ϱ t t', 0 < η → η ≤ ϱ → |T η η t t' - T ϱ ϱ t t'| ≤
      Real.sqrt (zr_ip P P) * (Real.sqrt (zr_ip P P - T ϱ ϱ t t) +
        Real.sqrt (zr_ip P P - T ϱ ϱ t' t'))) := by
  classical
  haveI := zr_prob m n B
  haveI := zr_borel m n
  haveI := zr_sc m n
  set μ := indepSpaceLaw m n B with hμ
  set ρ := zr_ip P P with hρ
  have hT' : ∀ ϱ ϱ' t t', T ϱ ϱ' t t' =
      ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ' ω t') ∂μ := by
    intro ϱ ϱ' t t'
    rw [hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Matrix.mul_one]
    exact zr_trace_proj P hs hi _ _
  have hPm : Measurable (fun K : Mat m n => P * K) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hX : ∀ ϱ, 0 < ϱ → ∀ t, Measurable (fun ω => P * indepUpd Fp ϱ ω t) :=
    fun ϱ hϱ t => hPm.comp (zr_upd_meas Fp hϱ.le t)
  have hD : ∀ η ϱ, 0 < η → η ≤ ϱ → ∀ t,
      Measurable (fun ω => P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t)) := by
    intro η ϱ hη hηϱ t
    have hsub : Measurable (fun ω => indepUpd Fp η ω t - indepUpd Fp ϱ ω t) :=
      (zr_upd_meas Fp hη.le t).sub (zr_upd_meas Fp (hη.le.trans hηϱ) t)
    exact hPm.comp hsub
  have hbd : ∀ ϱ, 0 < ϱ → ∀ ω t,
      zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) ≤ ρ := by
    intro ϱ hϱ ω t
    have h := zr_key P hϱ le_rfl (def_app_vol_product Fp ω t)
    have h0 := zr_ip_self_nonneg (P * (Q ϱ (def_app_vol_product Fp ω t) -
      Q ϱ (def_app_vol_product Fp ω t)))
    unfold indepUpd
    linarith
  have hkey : ∀ η ϱ, 0 < η → η ≤ ϱ → ∀ ω t,
      zr_ip (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t))
          (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t)) ≤
        ρ - zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) := by
    intro η ϱ hη hηϱ ω t
    have h := zr_key P hη hηϱ (def_app_vol_product Fp ω t)
    unfold indepUpd
    linarith
  have hkey0 : ∀ η ϱ, 0 < η → η ≤ ϱ → ∀ ω t,
      zr_ip (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t))
          (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t)) ≤ ρ := by
    intro η ϱ hη hηϱ ω t
    have h0 := zr_ip_self_nonneg (P * indepUpd Fp ϱ ω t)
    linarith [hkey η ϱ hη hηϱ ω t]
  have hintsq : ∀ ϱ, 0 < ϱ → ∀ t,
      Integrable (fun ω => zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t)) μ :=
    fun ϱ hϱ t => zr_int_ip (hX ϱ hϱ t) (hX ϱ hϱ t) ρ (fun ω => hbd ϱ hϱ ω t)
      (fun ω => hbd ϱ hϱ ω t)
  have hconst : ∫ ω, ρ ∂μ = ρ := by simp
  refine ⟨?_, ?_, ?_⟩
  · intro ϱ ϱ' t t' hϱ hϱ'
    rw [hT', hT', hT']
    exact zr_int_cs (hX ϱ hϱ t) (hX ϱ' hϱ' t') ρ (fun ω => hbd ϱ hϱ ω t)
      (fun ω => hbd ϱ' hϱ' ω t')
  · intro ϱ t hϱ
    rw [hT']
    refine ⟨integral_nonneg fun ω => zr_ip_self_nonneg _, ?_⟩
    calc ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) ∂μ ≤ ∫ ω, ρ ∂μ :=
          integral_mono (hintsq ϱ hϱ t) (integrable_const _) fun ω => hbd ϱ hϱ ω t
      _ = ρ := hconst
  · intro η ϱ t t' hη hηϱ
    have hϱ : 0 < ϱ := hη.trans_le hηϱ
    -- ∫ ‖P(Xη - Xϱ)‖² ≤ ρ - T ϱ ϱ
    have hdiffint : ∀ t, ∫ ω, zr_ip (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t))
        (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t)) ∂μ ≤ ρ - T ϱ ϱ t t := by
      intro t
      rw [hT' ϱ ϱ t t]
      have hi1 := zr_int_ip (μ := μ) (hD η ϱ hη hηϱ t) (hD η ϱ hη hηϱ t) ρ
        (hkey0 η ϱ hη hηϱ · t) (hkey0 η ϱ hη hηϱ · t)
      calc _ ≤ ∫ ω, (ρ - zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t)) ∂μ :=
            integral_mono hi1 ((integrable_const _).sub (hintsq ϱ hϱ t))
              fun ω => hkey η ϱ hη hηϱ ω t
        _ = _ := by rw [integral_sub (integrable_const _) (hintsq ϱ hϱ t), hconst]
    have hA : ∀ t, 0 ≤ ρ - T ϱ ϱ t t := fun t =>
      (integral_nonneg (fun ω => zr_ip_self_nonneg _)).trans (hdiffint t)
    have hfull : ∀ t, ∫ ω, zr_ip (P * indepUpd Fp η ω t) (P * indepUpd Fp η ω t) ∂μ ≤ ρ := by
      intro t
      calc _ ≤ ∫ ω, ρ ∂μ := integral_mono (hintsq η hη t) (integrable_const _)
              fun ω => hbd η hη ω t
        _ = ρ := hconst
    have hfull' : ∀ t, ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) ∂μ ≤ ρ := by
      intro t
      calc _ ≤ ∫ ω, ρ ∂μ := integral_mono (hintsq ϱ hϱ t) (integrable_const _)
              fun ω => hbd ϱ hϱ ω t
        _ = ρ := hconst
    have hdecomp : T η η t t' - T ϱ ϱ t t' =
        (∫ ω, zr_ip (P * (indepUpd Fp η ω t - indepUpd Fp ϱ ω t)) (P * indepUpd Fp η ω t') ∂μ) +
        ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * (indepUpd Fp η ω t' - indepUpd Fp ϱ ω t')) ∂μ := by
      have i1 := zr_int_ip (μ := μ) (hD η ϱ hη hηϱ t) (hX η hη t') ρ
        (hkey0 η ϱ hη hηϱ · t) (fun ω => hbd η hη ω t')
      have i2 := zr_int_ip (μ := μ) (hX ϱ hϱ t) (hD η ϱ hη hηϱ t') ρ
        (fun ω => hbd ϱ hϱ ω t) (hkey0 η ϱ hη hηϱ · t')
      rw [hT', hT', ← integral_add i1 i2]
      have i3 := zr_int_ip (μ := μ) (hX η hη t) (hX η hη t') ρ (fun ω => hbd η hη ω t)
        (fun ω => hbd η hη ω t')
      have i4 := zr_int_ip (μ := μ) (hX ϱ hϱ t) (hX ϱ hϱ t') ρ (fun ω => hbd ϱ hϱ ω t)
        (fun ω => hbd ϱ hϱ ω t')
      rw [← integral_sub i3 i4]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Matrix.mul_sub, zr_ip_sub_left, zr_ip_sub_right]
      ring
    have c1 := zr_cs_abs (μ := μ) (hD η ϱ hη hηϱ t) (hX η hη t') ρ
      (hkey0 η ϱ hη hηϱ · t) (fun ω => hbd η hη ω t') _ _ (hdiffint t) (hfull t')
    have c2 := zr_cs_abs (μ := μ) (hX ϱ hϱ t) (hD η ϱ hη hηϱ t') ρ
      (fun ω => hbd ϱ hϱ ω t) (hkey0 η ϱ hη hηϱ · t') _ _ (hfull' t) (hdiffint t')
    have hρ0 : 0 ≤ ρ := zr_ip_self_nonneg P
    rw [hdecomp]
    refine (abs_add_le _ _).trans ?_
    rw [Real.sqrt_mul (hA t)] at c1
    rw [Real.sqrt_mul hρ0] at c2
    nlinarith [c1, c2]

end ZrFin



section ZrRepl
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_replMat_apply {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) (a b : Fin (N * m)) :
    replMat S N a b = S ((replIdx m N).symm a).1 ((replIdx m N).symm b).1 *
      (if ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 then 1 else 0) := by
  simp [replMat, repKron, Matrix.one_apply]

private lemma zr_replMat_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    replMat (A * B) N = replMat A N * replMat B N := by
  unfold replMat repKron
  rw [Matrix.submatrix_mul_equiv]
  congr 1
  erw [← Matrix.mul_kronecker_mul, mul_one]
  rfl

private lemma zr_replMat_transpose {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    (replMat A N)ᵀ = replMat Aᵀ N := by
  unfold replMat repKron
  rw [Matrix.transpose_submatrix]
  congr 1
  have hT : (Matrix.kronecker A (1 : Matrix (Fin N) (Fin N) ℝ))ᵀ =
      Matrix.kronecker Aᵀ (1 : Matrix (Fin N) (Fin N) ℝ)ᵀ :=
    (Matrix.kroneckerMap_transpose _ _ _).symm
  rw [hT, Matrix.transpose_one]

private lemma zr_replMat_diagonal {m : ℕ} (d : Fin m → ℝ) (N : ℕ) :
    replMat (Matrix.diagonal d) N = Matrix.diagonal (replVec N d) := by
  ext a b
  rw [zr_replMat_apply]
  unfold replVec
  simp only [Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h; simp
  · have : ¬ (((replIdx m N).symm a).1 = ((replIdx m N).symm b).1 ∧
        ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2) := by
      rintro ⟨h1, h2⟩
      exact h ((replIdx m N).symm.injective (Prod.ext h1 h2))
    by_cases h1 : ((replIdx m N).symm a).1 = ((replIdx m N).symm b).1
    · have h2 : ¬ ((replIdx m N).symm a).2 = ((replIdx m N).symm b).2 := fun h2 => this ⟨h1, h2⟩
      simp [h, h2]
    · simp [h, h1]

private lemma zr_replMat_one {m : ℕ} (N : ℕ) : replMat (1 : Matrix (Fin m) (Fin m) ℝ) N = 1 := by
  unfold replMat repKron
  have h : Matrix.kronecker (1 : Matrix (Fin m) (Fin m) ℝ) (1 : Matrix (Fin N) (Fin N) ℝ) = 1 :=
    Matrix.one_kronecker_one
  rw [h, Matrix.submatrix_one_equiv]

private lemma zr_replMat_orth {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : Sᵀ * S = 1) (N : ℕ) :
    (replMat S N)ᵀ * replMat S N = 1 := by
  rw [zr_replMat_transpose, ← zr_replMat_mul, hS, zr_replMat_one]

private lemma zr_eig_matrix {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : ∀ i : Fin k, S *ᵥ (fun r => U r i) = μ i • (fun r => U r i)) :
    S * U = U * Matrix.diagonal μ := by
  ext r i
  have := congrFun (h i) r
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
  rw [Matrix.mul_apply, Matrix.mul_diagonal]
  rw [this]; ring

private lemma zr_eig_vec {k : ℕ} (S U : Matrix (Fin k) (Fin k) ℝ) (μ : Fin k → ℝ)
    (h : S * U = U * Matrix.diagonal μ) (i : Fin k) :
    S *ᵥ (fun r => U r i) = μ i • (fun r => U r i) := by
  funext r
  have := congrFun (congrFun h r) i
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at this
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [this]; ring

private lemma zr_exists_replSpec {m n : ℕ} (C : Covariances m n) (S : SpectralData C) (N : ℕ) :
    ∃ S' : SpectralData (replCov C N), S'.uOut = replMat S.uOut N ∧ S'.vIn = replMat S.vIn N ∧
      S'.μ = replVec N S.μ ∧ S'.lam = replVec N S.lam := by
  have h1 := zr_eig_matrix C.Sout S.uOut S.μ S.eigOut
  have h2 := zr_eig_matrix C.Sin S.vIn S.lam S.eigIn
  refine ⟨⟨replMat S.uOut N, replMat S.vIn N, replVec N S.μ, replVec N S.lam,
    zr_replMat_orth _ S.huOut N, zr_replMat_orth _ S.hvIn N, ?_, ?_⟩, rfl, rfl, rfl, rfl⟩
  · intro i
    refine zr_eig_vec _ _ _ ?_ i
    change replMat C.Sout N * replMat S.uOut N = replMat S.uOut N * Matrix.diagonal (replVec N S.μ)
    rw [← zr_replMat_diagonal, ← zr_replMat_mul, ← zr_replMat_mul, h1]
  · intro i
    refine zr_eig_vec _ _ _ ?_ i
    change replMat C.Sin N * replMat S.vIn N = replMat S.vIn N * Matrix.diagonal (replVec N S.lam)
    rw [← zr_replMat_diagonal, ← zr_replMat_mul, ← zr_replMat_mul, h2]


private lemma zr_proj_facts {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ)
    (hd : ∀ j, d j = 0 ∨ d j = 1) :
    (U * Matrix.diagonal d * Uᵀ)ᵀ = U * Matrix.diagonal d * Uᵀ ∧
    (U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal d * Uᵀ) = U * Matrix.diagonal d * Uᵀ ∧
    zr_ip (U * Matrix.diagonal d * Uᵀ) (U * Matrix.diagonal d * Uᵀ) = ∑ j, d j := by
  have hDD : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    rcases hd j with h | h <;> simp [h]
  have hsym : (U * Matrix.diagonal d * Uᵀ)ᵀ = U * Matrix.diagonal d * Uᵀ := by
    simp [Matrix.transpose_mul, Matrix.mul_assoc]
  have hidem : (U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal d * Uᵀ) =
      U * Matrix.diagonal d * Uᵀ := by
    calc (U * Matrix.diagonal d * Uᵀ) * (U * Matrix.diagonal d * Uᵀ)
        = U * Matrix.diagonal d * (Uᵀ * U) * Matrix.diagonal d * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = U * (Matrix.diagonal d * Matrix.diagonal d) * Uᵀ := by
          rw [hU, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [hDD]
  refine ⟨hsym, hidem, ?_⟩
  unfold zr_ip
  rw [hsym, hidem, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hU,
    Matrix.one_mul, Matrix.trace_diagonal]

section ZrOrth
open scoped Matrix.Norms.L2Operator

private lemma zr_norm_left_orth {a b : ℕ} (U : Matrix (Fin a) (Fin a) ℝ) (hU : Uᵀ * U = 1)
    (X : Matrix (Fin a) (Fin b) ℝ) : ‖U * X‖ = ‖X‖ := by
  have hUh : Uᴴ * U = 1 := by rw [Matrix.conjTranspose_eq_transpose_of_trivial]; exact hU
  have h : ‖U * X‖ * ‖U * X‖ = ‖X‖ * ‖X‖ := by
    rw [← Matrix.l2_opNorm_conjTranspose_mul_self, ← Matrix.l2_opNorm_conjTranspose_mul_self]
    congr 1
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U X, hUh, Matrix.one_mul]
  exact (mul_self_inj (norm_nonneg _) (norm_nonneg _)).mp h

private lemma zr_norm_right_orth {a b : ℕ} (X : Matrix (Fin a) (Fin b) ℝ)
    (W : Matrix (Fin b) (Fin b) ℝ) (hW : Wᵀ * W = 1) : ‖X * W‖ = ‖X‖ := by
  calc ‖X * W‖ = ‖(X * W)ᴴ‖ := (Matrix.l2_opNorm_conjTranspose _).symm
    _ = ‖Wᴴ * Xᴴ‖ := by rw [Matrix.conjTranspose_mul]
    _ = ‖Xᴴ‖ := by
      refine zr_norm_left_orth Wᴴ ?_ Xᴴ
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
      exact mul_eq_one_comm.mp hW
    _ = ‖X‖ := Matrix.l2_opNorm_conjTranspose X

private theorem zr_opNorm_conj_diag {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : Uᵀ * U = 1)
    (d : Fin k → ℝ) (hd : ∀ i, |d i| ≤ 1) : opNorm (U * Matrix.diagonal d * Uᵀ) ≤ 1 := by
  rw [opNorm_eq_norm]
  rw [zr_norm_right_orth _ Uᵀ (by rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.mp hU),
    zr_norm_left_orth U hU, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simpa using hd i

end ZrOrth

end ZrRepl

section ZrEnv
open scoped Matrix
open ProbabilityTheory
open Muon.Setup Muon.Volatility

private lemma zr_fsum_meas {m n : ℕ} {Ω' : Type*} {m1 : MeasurableSpace Ω'} (f : ℕ → Ω' → Mat m n)
    (s : Finset ℕ) (hf : ∀ j ∈ s, Measurable[m1] (f j)) :
    Measurable[m1] (fun ω => ∑ j ∈ s, f j ω) := by
  letI : MeasurableSpace Ω' := m1
  haveI := zr_borel m n
  haveI := zr_sc m n
  exact Finset.measurable_sum _ hf

private lemma zr_batch_meas_sub {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) (T : Set (ℤ × Fin B))
    (hT : ∀ a, (s, a) ∈ T) :
    Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => indepBatchG F ω s) := by
  have h : ∀ a, Measurable[⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω (s, a)) := fun a =>
    Measurable.of_comap_le (le_iSup₂ (f := fun i (_ : i ∈ T) => MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) (s, a) (hT a))
  generalize (⨆ i ∈ T, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance) = m1 at h ⊢
  letI : MeasurableSpace ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) := m1
  haveI := zr_borel m n
  haveI := zr_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (h a)

private lemma zr_batch_meas {m n B : ℕ} (F : FrozenParams m n B) (s : ℤ) :
    Measurable (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => indepBatchG F ω s) := by
  haveI := zr_borel m n
  haveI := zr_sc m n
  unfold indepBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : ℝ × (Vec m × Vec n) =>
      p.1 • (rOut F.C * outer p.2.1 p.2.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (measurable_pi_apply (s, a))

private lemma zr_indep {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    IndepFun (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => def_app_vol_product F ω t)
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)))
      (indepSpaceLaw m n B) := by
  haveI := zr_prob m n B
  have hI : iIndepFun (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
      (indepSpaceLaw m n B) :=
    iIndepFun_infinitePi (P := fun _ : ℤ × Fin B => indepSlotLaw m n)
      (X := fun _ x => x) (fun _ => measurable_id)
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (ℝ × (Vec m × Vec n))))
    (fun (p : ℤ × Fin B) (ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n)) => ω p)
    (indepSpaceLaw m n B)).mp hI
  have hdisj : Disjoint {p : ℤ × Fin B | p.1 ≤ t + 1} {p : ℤ × Fin B | t + 2 ≤ p.1} := by
    rw [Set.disjoint_left]
    intro p h1 h2
    simp only [Set.mem_setOf_eq] at h1 h2
    omega
  have key := indep_iSup_of_disjoint
    (fun p : ℤ × Fin B => (measurable_pi_apply (X := fun _ : ℤ × Fin B => ℝ × (Vec m × Vec n)) p).comap_le)
    hind hdisj
  have hA : Measurable[⨆ i ∈ {p : ℤ × Fin B | p.1 ≤ t + 1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => def_app_vol_product F ω t) := by
    unfold def_app_vol_product
    refine zr_tsum_meas _ _ fun j => ?_
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact zr_batch_meas_sub F _ _ (fun a => by
      show t + 1 - (j : ℤ) ≤ t + 1
      omega)
  have hB : Measurable[⨆ i ∈ {p : ℤ × Fin B | t + 2 ≤ p.1}, MeasurableSpace.comap
      (fun ω : (ℤ × Fin B) → ℝ × (Vec m × Vec n) => ω i) inferInstance]
      (fun ω => ∑ j ∈ Finset.range ℓ,
        emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) := by
    refine zr_fsum_meas _ _ fun j hj => ?_
    rw [Finset.mem_range] at hj
    refine Measurable.const_smul ?_ (emaW F.β j)
    exact zr_batch_meas_sub F _ _ (fun a => by
      show t + 2 ≤ t + (ℓ : ℤ) + 1 - (j : ℤ)
      omega)
  exact (IndepFun_iff_Indep _ _ (indepSpaceLaw m n B)).mpr
    (indep_of_indep_of_le_left (indep_of_indep_of_le_right key (measurable_iff_comap_le.mp hB))
      (measurable_iff_comap_le.mp hA))

private lemma zr_mean_zero {m n B : ℕ} (F : FrozenParams m n B) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ)
    (a : Fin m) (b : Fin n) :
    ∫ ω, Q ϱ (def_app_vol_product F ω t) a b ∂(indepSpaceLaw m n B) = 0 := by
  have hodd : ∀ x : ℝ, omegaF ϱ (-x) = -omegaF ϱ x := by
    intro x
    simp [omegaF, neg_div]
  have hbdd : ∃ M : ℝ, ∀ x : ℝ, |omegaF ϱ x| ≤ M := by
    refine ⟨1, fun x => ?_⟩
    have hpos : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr (by positivity)
    unfold omegaF
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact Real.abs_le_sqrt (by linarith)
  have h := def_app_vol_product_mean_oddSharp F (omegaF ϱ) hodd hbdd t
  have h2 := congrFun (congrFun h a) b
  simp only [Muon.mean, Matrix.of_apply, Matrix.zero_apply] at h2
  have e : ∀ ω, oddSharp (omegaF ϱ) (def_app_vol_product F ω t) =
      Q ϱ (def_app_vol_product F ω t) := fun ω => eqn_app_vol_filters_sharp_ii hϱ _
  simp_rw [e] at h2
  exact h2

open scoped Matrix.Norms.Frobenius in
private lemma zr_decomp {m n B : ℕ} (F : FrozenParams m n B) (t : ℤ) (ℓ : ℕ) :
    ∀ᵐ ω ∂(indepSpaceLaw m n B), def_app_vol_product F ω (t + (ℓ : ℤ)) =
      (∑ j ∈ Finset.range ℓ, emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ))) +
      F.β ^ ℓ • def_app_vol_product F ω t := by
  filter_upwards [def_app_vol_product_summable F] with ω hω
  have hs : Summable fun j : ℕ =>
      emaW F.β j • indepBatchG F ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := by
    refine Summable.of_norm ?_
    simpa [fro_eq_norm] using hω (t + (ℓ : ℤ))
  unfold def_app_vol_product
  rw [← Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff ℓ).2 hs)]
  congr 1
  have hshift : ∀ i : ℕ, emaW F.β (i + ℓ) • indepBatchG F ω (t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ)) =
      F.β ^ ℓ • (emaW F.β i • indepBatchG F ω (t + 1 - (i : ℤ))) := by
    intro i
    have e1 : t + (ℓ : ℤ) + 1 - ((i + ℓ : ℕ) : ℤ) = t + 1 - (i : ℤ) := by push_cast; ring
    have e2 : emaW F.β (i + ℓ) = F.β ^ ℓ * emaW F.β i := by
      unfold emaW; ring
    rw [e1, e2, smul_smul]
  simp_rw [hshift]
  exact tsum_const_smul'' _

private lemma zr_fro_sq {m n : ℕ} (K : Mat m n) : fro K ^ 2 = zr_ip K K := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity),
    zr_ip_eq]
  simp [Real.norm_eq_abs, sq_abs, sq]

private lemma zr_ip_sub_le {m n : ℕ} (a b : Mat m n) :
    zr_ip (a - b) (a - b) ≤ 2 * zr_ip a a + 2 * zr_ip b b := by
  rw [zr_ip_eq, zr_ip_eq, zr_ip_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (a x y + b x y)]

private lemma zr_proj_le {m n : ℕ} (P : Mat m m) (hs : Pᵀ = P) (hi : P * P = P) (D : Mat m n) :
    zr_ip (P * D) (P * D) ≤ zr_ip D D := by
  have hs' : (1 - P)ᵀ = 1 - P := by rw [Matrix.transpose_sub, Matrix.transpose_one, hs]
  have hi' : (1 - P) * (1 - P) = 1 - P := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, hi]
    abel
  have h1 := zr_trace_proj P hs hi D D
  have h2 := zr_trace_proj (1 - P) hs' hi' D D
  have h3 : Matrix.trace (P * D * Dᵀ) + Matrix.trace ((1 - P) * D * Dᵀ) = zr_ip D D := by
    rw [← Matrix.trace_add, ← Matrix.add_mul, ← Matrix.add_mul]
    simp [zr_ip]
  have := zr_ip_self_nonneg ((1 - P) * D)
  linarith

private lemma zr_entry_bound {m n : ℕ} {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (K : Mat m n) (a : Fin m) (b : Fin n) :
    |Q ϱ K a b| ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨-, h2, h3, -⟩ := Muon.Setup.lem_app_setup_filter_i ϱ hϱ K
  have h4 : zr_ip (Q ϱ K) (Q ϱ K) ≤ ((min m n : ℕ) : ℝ) := by
    rw [← zr_fro_sq]; exact h2.trans (by exact_mod_cast h3)
  refine Real.abs_le_sqrt ?_
  refine le_trans ?_ h4
  rw [zr_ip_eq]
  calc Q ϱ K a b ^ 2 = Q ϱ K a b * Q ϱ K a b := sq _
    _ ≤ ∑ b', Q ϱ K a b' * Q ϱ K a b' :=
        Finset.single_le_sum (f := fun b' => Q ϱ K a b' * Q ϱ K a b') (fun _ _ => mul_self_nonneg _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', Q ϱ K a' b' * Q ϱ K a' b' :=
        Finset.single_le_sum (f := fun a' => ∑ b', Q ϱ K a' b' * Q ϱ K a' b')
          (fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _) (Finset.mem_univ a)

private lemma zr_env {m n B : ℕ} (Fp : FrozenParams m n B) (P : Mat m m) (hs : Pᵀ = P)
    (hi : P * P = P) {ϱ : ℝ} (hϱ : 0 < ϱ) (t : ℤ) (ℓ : ℕ)
    (htr : 0 < Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin) :
    (∫ ω, Matrix.trace (P * indepUpd Fp ϱ ω t * (1 : Mat n n) *
        (indepUpd Fp ϱ ω (t + (ℓ : ℤ)))ᵀ) ∂(indepSpaceLaw m n B)) ^ 2 ≤
      zr_ip P P * (ϱ⁻¹ * Fp.β ^ (2 * ℓ) * ((B : ℝ) * (sPow Fp.β 2 / (B : ℝ) ^ 2 *
        Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin))) := by
  classical
  haveI := zr_prob m n B
  haveI := zr_borel m n
  haveI := zr_sc m n
  set μ := indepSpaceLaw m n B with hμ
  set ρ := zr_ip P P with hρ
  obtain ⟨hβ0, hβ1⟩ := Fp.hβ
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hρ0 : 0 ≤ ρ := zr_ip_self_nonneg P
  obtain ⟨Nl, hNl⟩ : ∃ Nl : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n,
      Nl = fun ω => ∑ j ∈ Finset.range ℓ,
        emaW Fp.β j • indepBatchG Fp ω (t + (ℓ : ℤ) + 1 - (j : ℤ)) := ⟨_, rfl⟩
  have hNlm : Measurable Nl := by
    rw [hNl]
    exact Finset.measurable_sum _ fun j _ =>
      (zr_batch_meas Fp (t + (ℓ : ℤ) + 1 - (j : ℤ))).const_smul (emaW Fp.β j)
  have hind : IndepFun (fun ω => def_app_vol_product Fp ω t) Nl μ := by
    rw [hNl]; exact zr_indep Fp t ℓ
  have hdec : ∀ᵐ ω ∂μ, def_app_vol_product Fp ω (t + (ℓ : ℤ)) =
      Nl ω + Fp.β ^ ℓ • def_app_vol_product Fp ω t := by
    filter_upwards [zr_decomp Fp t ℓ] with ω hω
    rw [hNl]; exact hω
  -- measurability
  have hPm : Measurable (fun K : Mat m n => P * K) :=
    (continuous_const.matrix_mul continuous_id).measurable
  have hXm : Measurable (fun ω => indepUpd Fp ϱ ω t) := zr_upd_meas Fp hϱ.le t
  have hYm : Measurable (fun ω => indepUpd Fp ϱ ω (t + (ℓ : ℤ))) := zr_upd_meas Fp hϱ.le _
  have hZm : Measurable (fun ω => Q ϱ (Nl ω)) := (zr_Q_meas hϱ.le).comp hNlm
  have hUm : Measurable (fun ω => P * indepUpd Fp ϱ ω t) := hPm.comp hXm
  have hPYm : Measurable (fun ω => P * indepUpd Fp ϱ ω (t + (ℓ : ℤ))) := hPm.comp hYm
  have hPZm : Measurable (fun ω => P * Q ϱ (Nl ω)) := hPm.comp hZm
  have hVm : Measurable (fun ω => P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) :=
    hPm.comp (hYm.sub hZm)
  -- bounds
  have hQb : ∀ K : Mat m n, zr_ip (P * Q ϱ K) (P * Q ϱ K) ≤ ρ := by
    intro K
    have h := zr_key P hϱ le_rfl K
    have h0 := zr_ip_self_nonneg (P * (Q ϱ K - Q ϱ K))
    linarith
  have hVb : ∀ ω, zr_ip (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω)))
      (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) ≤ 4 * ρ := by
    intro ω
    rw [Matrix.mul_sub]
    have h := zr_ip_sub_le (P * indepUpd Fp ϱ ω (t + (ℓ : ℤ))) (P * Q ϱ (Nl ω))
    have h1 := hQb (def_app_vol_product Fp ω (t + (ℓ : ℤ)))
    have h2 := hQb (Nl ω)
    unfold indepUpd at h ⊢
    linarith
  have hUb : ∀ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) ≤ 4 * ρ := by
    intro ω
    have := hQb (def_app_vol_product Fp ω t)
    unfold indepUpd
    linarith
  have hPYb : ∀ ω, zr_ip (P * indepUpd Fp ϱ ω (t + (ℓ : ℤ))) (P * indepUpd Fp ϱ ω (t + (ℓ : ℤ)))
      ≤ 4 * ρ := by
    intro ω
    have := hQb (def_app_vol_product Fp ω (t + (ℓ : ℤ)))
    unfold indepUpd
    linarith
  have hPZb : ∀ ω, zr_ip (P * Q ϱ (Nl ω)) (P * Q ϱ (Nl ω)) ≤ 4 * ρ := by
    intro ω
    have := hQb (Nl ω)
    linarith
  -- the zero-mean pairing
  have hentm : ∀ (W : ((ℤ × Fin B) → ℝ × (Vec m × Vec n)) → Mat m n), Measurable W →
      ∀ (a : Fin m) (b : Fin n), Measurable (fun ω => W ω a b) :=
    fun W hW a b => (measurable_pi_apply b).comp ((measurable_pi_apply a).comp hW)
  have hzero : ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * Q ϱ (Nl ω)) ∂μ = 0 := by
    have hpt : ∀ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * Q ϱ (Nl ω)) =
        ∑ c, ∑ e, ∑ d, P c d * (indepUpd Fp ϱ ω t d e * Q ϱ (Nl ω) c e) := by
      intro ω
      rw [← zr_trace_proj P hs hi]
      simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      ring
    have hint : ∀ c e d, Integrable (fun ω => P c d * (indepUpd Fp ϱ ω t d e * Q ϱ (Nl ω) c e)) μ := by
      intro c e d
      refine Integrable.of_bound (C := |P c d| * (Real.sqrt ((min m n : ℕ) : ℝ) *
        Real.sqrt ((min m n : ℕ) : ℝ))) ?_ (Filter.Eventually.of_forall fun ω => ?_)
      · exact (((hentm _ hXm d e).mul (hentm _ hZm c e)).const_mul _).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact mul_le_mul (zr_entry_bound hϱ.le _ d e) (zr_entry_bound hϱ.le _ c e)
          (abs_nonneg _) (Real.sqrt_nonneg _)
    simp_rw [hpt]
    rw [integral_finsetSum _ (fun c _ => integrable_finsetSum _ (fun e _ =>
      integrable_finsetSum _ (fun d _ => hint c e d)))]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [integral_finsetSum _ (fun e _ => integrable_finsetSum _ (fun d _ => hint c e d))]
    refine Finset.sum_eq_zero fun e _ => ?_
    rw [integral_finsetSum _ (fun d _ => hint c e d)]
    refine Finset.sum_eq_zero fun d _ => ?_
    rw [integral_const_mul]
    have hf : Measurable (fun K : Mat m n => Q ϱ K d e) :=
      (measurable_pi_apply e).comp ((measurable_pi_apply d).comp (zr_Q_meas hϱ.le))
    have hg : Measurable (fun K : Mat m n => Q ϱ K c e) :=
      (measurable_pi_apply e).comp ((measurable_pi_apply c).comp (zr_Q_meas hϱ.le))
    have hMm := zr_prod_meas Fp t
    have := hind.integral_fun_comp_mul_comp hMm.aemeasurable hNlm.aemeasurable
      hf.aestronglyMeasurable hg.aestronglyMeasurable
    have e1 : ∫ ω, Q ϱ (def_app_vol_product Fp ω t) d e ∂μ = 0 := zr_mean_zero Fp hϱ t d e
    have h2 : (∫ ω, indepUpd Fp ϱ ω t d e * Q ϱ (Nl ω) c e ∂μ) =
        (∫ ω, Q ϱ (def_app_vol_product Fp ω t) d e ∂μ) * ∫ ω, Q ϱ (Nl ω) c e ∂μ := this
    rw [h2, e1, zero_mul, mul_zero]
  -- integrability and the reduction to the difference
  have iXZ : Integrable (fun ω => zr_ip (P * indepUpd Fp ϱ ω t) (P * Q ϱ (Nl ω))) μ :=
    zr_int_ip hUm hPZm (4 * ρ) hUb hPZb
  have iXV := zr_int_ip (μ := μ) hUm hVm (4 * ρ) hUb hVb
  have hT : (∫ ω, Matrix.trace (P * indepUpd Fp ϱ ω t * (1 : Mat n n) *
      (indepUpd Fp ϱ ω (t + (ℓ : ℤ)))ᵀ) ∂μ) =
      ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t)
        (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) ∂μ := by
    have e1 : (∫ ω, Matrix.trace (P * indepUpd Fp ϱ ω t * (1 : Mat n n) *
        (indepUpd Fp ϱ ω (t + (ℓ : ℤ)))ᵀ) ∂μ) =
        ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω (t + (ℓ : ℤ))) ∂μ := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Matrix.mul_one]
      exact zr_trace_proj P hs hi _ _
    have e2 : ∀ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω (t + (ℓ : ℤ))) =
        zr_ip (P * indepUpd Fp ϱ ω t) (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) +
          zr_ip (P * indepUpd Fp ϱ ω t) (P * Q ϱ (Nl ω)) := by
      intro ω
      rw [Matrix.mul_sub, zr_ip_sub_right]
      ring
    rw [e1]
    simp_rw [e2]
    rw [integral_add iXV iXZ, hzero, add_zero]
  rw [hT]
  refine (zr_int_cs (μ := μ) hUm hVm (4 * ρ) hUb hVb).trans ?_
  have hconst : ∫ _ω, ρ ∂μ = ρ := by simp
  have hU1 : ∫ ω, zr_ip (P * indepUpd Fp ϱ ω t) (P * indepUpd Fp ϱ ω t) ∂μ ≤ ρ := by
    calc _ ≤ ∫ _ω, ρ ∂μ := integral_mono (zr_int_ip (μ := μ) hUm hUm (4 * ρ) hUb hUb)
            (integrable_const _) fun ω => by
              have := hQb (def_app_vol_product Fp ω t)
              unfold indepUpd; exact this
      _ = ρ := hconst
  -- the second moment of the buffer
  have hsw : 0 < sPow Fp.β 2 := by
    rw [sPow_two hβ0 hβ1]; exact div_pos (by linarith) (by linarith)
  have hmom := def_app_vol_product_moment Fp t
  have hrhs : 0 < sPow Fp.β 2 / (B : ℝ) ^ 2 * Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin := by
    rw [mul_assoc]; exact mul_pos (div_pos hsw (by positivity)) htr
  have hfroInt : Integrable (fun ω => fro (def_app_vol_product Fp ω t) ^ 2) μ := by
    by_contra h
    have h0 := integral_undef h
    rw [h0, mul_zero] at hmom
    linarith
  have hM2 : ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2 ∂μ = (B : ℝ) * (sPow Fp.β 2 / (B : ℝ) ^ 2 *
      Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin) := by
    calc _ = (B : ℝ) * ((B : ℝ)⁻¹ * ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2 ∂μ) := by
          field_simp
      _ = _ := by rw [hmom]
  have hae : ∀ᵐ ω ∂μ, zr_ip (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω)))
      (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) ≤
        ϱ⁻¹ * Fp.β ^ (2 * ℓ) * fro (def_app_vol_product Fp ω t) ^ 2 := by
    filter_upwards [hdec] with ω hω
    have hY : indepUpd Fp ϱ ω (t + (ℓ : ℤ)) =
        Q ϱ (Nl ω + Fp.β ^ ℓ • def_app_vol_product Fp ω t) := by
      unfold indepUpd; rw [hω]
    have h1 := zr_proj_le P hs hi (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))
    have h2 := Muon.Setup.lem_app_setup_filter_iii ϱ hϱ
      (Nl ω + Fp.β ^ ℓ • def_app_vol_product Fp ω t) (Nl ω)
    rw [← hY, add_sub_cancel_left] at h2
    have hfn : 0 ≤ fro (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω)) := Real.sqrt_nonneg _
    have h3 := pow_le_pow_left₀ hfn h2 2
    rw [mul_pow, zr_fro_sq, zr_fro_sq, zr_ip_smul_left, zr_ip_smul_right] at h3
    have h4 : (ϱ ^ (-(1 / 2 : ℝ))) ^ 2 = ϱ⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hϱ.le]
      norm_num
      exact Real.rpow_neg_one ϱ
    rw [h4, ← zr_fro_sq] at h3
    calc _ ≤ _ := h1
      _ = fro (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω)) ^ 2 := (zr_fro_sq _).symm
      _ ≤ _ := h3
      _ = _ := by rw [pow_mul', zr_fro_sq]; ring
  have hV1 : ∫ ω, zr_ip (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω)))
      (P * (indepUpd Fp ϱ ω (t + (ℓ : ℤ)) - Q ϱ (Nl ω))) ∂μ ≤
      ϱ⁻¹ * Fp.β ^ (2 * ℓ) * ((B : ℝ) * (sPow Fp.β 2 / (B : ℝ) ^ 2 *
        Matrix.trace Fp.C.Sout * Matrix.trace Fp.C.Sin)) := by
    calc _ ≤ ∫ ω, ϱ⁻¹ * Fp.β ^ (2 * ℓ) * fro (def_app_vol_product Fp ω t) ^ 2 ∂μ :=
          integral_mono_ae (zr_int_ip (μ := μ) hVm hVm (4 * ρ) hVb hVb)
            (hfroInt.const_mul _) hae
      _ = ϱ⁻¹ * Fp.β ^ (2 * ℓ) * ∫ ω, fro (def_app_vol_product Fp ω t) ^ 2 ∂μ :=
          integral_const_mul _ _
      _ = _ := by rw [hM2]
  exact mul_le_mul hU1 hV1 (integral_nonneg fun ω => zr_ip_self_nonneg _) hρ0


end ZrEnv


section ZrSetup2
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_setup' {N B : ℕ} (hB : 0 < B) (μ : Fin N → ℝ)
    (hpos : ∀ i, 0 < μ i) {β γstar CSig : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    ∃ (Fp : Muon.Setup.FrozenParams N N B) (S : Muon.Setup.SpectralData Fp.C),
      Fp.β = β ∧ S.μ = μ ∧ S.lam = (fun _ => (1 : ℝ)) ∧
      Muon.Volatility.SizeFin Fp.C B γstar CSig ∧
      Fp.C.Sout = Matrix.diagonal μ ∧ Fp.C.Sin = 1 := by
  classical
  let C : Covariances N N :=
    { Sout := Matrix.diagonal μ
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun j => (hpos j).le)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams N N B :=
    { C := C
      A := Pi.single i (Pi.single i 1)
      hA := by simp [fro, Pi.single_apply, ite_apply]
      β := β
      hβ := ⟨hβ0.le, hβ1⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := μ
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro j; ext k
        by_cases h : k = j <;> simp [Fp, C, Matrix.mulVec, dotProduct,
          Matrix.diagonal, Matrix.one_apply, h]
      eigIn := by intro j; simp [Fp, C] }
  refine ⟨Fp, S, rfl, rfl, rfl, ⟨?_, ?_, ?_⟩, rfl, Matrix.diagonal_one⟩
  · simpa [gammaOf, div_le_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)] using hγ
  · exact zr_diagonal_bound μ CSig (by linarith) (fun j => by
      rw [abs_of_pos (hpos j)]; exact hμC j)
  · exact zr_diagonal_bound (fun _ => 1) CSig (by linarith) (fun _ => by simpa using hC1)


private lemma zr_trace_repl {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (N : ℕ) :
    Matrix.trace (replMat S N) = N * Matrix.trace S := by
  rw [Matrix.trace, Matrix.trace]
  simp only [Matrix.diag]
  rw [← Equiv.sum_comp (replIdx m N)]
  simp [zr_replMat_apply, Fintype.sum_prod_type_right, Finset.mul_sum]

end ZrSetup2

section ZrModel
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_sum_repl {m : ℕ} (N : ℕ) (a : Fin m → ℝ) :
    ∑ j, replVec N a j = N * ∑ j, a j := by
  rw [← Equiv.sum_comp (replIdx m N)]
  simp [replVec, Fintype.sum_prod_type_right]

private lemma zr_sqrt_norm (n A : ℝ) (hn : 0 < n) :
    n⁻¹ * (Real.sqrt n * Real.sqrt (n - A)) = Real.sqrt (1 - n⁻¹ * A) := by
  have h1 : 1 - n⁻¹ * A = n⁻¹ * (n - A) := by field_simp
  rw [h1, Real.sqrt_mul (inv_nonneg.2 hn.le), Real.sqrt_inv]
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn.le
  have key : n⁻¹ * Real.sqrt n = (Real.sqrt n)⁻¹ := by
    nth_rewrite 1 [← hss]
    field_simp
  calc n⁻¹ * (Real.sqrt n * Real.sqrt (n - A)) = (n⁻¹ * Real.sqrt n) * Real.sqrt (n - A) := by ring
    _ = _ := by rw [key]

private lemma zr_model (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {ϱlo ϱhi : ℝ} (hlo : 0 < ϱlo) (hlh : ϱlo ≤ ϱhi) :
    ∃ c : ℕ → ℝ → ℝ → ℤ → ℤ → ℝ,
      (∀ k ϱ ϱ' t t', ϱ ∈ Set.Icc ϱlo ϱhi → ϱ' ∈ Set.Icc ϱlo ϱhi →
        c k ϱ ϱ' t t' ^ 2 ≤ c k ϱ ϱ t t * c k ϱ' ϱ' t' t') ∧
      (∀ k ϱ t, ϱ ∈ Set.Icc ϱlo ϱhi → 0 ≤ c k ϱ ϱ t t ∧ c k ϱ ϱ t t ≤ 1) ∧
      (∀ k η ϱ t t', η ∈ Set.Icc ϱlo ϱhi → ϱ ∈ Set.Icc ϱlo ϱhi → η ≤ ϱ →
        |c k η η t t' - c k ϱ ϱ t t'| ≤
          Real.sqrt (1 - c k ϱ ϱ t t) + Real.sqrt (1 - c k ϱ ϱ t' t')) ∧
      (∀ ϱ ϱ', ϱ ∈ Set.Icc ϱlo ϱhi → ϱ' ∈ Set.Icc ϱlo ϱhi → ∀ (t : ℤ) (ℓ : ℕ),
        Tendsto (fun k => c k ϱ ϱ' t (t + (ℓ : ℤ))) atTop
          (𝓝 (lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ'))) ∧
      (∀ k ϱ t (ℓ : ℕ), ϱ ∈ Set.Icc ϱlo ϱhi →
        c k ϱ ϱ t (t + (ℓ : ℤ)) ^ 2 ≤
          sPow β 2 * gammaOf N B * (∑ j, μ j) * (β ^ (2 * ℓ) / ϱ)) := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS, hSout, hSin⟩ := zr_setup' hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hR⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig ϱlo ϱhi hC1 hS hN hN ⟨hlo, hlh⟩
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hR
  subst rm rn rB rγ rC rβ rlo rhi
  have hCov : ∀ k, (rF k).C = replCov Fp.C (k + 1) := fun k => eq_of_heq (hR k).1
  have hspec : ∀ k, ∃ Sp : SpectralData (rF k).C,
      Sp.μ = replVec (k + 1) S.μ ∧ Sp.lam = replVec (k + 1) S.lam := by
    intro k
    rw [hCov k]
    obtain ⟨Sp, -, -, hμ, hl⟩ := zr_exists_replSpec Fp.C S (k + 1)
    exact ⟨Sp, hμ, hl⟩
  choose Sp hSpμ hSpl using hspec
  have hSize : SizeSeq (B := fun k => (k + 1) * B) (fun k => (rF k).C) γstar CSig
      rprop.γout rprop.γin :=
    ⟨fun k => ⟨rdims k, rnormO k, rnormI k⟩, rprop.B_top, rprop.ratio_in, rprop.ratio_out⟩
  have hbeta : ∀ k, (rF k).β ≤ β := fun k => by rw [rhβ k, hβ]
  have clos := fun ℓ : ℕ => by
    first
    | exact thm_app_vol_lag_kernel_closure_indep cert γstar CSig rprop.γout rprop.γin
        hC1 ϱlo ϱhi ⟨hlo, hlh⟩ (fun k => (k + 1) * N) (fun k => (k + 1) * N)
        (fun k => (k + 1) * B) rF Sp hSize β hβ1 hbeta ℓ ∅ isCompact_empty (Set.empty_subset _)
    | exact thm_app_vol_lag_kernel_closure_indep cert γstar CSig rprop.γout rprop.γin
        hC1 ϱlo ϱhi ⟨hlo, hlh⟩ (fun k => (k + 1) * N) (fun k => (k + 1) * N)
        (fun k => (k + 1) * B) rF Sp hSize ℓ ∅ isCompact_empty (Set.empty_subset _)
  -- the replicated tests
  obtain ⟨Fd, hFd⟩ : ∃ Fd : ∀ k, Fin ((k + 1) * N) → ℝ,
      ∀ k, Fd k = replVec (k + 1) (Pi.single i (1 : ℝ) : Fin N → ℝ) := ⟨fun k => _, fun _ => rfl⟩
  obtain ⟨Gd, hGd⟩ : ∃ Gd : ∀ k, Fin ((k + 1) * N) → ℝ,
      ∀ k, Gd k = replVec (k + 1) (fun _ : Fin N => (1 : ℝ)) := ⟨fun k => _, fun _ => rfl⟩
  have hd01 : ∀ k j, Fd k j = 0 ∨ Fd k j = 1 := by
    intro k j
    rw [hFd]
    simp only [replVec, Pi.single_apply]
    split_ifs <;> simp
  have hGone : ∀ k j, Gd k j = 1 := by
    intro k j
    rw [hGd]
    rfl
  have hGm : ∀ k, (Sp k).vIn * Matrix.diagonal (Gd k) * (Sp k).vInᵀ = 1 := by
    intro k
    have h1 : Matrix.diagonal (Gd k) = 1 := by
      have : Gd k = fun _ => 1 := funext (hGone k)
      rw [this]
      exact Matrix.diagonal_one
    rw [h1, Matrix.mul_one]
    exact mul_eq_one_comm.mp (Sp k).hvIn
  have hsumF : ∀ k, ∑ j, Fd k j = ((k : ℝ) + 1) := by
    intro k
    rw [hFd, zr_sum_repl]
    simp
  obtain ⟨P, hP⟩ : ∃ P : ∀ k, Mat ((k + 1) * N) ((k + 1) * N),
      ∀ k, P k = (Sp k).uOut * Matrix.diagonal (Fd k) * (Sp k).uOutᵀ := ⟨fun k => _, fun _ => rfl⟩
  have hPf : ∀ k, (P k)ᵀ = P k ∧ P k * P k = P k ∧ zr_ip (P k) (P k) = (k : ℝ) + 1 := by
    intro k
    obtain ⟨h1, h2, h3⟩ := zr_proj_facts (Sp k).uOut (Sp k).huOut (Fd k) (hd01 k)
    rw [hP]
    exact ⟨h1, h2, h3.trans (hsumF k)⟩
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ → ℝ → ℤ → ℤ → ℝ, ∀ k ϱ ϱ' t t', T k ϱ ϱ' t t' =
      ∫ ω, Matrix.trace (P k * indepUpd (rF k) ϱ ω t * (1 : Mat ((k + 1) * N) ((k + 1) * N)) *
        (indepUpd (rF k) ϱ' ω t')ᵀ) ∂(indepSpaceLaw ((k + 1) * N) ((k + 1) * N) ((k + 1) * B)) :=
    ⟨fun k ϱ ϱ' t t' => _, fun _ _ _ _ _ => rfl⟩
  have hfin := fun k => zr_fin (rF k) (P k) (hPf k).1 (hPf k).2.1 (T k) (hT k)
  have hnpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  refine ⟨fun k ϱ ϱ' t t' => ((k : ℝ) + 1)⁻¹ * T k ϱ ϱ' t t', ?_, ?_, ?_, ?_, ?_⟩
  · intro k ϱ ϱ' t t' hϱ hϱ'
    have h := (hfin k).1 ϱ ϱ' t t' (hlo.trans_le hϱ.1) (hlo.trans_le hϱ'.1)
    have hn := inv_nonneg.2 (hnpos k).le
    calc (((k : ℝ) + 1)⁻¹ * T k ϱ ϱ' t t') ^ 2
        = (((k : ℝ) + 1)⁻¹) ^ 2 * T k ϱ ϱ' t t' ^ 2 := by ring
      _ ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (T k ϱ ϱ t t * T k ϱ' ϱ' t' t') :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by ring
  · intro k ϱ t hϱ
    obtain ⟨h0, h1⟩ := (hfin k).2.1 ϱ t (hlo.trans_le hϱ.1)
    rw [(hPf k).2.2] at h1
    refine ⟨mul_nonneg (inv_nonneg.2 (hnpos k).le) h0, ?_⟩
    calc ((k : ℝ) + 1)⁻¹ * T k ϱ ϱ t t ≤ ((k : ℝ) + 1)⁻¹ * ((k : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 (hnpos k).le)
      _ = 1 := inv_mul_cancel₀ (hnpos k).ne'
  · intro k η ϱ t t' hη hϱ hηϱ
    have h := (hfin k).2.2 η ϱ t t' (hlo.trans_le hη.1) hηϱ
    rw [(hPf k).2.2] at h
    have hn := hnpos k
    have e : ((k : ℝ) + 1)⁻¹ * T k η η t t' - ((k : ℝ) + 1)⁻¹ * T k ϱ ϱ t t' =
        ((k : ℝ) + 1)⁻¹ * (T k η η t t' - T k ϱ ϱ t t') := by ring
    rw [e, abs_mul, abs_of_pos (inv_pos.2 hn), ← zr_sqrt_norm _ _ hn, ← zr_sqrt_norm _ _ hn]
    calc ((k : ℝ) + 1)⁻¹ * |T k η η t t' - T k ϱ ϱ t t'|
        ≤ ((k : ℝ) + 1)⁻¹ * (Real.sqrt ((k : ℝ) + 1) * (Real.sqrt ((k : ℝ) + 1 - T k ϱ ϱ t t) +
          Real.sqrt ((k : ℝ) + 1 - T k ϱ ϱ t' t'))) :=
          mul_le_mul_of_nonneg_left h (inv_nonneg.2 hn.le)
      _ = _ := by ring
  · intro ϱ ϱ' hϱ hϱ' t ℓ
    have hϱ0 : 0 < ϱ := hlo.trans_le hϱ.1
    have hϱ0' : 0 < ϱ' := hlo.trans_le hϱ'.1
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
    have h := (clos ℓ).2 (ε / (2 * B)) (by positivity)
    filter_upwards [h] with k hk
    have hk' := hk t ϱ hϱ ϱ' hϱ' (Fd k) (Gd k) (P k) ((Sp k).vIn * Matrix.diagonal (Gd k) * (Sp k).vInᵀ)
      (hP k) rfl (by rw [hP]; exact zr_opNorm_conj_diag _ (Sp k).huOut _ (fun j => by
        rcases hd01 k j with h | h <;> simp [h]))
      (zr_opNorm_conj_diag _ (Sp k).hvIn _ (fun j => by simp [hGone k j]))
    rw [hGm k] at hk'
    have hrepl := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hC1 ℓ
      (omegaF ϱ) (omegaF ϱ') (lem_app_vol_sharp_ii hϱ0 hϱ0).2.1
      (lem_app_vol_sharp_ii hϱ0' hϱ0').2.1).2.2.2.2.2 (k + 1) (Nat.succ_pos k)
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
    rw [rhβ k, hSpμ k, hSpl k, hFd, hGd, hrepl, hβ, hμ, hlam] at hk'
    rw [Real.dist_eq]
    have hTk := hT k ϱ ϱ' t (t + (ℓ : ℤ))
    simp only [lagRowBar]
    set L := lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ') with hL
    rw [← hTk] at hk'
    have hn := hnpos k
    have e : ((k : ℝ) + 1)⁻¹ * T k ϱ ϱ' t (t + (ℓ : ℤ)) - (B : ℝ) * L =
        (B : ℝ) * ((((k + 1) * B : ℕ) : ℝ)⁻¹ * T k ϱ ϱ' t (t + (ℓ : ℤ)) - L) := by
      push_cast
      field_simp
    rw [e, abs_mul, abs_of_pos hBpos]
    calc (B : ℝ) * |(((k + 1) * B : ℕ) : ℝ)⁻¹ * T k ϱ ϱ' t (t + (ℓ : ℤ)) - L|
        ≤ (B : ℝ) * (ε / (2 * B)) := mul_le_mul_of_nonneg_left hk' hBpos.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · intro k ϱ t ℓ hϱ
    have hϱ0 : 0 < ϱ := hlo.trans_le hϱ.1
    have hn := hnpos k
    have hsumpos : 0 < ∑ j, μ j := Finset.sum_pos (fun j _ => hpos j) ⟨i, Finset.mem_univ i⟩
    have htrO : Matrix.trace (rF k).C.Sout = ((k : ℝ) + 1) * ∑ j, μ j := by
      rw [hCov k]
      change Matrix.trace (replMat Fp.C.Sout (k + 1)) = _
      rw [zr_trace_repl, hSout, Matrix.trace_diagonal]
      push_cast
      ring
    have htrI : Matrix.trace (rF k).C.Sin = ((k : ℝ) + 1) * N := by
      rw [hCov k]
      change Matrix.trace (replMat Fp.C.Sin (k + 1)) = _
      rw [zr_trace_repl, hSin, Matrix.trace_one]
      simp
    have hpos' : 0 < Matrix.trace (rF k).C.Sout * Matrix.trace (rF k).C.Sin := by
      rw [htrO, htrI]
      have : (0 : ℝ) < N := Nat.cast_pos.mpr hN
      positivity
    have h := zr_env (rF k) (P k) (hPf k).1 (hPf k).2.1 hϱ0 t ℓ hpos'
    rw [(hPf k).2.2, htrO, htrI, rhβ k, hβ, ← hT k ϱ ϱ t (t + (ℓ : ℤ))] at h
    have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
    calc (((k : ℝ) + 1)⁻¹ * T k ϱ ϱ t (t + (ℓ : ℤ))) ^ 2
        = (((k : ℝ) + 1)⁻¹) ^ 2 * T k ϱ ϱ t (t + (ℓ : ℤ)) ^ 2 := by ring
      _ ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (((k : ℝ) + 1) * (ϱ⁻¹ * β ^ (2 * ℓ) *
          ((((k + 1) * B : ℕ) : ℝ) * (sPow β 2 / ((((k + 1) * B : ℕ) : ℝ)) ^ 2 *
            (((k : ℝ) + 1) * ∑ j, μ j) * (((k : ℝ) + 1) * N))))) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = _ := by
          unfold gammaOf
          push_cast
          field_simp

end ZrModel

section ZrRow
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_diag_diracs {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : A.IsHermitian) (d : Fin N → ℝ) (hd : A = Matrix.diagonal d) :
    ∑ i, Measure.dirac (hA.eigenvalues i) = ∑ i, Measure.dirac (d i) := by
  have hr := hA.roots_charpoly_eq_eigenvalues
  have hp : A.charpoly.roots = (Matrix.diagonal d).charpoly.roots :=
    congrArg (fun M => M.charpoly.roots) hd
  rw [hp, Matrix.charpoly_diagonal, Polynomial.roots_prod] at hr
  · have he : Multiset.map hA.eigenvalues Finset.univ.val = Multiset.map d Finset.univ.val := by
      simpa using hr.symm
    have h := congrArg (fun z : Multiset ℝ => (z.map Measure.dirac).sum) he
    simpa [Finset.sum_eq_multiset_sum, Function.comp_def] using h
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

private lemma zr_nuOut {N B : ℕ} (C : Muon.Covariances N N) (μ : Fin N → ℝ)
    (hB : 0 < B) (hC : C.Sout = Matrix.diagonal μ) :
    Muon.nuOut C B = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i) := by
  unfold Muon.nuOut
  rw [zr_diag_diracs C.Sout C.psdOut.isHermitian μ hC]
  congr 1
  simp [ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma zr_nuIn {N B : ℕ} (C : Muon.Covariances N N) (hB : 0 < B)
    (hC : C.Sin = 1) :
    Muon.nuIn C B = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := by
  unfold Muon.nuIn
  rw [zr_diag_diracs C.Sin C.psdIn.isHermitian (fun _ => 1) (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul]
  congr 1
  simp [gammaOf, div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma zr_row0_eq (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      volraw β ν ν' (μ i) ϱ := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS, hSout, hSin⟩ :=
    zr_setup' hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  have hz := Muon.Volatility.thm_app_vol_mode_kernels_iv_zero_lag cert γstar CSig Fp S hS hC1 hSin
    ν ν' (by rw [hν, zr_nuOut Fp.C μ hB hSout]) (by rw [hν', zr_nuIn Fp.C hB hSin]) i ϱ hϱ
  simp only [hβ, hμ, hlam] at hz
  exact hz

private lemma zr_cs_row (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) (ℓ : ℕ) :
    lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ ^ 2 ≤
      lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ *
        lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ := by
  obtain ⟨c, h1, -, -, h4, -⟩ := zr_model cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i hϱ le_rfl
  have hI : ϱ ∈ Set.Icc ϱ ϱ := ⟨le_rfl, le_rfl⟩
  have a1 := h4 ϱ ϱ hI hI 0 ℓ
  have a2 := h4 ϱ ϱ hI hI 0 0
  have a3 := h4 ϱ ϱ hI hI ((0 : ℤ) + (ℓ : ℤ)) 0
  simp only [Nat.cast_zero, add_zero, zero_add] at a1 a2 a3
  exact le_of_tendsto_of_tendsto' (a1.pow 2) (a2.mul a3) fun k => by
    simpa using h1 k ϱ ϱ 0 (ℓ : ℤ) hI hI

end ZrRow

/-- `lem:app-pl-two-ridge`, first bound (`eqn:app-pl-two-ridge`, first display), snapshot `cr-2026-10-23`.
Declaration of record, part (i): for `0 < η ≤ ϱ` and every `ℓ ≥ 0`,
`|C̄_{i,ℓ}(η) − C̄_{i,ℓ}(ϱ)| ≤ 2 √(1 − volraw_i(ϱ))`. LaTeX, verbatim:

\begin{lemma}[Two ridges and the lag envelope]\label{lem:app-pl-two-ridge}
For $0<\eta\le\ridge$ and every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-two-ridge}
\abs{\overline C_{i,\ell}(\eta)-\overline C_{i,\ell}(\ridge)}\le2\sqrt{1-\volraw_i(\ridge)},\qquad
\abs{\overline C_{i,\ell}(\ridge)}\le1,
\end{equation}
and for every $\ell\ge1$,
\begin{equation}\label{eqn:app-pl-envelope}
\abs{\overline C_{i,\ell}(\ridge)}\le\frac{A_N\,\bmom^\ell}{\sqrt\ridge}.
\end{equation}
\end{lemma}
-/
theorem lem_app_pl_two_ridge_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (i : Fin N) :
    plRowExists cert γstar CSig β B μ i ∧
    ∀ (η ϱ : ℝ) (ℓ : ℕ), 0 < η → η ≤ ϱ →
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i η η -
          lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
        2 * Real.sqrt (1 - volraw β ν ν' (μ i) ϱ) := by
  refine ⟨zr_row_exists cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i, ?_⟩
  intro η ϱ ℓ hη hηϱ
  have hϱ : 0 < ϱ := hη.trans_le hηϱ
  obtain ⟨c, -, -, h2, h4, -⟩ :=
    zr_model cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i hη hηϱ
  have hIη : η ∈ Set.Icc η ϱ := ⟨le_rfl, hηϱ⟩
  have hIϱ : ϱ ∈ Set.Icc η ϱ := ⟨hηϱ, le_rfl⟩
  have b1 := h4 η η hIη hIη 0 ℓ
  have b2 := h4 ϱ ϱ hIϱ hIϱ 0 ℓ
  have b3 := h4 ϱ ϱ hIϱ hIϱ 0 0
  have b4 := h4 ϱ ϱ hIϱ hIϱ ((0 : ℤ) + (ℓ : ℤ)) 0
  simp only [Nat.cast_zero, add_zero, zero_add] at b1 b2 b3 b4
  have e0 := zr_row0_eq cert γstar CSig hB μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' i hϱ
  have lim := (((tendsto_const_nhds (x := (1 : ℝ))).sub b3).sqrt).add
    (((tendsto_const_nhds (x := (1 : ℝ))).sub b4).sqrt)
  have key := le_of_tendsto_of_tendsto' ((b1.sub b2).abs) lim fun k => by
    simpa using h2 k η ϱ 0 (ℓ : ℤ) hIη hIϱ hηϱ
  rw [e0] at key
  linarith

/-- `lem:app-pl-two-ridge`, second bound (`eqn:app-pl-two-ridge`, second display), snapshot `cr-2026-10-23`.
Declaration of record, part (ii): `|C̄_{i,ℓ}(ϱ)| ≤ 1` for every `ℓ ≥ 0` and `ϱ > 0`. LaTeX, verbatim:

\begin{lemma}[Two ridges and the lag envelope]\label{lem:app-pl-two-ridge}
For $0<\eta\le\ridge$ and every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-two-ridge}
\abs{\overline C_{i,\ell}(\eta)-\overline C_{i,\ell}(\ridge)}\le2\sqrt{1-\volraw_i(\ridge)},\qquad
\abs{\overline C_{i,\ell}(\ridge)}\le1,
\end{equation}
and for every $\ell\ge1$,
\begin{equation}\label{eqn:app-pl-envelope}
\abs{\overline C_{i,\ell}(\ridge)}\le\frac{A_N\,\bmom^\ell}{\sqrt\ridge}.
\end{equation}
\end{lemma}
-/
theorem lem_app_pl_two_ridge_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    plRowExists cert γstar CSig β B μ i ∧
    ∀ (ϱ : ℝ) (ℓ : ℕ), 0 < ϱ →
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤ 1 := by
  refine ⟨zr_row_exists cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i, ?_⟩
  intro ϱ ℓ hϱ
  have h := zr_cs_row cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i hϱ ℓ
  have h0 := zr_zero_lag_bound cert γstar CSig hB μ hpos hβ0 hβ1 hγ hμC hC1 i hϱ
  rw [← sq] at h
  exact (sq_le_sq.mp h).trans h0

/-- `lem:app-pl-two-ridge`, envelope (`eqn:app-pl-envelope`), snapshot `cr-2026-10-23`. Declaration of record,
part (iii): for every `ℓ ≥ 1` and `ϱ > 0`, `|C̄_{i,ℓ}(ϱ)| ≤ A_N β^ℓ / √ϱ`. LaTeX, verbatim:

\begin{lemma}[Two ridges and the lag envelope]\label{lem:app-pl-two-ridge}
For $0<\eta\le\ridge$ and every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-two-ridge}
\abs{\overline C_{i,\ell}(\eta)-\overline C_{i,\ell}(\ridge)}\le2\sqrt{1-\volraw_i(\ridge)},\qquad
\abs{\overline C_{i,\ell}(\ridge)}\le1,
\end{equation}
and for every $\ell\ge1$,
\begin{equation}\label{eqn:app-pl-envelope}
\abs{\overline C_{i,\ell}(\ridge)}\le\frac{A_N\,\bmom^\ell}{\sqrt\ridge}.
\end{equation}
\end{lemma}
-/
theorem lem_app_pl_two_ridge_iii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    plRowExists cert γstar CSig β B μ i ∧
    ∀ (ϱ : ℝ) (ℓ : ℕ), 0 < ϱ → 1 ≤ ℓ →
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
        plAN β B μ * β ^ ℓ / Real.sqrt ϱ := by
  refine ⟨zr_row_exists cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i, ?_⟩
  intro ϱ ℓ hϱ hℓ
  obtain ⟨c, -, -, -, h4, h5⟩ :=
    zr_model cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i hϱ le_rfl
  have hI : ϱ ∈ Set.Icc ϱ ϱ := ⟨le_rfl, le_rfl⟩
  have a1 := h4 ϱ ϱ hI hI 0 ℓ
  have hsq : lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ ^ 2 ≤
      sPow β 2 * gammaOf N B * (∑ j, μ j) * (β ^ (2 * ℓ) / ϱ) :=
    le_of_tendsto_of_tendsto' (a1.pow 2) tendsto_const_nhds fun k => by
      simpa using h5 k ϱ 0 ℓ hI
  have hsw : 0 < sPow β 2 := by
    rw [sPow_two hβ0.le hβ1]; exact div_pos (by linarith) (by linarith)
  have hγ0 : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
  have hsum0 : 0 ≤ ∑ j, μ j := Finset.sum_nonneg fun j _ => (hpos j).le
  have hK0 : 0 ≤ sPow β 2 * gammaOf N B * (∑ j, μ j) := by positivity
  have hAN : plAN β B μ ^ 2 = 2 * gammaOf N B * sPow β 2 * ∑ j, μ j := by
    unfold plAN
    rw [Real.sq_sqrt (by positivity)]
  have hb0 : 0 ≤ plAN β B μ * β ^ ℓ / Real.sqrt ϱ := by
    have : 0 ≤ plAN β B μ := Real.sqrt_nonneg _
    positivity
  have hb2 : (plAN β B μ * β ^ ℓ / Real.sqrt ϱ) ^ 2 =
      2 * gammaOf N B * sPow β 2 * (∑ j, μ j) * (β ^ (2 * ℓ) / ϱ) := by
    rw [div_pow, mul_pow, hAN, Real.sq_sqrt hϱ.le, pow_mul']
    ring
  have hfin : lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ ^ 2 ≤
      (plAN β B μ * β ^ ℓ / Real.sqrt ϱ) ^ 2 := by
    refine hsq.trans ?_
    rw [hb2]
    have : 0 ≤ sPow β 2 * gammaOf N B * (∑ j, μ j) * (β ^ (2 * ℓ) / ϱ) := by positivity
    nlinarith
  have := sq_le_sq.mp hfin
  rwa [abs_of_nonneg hb0] at this

private lemma zr_mOf_spec {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {s : ℝ} (hs : 0 < s) :
    mOf β B μ s ∈ Ioo 0 (gammaOf N B) ∧ sN β B μ (mOf β B μ s) = s := by
  have hbij := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨x, hx, hfx⟩ := hbij.surjOn (show s ∈ Ioi (0 : ℝ) from hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨x, hx, hfx⟩
  unfold mOf
  exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩

private lemma zr_tendsto_of_two_ridge (f : ℝ → ℝ) (z K : ℝ) (hz : 0 < z)
    (h : ∀ η ϱ : ℝ, 0 < η → η ≤ ϱ → ϱ ≤ z →
      |f η - f ϱ| ≤ K * ϱ ^ ((1 : ℝ) / 4)) :
    Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (limUnder (𝓝[>] (0 : ℝ)) f)) ∧
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ z →
        |limUnder (𝓝[>] (0 : ℝ)) f - f ϱ| ≤ K * ϱ ^ ((1 : ℝ) / 4) := by
  have hp : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / 4)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hs : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) := by
      rw [nhdsWithin]
      exact inf_le_left
    simpa using
      (Real.continuousAt_rpow_const 0 ((1 : ℝ) / 4) (Or.inr (by norm_num))).tendsto.mono_left hs
  have hK : Tendsto (fun x : ℝ => K * x ^ ((1 : ℝ) / 4)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hp
  have hc : Cauchy (Filter.map f (𝓝[>] (0 : ℝ))) := by
    rw [Metric.cauchy_iff]
    refine ⟨Filter.map_neBot, ?_⟩
    intro ε hε
    have heps : ∀ᶠ x in 𝓝[>] (0 : ℝ), K * x ^ ((1 : ℝ) / 4) < ε :=
      hK.eventually (Iio_mem_nhds hε)
    have hs : {x : ℝ | 0 < x ∧ x < z ∧ K * x ^ ((1 : ℝ) / 4) < ε} ∈ 𝓝[>] (0 : ℝ) := by
      filter_upwards [Ioo_mem_nhdsGT hz, heps] with x hx hxe
      exact ⟨hx.1, hx.2, hxe⟩
    refine ⟨f '' {x : ℝ | 0 < x ∧ x < z ∧ K * x ^ ((1 : ℝ) / 4) < ε},
      image_mem_map hs, ?_⟩
    intro x hx y hy
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    rw [Real.dist_eq]
    by_cases hab : a ≤ b
    · exact lt_of_le_of_lt (h a b ha.1 hab hb.2.1.le) hb.2.2
    · rw [abs_sub_comm]
      exact lt_of_le_of_lt (h b a hb.1 (le_of_not_ge hab) ha.2.1.le) ha.2.2
  obtain ⟨L, hL⟩ := cauchy_map_iff_exists_tendsto.mp hc
  have hlim := tendsto_nhds_limUnder ⟨L, hL⟩
  refine ⟨hlim, ?_⟩
  intro ϱ hϱ hϱz
  refine le_of_tendsto (hlim.sub tendsto_const_nhds |>.abs) ?_
  filter_upwards [Ioo_mem_nhdsGT hϱ] with η hη
  exact h η ϱ hη.1 hη.2.le hϱz

private lemma zr_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (Real.sqrt x) = x ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hx]
  norm_num

private lemma zr_scale_id (A D z b : ℝ) (hz : 0 < z) (hb : 0 < b) :
    A * b ^ 3 / Real.sqrt (z * b ^ 4) +
        2 * Real.sqrt D * (z * b ^ 4) ^ ((1 : ℝ) / 4) =
      (A * z ^ (-(1 : ℝ) / 2) + 2 * Real.sqrt D * z ^ ((1 : ℝ) / 4)) * b := by
  have hsz : 0 < Real.sqrt z := Real.sqrt_pos.2 hz
  have hsqrt : Real.sqrt (z * b ^ 4) = Real.sqrt z * b ^ 2 := by
    rw [Real.sqrt_mul hz.le]
    have : Real.sqrt (b ^ 4) = b ^ 2 := by
      rw [show b ^ 4 = (b ^ 2) ^ 2 by ring, Real.sqrt_sq_eq_abs, abs_of_pos (pow_pos hb 2)]
    rw [this]
  have hrpow : (z * b ^ 4) ^ ((1 : ℝ) / 4) = z ^ ((1 : ℝ) / 4) * b := by
    rw [Real.mul_rpow hz.le (pow_nonneg hb.le 4)]
    have : (b ^ 4) ^ ((1 : ℝ) / 4) = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
      norm_num
    rw [this]
  have hneg : z ^ (-(1 : ℝ) / 2) = (Real.sqrt z)⁻¹ := by
    rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg hz.le]
  rw [hsqrt, hrpow, hneg]
  field_simp

private lemma zr_tsum_split_bound (a b : ℕ → ℝ) (H : ℕ) (δ E q : ℝ)
    (ha : Summable a) (hb : Summable b) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hhead : ∀ k, k < H → |a k - b k| ≤ δ)
    (htail : ∀ k, |a (k + H) - b (k + H)| ≤ 2 * E * q ^ (k + H + 1)) :
    |∑' k, a k - ∑' k, b k| ≤ (H : ℝ) * δ + 2 * E * q ^ (H + 1) / (1 - q) := by
  have hd : Summable (fun k => a k - b k) := ha.sub hb
  have hda : Summable (fun k => |a k - b k|) := by
    simpa only [Real.norm_eq_abs] using hd.norm
  have hdat : Summable (fun k => |a (k + H) - b (k + H)|) :=
    hda.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hdatnorm : Summable (fun k => ‖a (k + H) - b (k + H)‖) := by
    simpa only [Real.norm_eq_abs] using hdat
  have hnormtail : |∑' k, (a (k + H) - b (k + H))| ≤
      ∑' k, |a (k + H) - b (k + H)| := by
    have ht := norm_tsum_le_tsum_norm hdatnorm
    simpa only [Real.norm_eq_abs] using ht
  have hg := summable_geometric_of_lt_one hq0 hq1
  have hm : Summable (fun k : ℕ => 2 * E * q ^ (k + H + 1)) := by
    have := hg.mul_left (2 * E * q ^ (H + 1))
    convert this using 1
    funext k
    rw [pow_add]
    ring
  have hmt : ∑' k : ℕ, 2 * E * q ^ (k + H + 1) =
      2 * E * q ^ (H + 1) / (1 - q) := by
    rw [show (fun k : ℕ => 2 * E * q ^ (k + H + 1)) =
        fun k => (2 * E * q ^ (H + 1)) * q ^ k by
      funext k
      rw [pow_add]
      ring, tsum_mul_left, tsum_geometric_of_lt_one hq0 hq1]
    rw [div_eq_mul_inv]
  rw [← ha.tsum_sub hb, ← hd.sum_add_tsum_nat_add H]
  calc
    |∑ k ∈ Finset.range H, (a k - b k) + ∑' k, (a (k + H) - b (k + H))| ≤
        |∑ k ∈ Finset.range H, (a k - b k)| + |∑' k, (a (k + H) - b (k + H))| :=
      abs_add_le _ _
    _ ≤ (∑ k ∈ Finset.range H, |a k - b k|) +
        ∑' k, |a (k + H) - b (k + H)| := by
      apply add_le_add
      · exact Finset.abs_sum_le_sum_abs _ _
      · exact hnormtail
    _ ≤ (∑ _k ∈ Finset.range H, δ) + ∑' k, 2 * E * q ^ (k + H + 1) :=
      add_le_add (Finset.sum_le_sum fun k hk => hhead k (Finset.mem_range.1 hk))
        (hdat.tsum_le_tsum htail hm)
    _ = (H : ℝ) * δ + 2 * E * q ^ (H + 1) / (1 - q) := by
      rw [hmt]
      simp [mul_comm]

/-! ## Volatility at zero ridge (`prop:app-pl-vol-zero`) -/

/-- `prop:app-pl-vol-zero`(i), snapshot `cr-2026-10-23`. Declaration of record: for every `ℓ ≥ 0` the limit
`C̄_{i,ℓ}(0)` exists (conjunct 2, identified with `cbarZero`), `C̄_{i,0}(0) = 1` (conjunct 3), and
`|C̄_{i,ℓ}(ϱ)| ≤ E_i β^{ℓ/3}` for `0 < ϱ ≤ z̄` and `ℓ ≥ 1` (conjunct 4; the zero-ridge version, conjunct 5,
follows by the limit). Hypothesis `0 < z̄ ≤ z_1` (`plZ1`). LaTeX, verbatim:

\begin{proposition}[Volatility at zero ridge]\label{prop:app-pl-vol-zero}
Let $0<\bar z\le z_1$ and $E_i\defeq A_N\bar z^{-1/2}+2\sqrt{D_i}\,\bar z^{1/4}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ the limit $\overline C_{i,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{i,\ell}(\ridge)$
exists, $\overline C_{i,0}(0)=1$, and $\abs{\overline C_{i,\ell}(\ridge)}\le E_i\,\bmom^{\ell/3}$ for
$0\le\ridge\le\bar z$ and $\ell\ge1$.
\item The series $\mathfrak v_i(0)\defeq1+2\sum_{\ell\ge1}\overline C_{i,\ell}(0)$ converges
absolutely, $\mathfrak v_i(\ridge)\to\mathfrak v_i(0)$ as $\ridge\downarrow0$, and for every
integer $H\ge0$ and $0<\ridge\le\bar z$,
\begin{equation}\label{eqn:app-pl-vol-ridge}
\abs{\mathfrak v_i(\ridge)-\mathfrak v_i(0)}\le2(1+2H)\sqrt{D_i}\,\ridge^{1/4}+\frac{4E_i\,\bmom^{(H+1)/3}}{1-\bmom^{1/3}} .
\end{equation}
\item For every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
all terms are nonnegative, and $\mathfrak v_i(0)=\sum_{\ell\in\mathbb Z}\overline C_{i,\ell}(0)\ge1$ with
$\overline C_{i,-\ell}(0)\defeq\overline C_{i,\ell}(0)$, which is the integral
\cref{eqn:app-pl-vol-zero} with the kernels of the lag $-\ell$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_vol_zero_i (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {zbar : ℝ} (hz0 : 0 < zbar) (hz1 : zbar ≤ plZ1 β B μ) :
    plRowExists cert γstar CSig β B μ i ∧
    (∀ ℓ : ℕ, Tendsto (fun ϱ : ℝ => lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (cbarZero cert γstar CSig β B μ i ℓ))) ∧
    cbarZero cert γstar CSig β B μ i 0 = 1 ∧
    (∀ (ℓ : ℕ) (ϱ : ℝ), 1 ≤ ℓ → 0 < ϱ → ϱ ≤ zbar →
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
        plEi β B μ hN i zbar * β ^ ((ℓ : ℝ) / 3)) ∧
    (∀ ℓ : ℕ, 1 ≤ ℓ →
      |cbarZero cert γstar CSig β B μ i ℓ| ≤ plEi β B μ hN i zbar * β ^ ((ℓ : ℝ) / 3)) := by
  classical
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) =
      ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hν' : (ν' : Measure ℝ) =
      ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := rfl
  have hdef (s : ℝ) (hs : 0 < s) (hsz : s ≤ plZ1 β B μ) :
      0 < 1 - volraw β ν ν' (μ i) s ∧
      1 - volraw β ν ν' (μ i) s ≤ plDcoef β B μ hN i * Real.sqrt s := by
    have hd := prop_app_pl_drift_zero_i_volraw μ hβ0 hβ1 hB hN hanti hpos
      hν hν' hμC hC1 i hs hsz
    have hm := zr_mOf_spec μ hβ0 hβ1 hB hN hanti hpos hs
    have hLam : 0 < partLam B μ (mOf β B μ s) :=
      (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm.1
    constructor
    · rw [hd.1]
      exact one_div_pos.mpr (by nlinarith [mul_pos hLam (hpos i)])
    · rw [hd.1]
      simpa [plDcoef, plFstar, one_div] using hd.2
  have hDz := hdef zbar hz0 hz1
  have hDmul : 0 < plDcoef β B μ hN i * Real.sqrt zbar := hDz.1.trans_le hDz.2
  have hD : 0 < plDcoef β B μ hN i :=
    pos_of_mul_pos_left hDmul (Real.sqrt_nonneg _)
  have htwo := (lem_app_pl_two_ridge_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 hν hν' i).2
  have hcmp (η ϱ : ℝ) (ℓ : ℕ) (hη : 0 < η) (hηϱ : η ≤ ϱ) (hϱz : ϱ ≤ zbar) :
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i η η -
          lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
        2 * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4) := by
    have hϱ : 0 < ϱ := hη.trans_le hηϱ
    calc
      _ ≤ 2 * Real.sqrt (1 - volraw β ν ν' (μ i) ϱ) := htwo η ϱ ℓ hη hηϱ
      _ ≤ 2 * Real.sqrt (plDcoef β B μ hN i * Real.sqrt ϱ) := by
        gcongr
        exact (hdef ϱ hϱ (hϱz.trans hz1)).2
      _ = _ := by
        rw [Real.sqrt_mul hD.le, zr_sqrt_sqrt hϱ.le]
        ring
  have hlim (ℓ : ℕ) := zr_tendsto_of_two_ridge
    (fun ϱ : ℝ => lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
    zbar (2 * Real.sqrt (plDcoef β B μ hN i)) hz0 (fun η ϱ hη hηϱ hϱz =>
      hcmp η ϱ ℓ hη hηϱ hϱz)
  have hzero : cbarZero cert γstar CSig β B μ i 0 = 1 := by
    have hsqrt : Tendsto (fun s : ℝ => plDcoef β B μ hN i * Real.sqrt s)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hs : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) :=
        by rw [nhdsWithin]; exact inf_le_left
      simpa using tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto 0 |>.mono_left hs)
    have hdeflim : Tendsto (fun s : ℝ => 1 - volraw β ν ν' (μ i) s)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsqrt ?_ ?_
      · filter_upwards [Ioo_mem_nhdsGT hz0] with s hs
        exact (hdef s hs.1 (hs.2.le.trans hz1)).1.le
      · filter_upwards [Ioo_mem_nhdsGT hz0] with s hs
        exact (hdef s hs.1 (hs.2.le.trans hz1)).2
    have hvol : Tendsto (fun s : ℝ => volraw β ν ν' (μ i) s)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [sub_sub_cancel, sub_zero] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub hdeflim
    have hrow : Tendsto
        (fun s : ℝ => lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i s s)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      refine hvol.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (zr_row0_eq cert γstar CSig hB μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' i hs).symm
    exact tendsto_nhds_unique (hlim 0).1 hrow
  have henvall : ∀ (ℓ : ℕ) (ϱ : ℝ), 1 ≤ ℓ → 0 < ϱ → ϱ ≤ zbar →
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
        plEi β B μ hN i zbar * β ^ ((ℓ : ℝ) / 3) := by
    intro ℓ ϱ hℓ hϱ hϱz
    let b : ℝ := β ^ ((ℓ : ℝ) / 3)
    have hb : 0 < b := Real.rpow_pos_of_pos hβ0 _
    have hb1 : b ≤ 1 := Real.rpow_le_one hβ0.le hβ1.le (by positivity)
    have hb3 : b ^ 3 = β ^ ℓ := by
      simp only [b, ← Real.rpow_natCast]
      rw [← Real.rpow_mul hβ0.le]
      congr 1
      norm_num
    let r : ℝ := zbar * b ^ 4
    have hr : 0 < r := mul_pos hz0 (pow_pos hb 4)
    have hrz : r ≤ zbar := by
      dsimp only [r]
      exact mul_le_of_le_one_right hz0.le (pow_le_one₀ hb.le hb1)
    have henv := (lem_app_pl_two_ridge_iii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
      hγ hμC hC1 i).2
    have hscale := zr_scale_id (plAN β B μ) (plDcoef β B μ hN i) zbar b hz0 hb
    change |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
      plEi β B μ hN i zbar * b
    by_cases hϱr : ϱ ≤ r
    · calc
        _ ≤ |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r| +
              |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ -
                lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r| := by
              have heq : lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
                  lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r +
                    (lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ -
                      lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r) := by ring
              calc
                _ = |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r +
                    (lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ -
                      lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r)| :=
                    congrArg abs heq
                _ ≤ _ := abs_add_le _ _
        _ ≤ plAN β B μ * β ^ ℓ / Real.sqrt r +
              2 * Real.sqrt (plDcoef β B μ hN i) * r ^ ((1 : ℝ) / 4) :=
            add_le_add (henv r ℓ hr hℓ) (hcmp ϱ r ℓ hϱ hϱr hrz)
        _ = plEi β B μ hN i zbar * b := by
            rw [← hb3]
            exact hscale
    · have hrϱ : r < ϱ := lt_of_not_ge hϱr
      have hsqrt : Real.sqrt r ≤ Real.sqrt ϱ := Real.sqrt_le_sqrt hrϱ.le
      have hnum : 0 ≤ plAN β B μ * β ^ ℓ := mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hβ0.le _)
      calc
        _ ≤ plAN β B μ * β ^ ℓ / Real.sqrt ϱ := henv ϱ ℓ hϱ hℓ
        _ ≤ plAN β B μ * β ^ ℓ / Real.sqrt r :=
          div_le_div_of_nonneg_left hnum (Real.sqrt_pos.2 hr) hsqrt
        _ ≤ plAN β B μ * β ^ ℓ / Real.sqrt r +
              2 * Real.sqrt (plDcoef β B μ hN i) * r ^ ((1 : ℝ) / 4) := by
            have : 0 ≤ 2 * Real.sqrt (plDcoef β B μ hN i) * r ^ ((1 : ℝ) / 4) := by positivity
            linarith
        _ = plEi β B μ hN i zbar * b := by
            rw [← hb3]
            exact hscale
  refine ⟨(lem_app_pl_two_ridge_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 hν hν' i).1, fun ℓ => (hlim ℓ).1, hzero, henvall, ?_⟩
  · intro ℓ hℓ
    refine le_of_tendsto ((hlim ℓ).1.abs) ?_
    filter_upwards [Ioo_mem_nhdsGT hz0] with ϱ hϱ
    exact henvall ℓ ϱ hℓ hϱ.1 hϱ.2.le

/-- `prop:app-pl-vol-zero`(ii), snapshot `cr-2026-10-23`. Declaration of record: the series `𝔳_i(0)` converges
absolutely (conjunct 2); `𝔳_i(ϱ) → 𝔳_i(0)` as `ϱ ↓ 0` (conjunct 3); and for every integer `H ≥ 0` and
`0 < ϱ ≤ z̄`, the quantitative bound (conjunct 4). Conjunct 1 gives the summability of the row series at
`ϱ ∈ (0, z̄]` that `rowVBar` needs. LaTeX, verbatim:

\begin{proposition}[Volatility at zero ridge]\label{prop:app-pl-vol-zero}
Let $0<\bar z\le z_1$ and $E_i\defeq A_N\bar z^{-1/2}+2\sqrt{D_i}\,\bar z^{1/4}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ the limit $\overline C_{i,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{i,\ell}(\ridge)$
exists, $\overline C_{i,0}(0)=1$, and $\abs{\overline C_{i,\ell}(\ridge)}\le E_i\,\bmom^{\ell/3}$ for
$0\le\ridge\le\bar z$ and $\ell\ge1$.
\item The series $\mathfrak v_i(0)\defeq1+2\sum_{\ell\ge1}\overline C_{i,\ell}(0)$ converges
absolutely, $\mathfrak v_i(\ridge)\to\mathfrak v_i(0)$ as $\ridge\downarrow0$, and for every
integer $H\ge0$ and $0<\ridge\le\bar z$,
\begin{equation}\label{eqn:app-pl-vol-ridge}
\abs{\mathfrak v_i(\ridge)-\mathfrak v_i(0)}\le2(1+2H)\sqrt{D_i}\,\ridge^{1/4}+\frac{4E_i\,\bmom^{(H+1)/3}}{1-\bmom^{1/3}} .
\end{equation}
\item For every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
all terms are nonnegative, and $\mathfrak v_i(0)=\sum_{\ell\in\mathbb Z}\overline C_{i,\ell}(0)\ge1$ with
$\overline C_{i,-\ell}(0)\defeq\overline C_{i,\ell}(0)$, which is the integral
\cref{eqn:app-pl-vol-zero} with the kernels of the lag $-\ell$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_vol_zero_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) {zbar : ℝ} (hz0 : 0 < zbar) (hz1 : zbar ≤ plZ1 β B μ) :
    plRowExists cert γstar CSig β B μ i ∧
    (∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ zbar →
      Summable (fun ℓ : ℕ => lagRowBar cert γstar CSig β (ℓ + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)) ∧
    Summable (fun ℓ : ℕ => |cbarZero cert γstar CSig β B μ i (ℓ + 1)|) ∧
    Tendsto (fun ϱ : ℝ => rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (vZero cert γstar CSig β B μ i)) ∧
    (∀ (H : ℕ) (ϱ : ℝ), 0 < ϱ → ϱ ≤ zbar →
      |rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ - vZero cert γstar CSig β B μ i| ≤
        2 * (1 + 2 * (H : ℝ)) * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4) +
          4 * plEi β B μ hN i zbar * β ^ (((H : ℝ) + 1) / 3) / (1 - β ^ ((1 : ℝ) / 3))) := by
  classical
  have hi := prop_app_pl_vol_zero_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 hz1
  let q : ℝ := β ^ ((1 : ℝ) / 3)
  let E : ℝ := plEi β B μ hN i zbar
  have hq0 : 0 ≤ q := (Real.rpow_pos_of_pos hβ0 _).le
  have hq1 : q < 1 := Real.rpow_lt_one hβ0.le hβ1 (by norm_num)
  have hpow (n : ℕ) : β ^ ((n : ℝ) / 3) = q ^ n := by
    simp only [q, ← Real.rpow_natCast]
    rw [← Real.rpow_mul hβ0.le]
    congr 1
    ring
  have hE : 0 ≤ E := by
    have hp := hi.2.2.2.2 1 (by omega)
    have hp' : 0 ≤ E * β ^ ((1 : ℝ) / 3) :=
      (abs_nonneg (cbarZero cert γstar CSig β B μ i 1)).trans (by
        simpa only [E, Nat.cast_one] using hp)
    exact nonneg_of_mul_nonneg_left hp' (Real.rpow_pos_of_pos hβ0 _)
  have hgeom : Summable (fun k : ℕ => E * q ^ (k + 1)) := by
    have h := (summable_geometric_of_lt_one hq0 hq1).mul_left (E * q)
    convert h using 1
    funext k
    rw [pow_succ]
    ring
  have habs : Summable (fun k : ℕ => |cbarZero cert γstar CSig β B μ i (k + 1)|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_) hgeom
    rw [← hpow]
    exact hi.2.2.2.2 (k + 1) (by omega)
  have hsumzero : Summable (fun k : ℕ => cbarZero cert γstar CSig β B μ i (k + 1)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using habs)
  have hsumridge (ϱ : ℝ) (hϱ : 0 < ϱ) : Summable (fun k : ℕ =>
      lagRowBar cert γstar CSig β (k + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) :=
    (eqn_app_pl_Cil_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
      hγ hμC hC1 i hϱ).2.1
  have htsum : Tendsto (fun ϱ : ℝ => ∑' k : ℕ,
      lagRowBar cert γstar CSig β (k + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑' k : ℕ, cbarZero cert γstar CSig β B μ i (k + 1))) := by
    apply tendsto_tsum_of_dominated_convergence hgeom
    · intro k
      exact hi.2.1 (k + 1)
    · filter_upwards [Ioo_mem_nhdsGT hz0] with ϱ hϱ
      intro k
      rw [Real.norm_eq_abs, ← hpow]
      exact hi.2.2.2.1 (k + 1) ϱ (by omega) hϱ.1 hϱ.2.le
  have hrowlim : Tendsto
      (fun ϱ : ℝ => rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (vZero cert γstar CSig β B μ i)) := by
    have hc := (hi.2.1 0).add (htsum.const_mul 2)
    have hc' : Tendsto (fun ϱ : ℝ =>
        lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ +
          2 * ∑' k : ℕ, lagRowBar cert γstar CSig β (k + 1) B μ
            (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
        (𝓝[>] (0 : ℝ)) (𝓝 (vZero cert γstar CSig β B μ i)) := by
      simpa only [vZero, hi.2.2.1] using hc
    refine hc'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    exact (eqn_app_pl_Cil_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
      hγ hμC hC1 i hϱ).2.2.symm
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) =
      ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hν' : (ν' : Measure ℝ) =
      ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := rfl
  have hdef (s : ℝ) (hs : 0 < s) (hsz : s ≤ plZ1 β B μ) :
      1 - volraw β ν ν' (μ i) s ≤ plDcoef β B μ hN i * Real.sqrt s := by
    have hd := prop_app_pl_drift_zero_i_volraw μ hβ0 hβ1 hB hN hanti hpos
      hν hν' hμC hC1 i hs hsz
    rw [hd.1]
    simpa [plDcoef, plFstar, one_div] using hd.2
  have hD : 0 ≤ plDcoef β B μ hN i := by
    have hz := hdef zbar hz0 hz1
    have hm := zr_mOf_spec μ hβ0 hβ1 hB hN hanti hpos hz0
    have hLam : 0 < partLam B μ (mOf β B μ zbar) :=
      (def_app_pl_participation_bij μ hB hN hpos).2.1.mapsTo hm.1
    have hd := prop_app_pl_drift_zero_i_volraw μ hβ0 hβ1 hB hN hanti hpos
      hν hν' hμC hC1 i hz0 hz1
    have hp : 0 < 1 - volraw β ν ν' (μ i) zbar := by
      rw [hd.1]
      exact one_div_pos.mpr (by nlinarith [mul_pos hLam (hpos i)])
    exact (pos_of_mul_pos_left (hp.trans_le hz) (Real.sqrt_nonneg _)).le
  have hlag (ℓ : ℕ) (ϱ : ℝ) (hϱ : 0 < ϱ) (hϱz : ϱ ≤ zbar) :
      |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ -
          cbarZero cert γstar CSig β B μ i ℓ| ≤
        2 * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4) := by
    have htwo := (lem_app_pl_two_ridge_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
      hγ hμC hC1 hν hν' i).2
    have hev : ∀ᶠ η in 𝓝[>] (0 : ℝ),
        |lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i η η -
          lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ| ≤
          2 * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4) := by
      filter_upwards [Ioo_mem_nhdsGT hϱ] with η hη
      calc
        _ ≤ 2 * Real.sqrt (1 - volraw β ν ν' (μ i) ϱ) := htwo η ϱ ℓ hη.1 hη.2.le
        _ ≤ 2 * Real.sqrt (plDcoef β B μ hN i * Real.sqrt ϱ) := by
          gcongr
          exact hdef ϱ hϱ (hϱz.trans hz1)
        _ = _ := by
          rw [Real.sqrt_mul hD, zr_sqrt_sqrt hϱ.le]
          ring
    have := le_of_tendsto ((hi.2.1 ℓ).sub tendsto_const_nhds |>.abs) hev
    rwa [abs_sub_comm] at this
  have hquant : ∀ (H : ℕ) (ϱ : ℝ), 0 < ϱ → ϱ ≤ zbar →
      |rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ -
          vZero cert γstar CSig β B μ i| ≤
        2 * (1 + 2 * (H : ℝ)) * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4) +
          4 * plEi β B μ hN i zbar * β ^ (((H : ℝ) + 1) / 3) /
            (1 - β ^ ((1 : ℝ) / 3)) := by
    intro H ϱ hϱ hϱz
    let a : ℕ → ℝ := fun k => lagRowBar cert γstar CSig β (k + 1) B μ
      (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ
    let b : ℕ → ℝ := fun k => cbarZero cert γstar CSig β B μ i (k + 1)
    let δ : ℝ := 2 * Real.sqrt (plDcoef β B μ hN i) * ϱ ^ ((1 : ℝ) / 4)
    have hs := zr_tsum_split_bound a b H δ E q (hsumridge ϱ hϱ) hsumzero hq0 hq1
      (fun k _ => hlag (k + 1) ϱ hϱ hϱz)
      (fun k => by
        calc
          |a (k + H) - b (k + H)| ≤ |a (k + H)| + |b (k + H)| := abs_sub _ _
          _ ≤ E * q ^ (k + H + 1) + E * q ^ (k + H + 1) := by
            apply add_le_add
            · dsimp only [a, E]
              rw [← hpow]
              exact hi.2.2.2.1 (k + H + 1) ϱ (by omega) hϱ hϱz
            · dsimp only [b, E]
              rw [← hpow]
              exact hi.2.2.2.2 (k + H + 1) (by omega)
          _ = 2 * E * q ^ (k + H + 1) := by ring)
    have hv := (eqn_app_pl_Cil_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
      hγ hμC hC1 i hϱ).2.2
    rw [hv, vZero]
    calc
      |(lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ +
          2 * ∑' k, a k) - (1 + 2 * ∑' k, b k)| ≤
          |lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ - 1| +
            2 * |∑' k, a k - ∑' k, b k| := by
        have heq : (lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ +
            2 * ∑' k, a k) - (1 + 2 * ∑' k, b k) =
            (lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ - 1) +
              2 * ((∑' k, a k) - ∑' k, b k) := by ring
        rw [heq]
        calc
          _ ≤ |lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ - 1| +
              |2 * ((∑' k, a k) - ∑' k, b k)| := abs_add_le _ _
          _ = _ := by rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ δ + 2 * ((H : ℝ) * δ + 2 * E * q ^ (H + 1) / (1 - q)) :=
        add_le_add (by simpa only [hi.2.2.1] using hlag 0 ϱ hϱ hϱz)
          (mul_le_mul_of_nonneg_left hs (by norm_num))
      _ = _ := by
        dsimp only [δ, E, q]
        rw [← hpow (H + 1)]
        norm_num [Nat.cast_add, Nat.cast_one]
        ring
  refine ⟨hi.1, ?_, habs, hrowlim, hquant⟩
  intro ϱ hϱ _
  exact hsumridge ϱ hϱ

section ZrInt
open Muon.Volatility (supNorm IsOddBddLip omegaT)

private lemma zrb_iota_abs {s0 s x : ℝ} (hs0 : 0 < s0) (hs : s0 ≤ s) :
    |iotaF s x| ≤ 1 / (2 * Real.sqrt s0) := by
  have hr : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hr2 : Real.sqrt s0 ^ 2 = s0 := Real.sq_sqrt hs0.le
  have hP : 0 < x ^ 2 + s := by nlinarith [sq_nonneg x]
  unfold iotaF
  rw [abs_div, abs_of_pos hP, div_le_div_iff₀ hP (by positivity)]
  have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - Real.sqrt s0), abs_nonneg x]

private lemma zrb_iota_lip {s0 s x x' : ℝ} (hs0 : 0 < s0) (hs : s0 ≤ s) :
    |iotaF s x - iotaF s x'| ≤ |x - x'| / s0 := by
  have hP : 0 < x ^ 2 + s := by nlinarith [sq_nonneg x]
  have hP' : 0 < x' ^ 2 + s := by nlinarith [sq_nonneg x']
  have hs' : 0 < s := hs0.trans_le hs
  have e : iotaF s x - iotaF s x' = (x - x') * (s - x * x') / ((x ^ 2 + s) * (x' ^ 2 + s)) := by
    unfold iotaF; field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hP hP'), div_le_div_iff₀ (mul_pos hP hP') hs0]
  have key : |s - x * x'| * s0 ≤ (x ^ 2 + s) * (x' ^ 2 + s) := by
    have h1 : |s - x * x'| ≤ s + |x * x'| := by
      calc |s - x * x'| ≤ |s| + |x * x'| := abs_sub _ _
        _ = _ := by rw [abs_of_pos hs']
    have h2 : |x * x'| ≤ (x ^ 2 + x' ^ 2) / 2 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (x - x'), sq_nonneg (x + x')]
    have h3 : (s + |x * x'|) * s0 ≤ (x ^ 2 + s) * (x' ^ 2 + s) := by
      nlinarith [sq_nonneg x, sq_nonneg x', mul_nonneg (sq_nonneg x) (sq_nonneg x'), abs_nonneg (x * x')]
    calc |s - x * x'| * s0 ≤ (s + |x * x'|) * s0 := mul_le_mul_of_nonneg_right h1 hs0.le
      _ ≤ _ := h3
  calc |x - x'| * |s - x * x'| * s0 = |x - x'| * (|s - x * x'| * s0) := by ring
    _ ≤ |x - x'| * ((x ^ 2 + s) * (x' ^ 2 + s)) := mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = _ := by ring

private lemma zrb_iota_param {s0 s s' x : ℝ} (hs0 : 0 < s0) (hs : s0 ≤ s) (hs' : s0 ≤ s') :
    |iotaF s x - iotaF s' x| ≤ |s - s'| / (s0 * Real.sqrt s0) := by
  have hr : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hr2 : Real.sqrt s0 ^ 2 = s0 := Real.sq_sqrt hs0.le
  have hP : 0 < x ^ 2 + s := by nlinarith [sq_nonneg x]
  have hP' : 0 < x ^ 2 + s' := by nlinarith [sq_nonneg x]
  have e : iotaF s x - iotaF s' x = x * (s' - s) / ((x ^ 2 + s) * (x ^ 2 + s')) := by
    unfold iotaF; field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos (mul_pos hP hP'), abs_sub_comm s' s,
    div_le_div_iff₀ (mul_pos hP hP') (by positivity)]
  have h1 : 2 * |x| * Real.sqrt s0 ≤ x ^ 2 + s0 := by
    nlinarith [sq_nonneg (|x| - Real.sqrt s0), sq_abs x]
  have key : |x| * (s0 * Real.sqrt s0) ≤ (x ^ 2 + s) * (x ^ 2 + s') := by
    have a1 : x ^ 2 + s0 ≤ x ^ 2 + s := by linarith
    have a2 : x ^ 2 + s0 ≤ x ^ 2 + s' := by linarith
    have a3 : (x ^ 2 + s0) * (x ^ 2 + s0) ≤ (x ^ 2 + s) * (x ^ 2 + s') :=
      mul_le_mul a1 a2 (by positivity) hP.le
    nlinarith [mul_nonneg (abs_nonneg x) hr.le, mul_nonneg hs0.le (abs_nonneg x),
      mul_le_mul_of_nonneg_left h1 hs0.le, sq_nonneg x]
  calc |x| * |s - s'| * (s0 * Real.sqrt s0) = |s - s'| * (|x| * (s0 * Real.sqrt s0)) := by ring
    _ ≤ |s - s'| * ((x ^ 2 + s) * (x ^ 2 + s')) := mul_le_mul_of_nonneg_left key (abs_nonneg _)
    _ = _ := by ring


private lemma zrb_iota_cont {ϱ a b s0 : ℝ} (hs0 : 0 < s0) (hy : ∀ y ∈ Icc a b, s0 ≤ ϱ + y ^ 2) (x : ℝ) :
    ContinuousOn (fun y => iotaF (ϱ + y ^ 2) x) (Icc a b) := by
  unfold iotaF
  refine continuousOn_const.div (by fun_prop) fun y hyy => ?_
  have := hy y hyy
  nlinarith [sq_nonneg x]

private lemma zrb_F_obl {ϱ a b s0 : ℝ} (hs0 : 0 < s0) (hab : a ≤ b)
    (hy : ∀ y ∈ Icc a b, s0 ≤ ϱ + y ^ 2) :
    IsOddBddLip (fun x => (2 / Real.pi) * ∫ y in a..b, iotaF (ϱ + y ^ 2) x) := by
  have hint : ∀ x, IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume a b := fun x =>
    (zrb_iota_cont hs0 hy x).intervalIntegrable_of_Icc hab
  have hpi : 0 < Real.pi := Real.pi_pos
  refine ⟨fun x => ?_, ⟨(2 / Real.pi) * (1 / (2 * Real.sqrt s0) * |b - a|), fun x => ?_⟩,
    ⟨(2 / Real.pi) * (1 / s0 * |b - a|), fun x x' => ?_⟩⟩
  · have : ∀ y, iotaF (ϱ + y ^ 2) (-x) = -iotaF (ϱ + y ^ 2) x := fun y => by
      unfold iotaF; rw [neg_sq, neg_div]
    simp only [this, intervalIntegral.integral_neg]; ring
  · rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun y => iotaF (ϱ + y ^ 2) x) (C := 1 / (2 * Real.sqrt s0)) (fun y hyy => by
        rw [Real.norm_eq_abs]
        rw [Set.uIoc_of_le hab] at hyy
        have hyy' : y ∈ Icc a b := ⟨hyy.1.le, hyy.2⟩
        exact zrb_iota_abs hs0 (hy y hyy'))
    simpa [Real.norm_eq_abs] using this
  · rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi), ← intervalIntegral.integral_sub (hint x) (hint x')]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b)
      (f := fun y => iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y ^ 2) x') (C := |x - x'| / s0) (fun y hyy => by
        rw [Set.uIoc_of_le hab] at hyy
        rw [Real.norm_eq_abs]
        exact zrb_iota_lip hs0 (hy y ⟨hyy.1.le, hyy.2⟩))
    rw [Real.norm_eq_abs] at this
    calc 2 / Real.pi * |∫ y in a..b, (iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y ^ 2) x')|
        ≤ 2 / Real.pi * (|x - x'| / s0 * |b - a|) := mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring


private lemma zrb_obl_add {f f' : ℝ → ℝ} (c : ℝ) (hf : IsOddBddLip f) (hf' : IsOddBddLip f') :
    IsOddBddLip (fun x => f x + c * f' x) := by
  obtain ⟨o1, ⟨M1, b1⟩, ⟨L1, l1⟩⟩ := hf
  obtain ⟨o2, ⟨M2, b2⟩, ⟨L2, l2⟩⟩ := hf'
  refine ⟨fun x => ?_, ⟨M1 + |c| * M2, fun x => ?_⟩, ⟨L1 + |c| * L2, fun x y => ?_⟩⟩
  · simp only [o1, o2]; ring
  · calc |f x + c * f' x| ≤ |f x| + |c * f' x| := abs_add_le _ _
      _ ≤ M1 + |c| * M2 := by rw [abs_mul]; exact add_le_add (b1 x) (mul_le_mul_of_nonneg_left (b2 x) (abs_nonneg c))
  · have : f x + c * f' x - (f y + c * f' y) = (f x - f y) + c * (f' x - f' y) := by ring
    rw [this]
    calc |(f x - f y) + c * (f' x - f' y)| ≤ |f x - f y| + |c * (f' x - f' y)| := abs_add_le _ _
      _ ≤ L1 * |x - y| + |c| * (L2 * |x - y|) := by
          rw [abs_mul]; exact add_le_add (l1 x y) (mul_le_mul_of_nonneg_left (l2 x y) (abs_nonneg c))
      _ = _ := by ring

private lemma zrb_supNorm_le {f : ℝ → ℝ} {C : ℝ} (h : ∀ x, |f x| ≤ C) : supNorm f ≤ C :=
  ciSup_le h

private lemma zrb_iota_obl {s : ℝ} (hs : 0 < s) : IsOddBddLip (iotaF s) :=
  (Muon.Volatility.lem_app_vol_sharp_ii hs one_pos).1


private lemma zrb_H1 (Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb) (G : ℝ → ℝ)
    (hlin : ∀ (f f' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' →
      Φ (fun x => f x + c * f' x) G = Φ f G + c * Φ f' G)
    (hbd : ∀ f : ℝ → ℝ, IsOddBddLip f → |Φ f G| ≤ Cb * supNorm f)
    {ϱ a b s0 : ℝ} (hs0 : 0 < s0) (hab : a ≤ b) (hy : ∀ y ∈ Icc a b, s0 ≤ ϱ + y ^ 2) :
    Φ (fun x => (2 / Real.pi) * ∫ y in a..b, iotaF (ϱ + y ^ 2) x) G =
      (2 / Real.pi) * ∫ y in a..b, Φ (iotaF (ϱ + y ^ 2)) G := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hp2 : 0 < 2 / Real.pi := by positivity
  have hr : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  set Fu : ℝ → ℝ → ℝ := fun u x => (2 / Real.pi) * ∫ y in a..u, iotaF (ϱ + y ^ 2) x with hFu
  have hFobl : ∀ u ∈ Icc a b, IsOddBddLip (Fu u) := fun u hu =>
    zrb_F_obl hs0 hu.1 (fun y hyy => hy y ⟨hyy.1, hyy.2.trans hu.2⟩)
  have hιobl : ∀ y ∈ Icc a b, IsOddBddLip (iotaF (ϱ + y ^ 2)) := fun y hyy =>
    zrb_iota_obl (hs0.trans_le (hy y hyy))
  set g : ℝ → ℝ := fun y => Φ (iotaF (ϱ + y ^ 2)) G with hg
  set M : ℝ := |a| + |b| with hM
  set c1 : ℝ := 1 / (s0 * Real.sqrt s0) with hc1
  have hc10 : 0 ≤ c1 := by positivity
  have hMy : ∀ y ∈ Icc a b, |y| ≤ M := fun y hyy => by
    rcases abs_cases y with h | h <;> rcases abs_cases a with h1 | h1 <;>
      rcases abs_cases b with h2 | h2 <;> simp only [hM] <;> linarith [hyy.1, hyy.2, abs_nonneg a, abs_nonneg b]
  have hM0 : 0 ≤ M := by positivity
  have hpt : ∀ y ∈ Icc a b, ∀ y' ∈ Icc a b, ∀ x, |iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y' ^ 2) x| ≤
      2 * M * c1 * |y - y'| := by
    intro y hyy y' hyy' x
    have h := zrb_iota_param (x := x) hs0 (hy y hyy) (hy y' hyy')
    have e : |(ϱ + y ^ 2) - (ϱ + y' ^ 2)| = |y + y'| * |y - y'| := by
      rw [← abs_mul]; congr 1; ring
    rw [e] at h
    have h2 : |y + y'| ≤ 2 * M := by
      calc |y + y'| ≤ |y| + |y'| := abs_add_le _ _
        _ ≤ M + M := add_le_add (hMy y hyy) (hMy y' hyy')
        _ = _ := by ring
    calc _ ≤ |y + y'| * |y - y'| / (s0 * Real.sqrt s0) := h
      _ = |y + y'| * |y - y'| * c1 := by rw [hc1]; ring
      _ ≤ 2 * M * |y - y'| * c1 := by gcongr
      _ = _ := by ring
  set Lg : ℝ := Cb * (2 * M * c1) with hLg
  have hLg0 : 0 ≤ Lg := by positivity
  have hg_lip : ∀ y ∈ Icc a b, ∀ y' ∈ Icc a b, |g y - g y'| ≤ Lg * |y - y'| := by
    intro y hyy y' hyy'
    have h1 := hlin (iotaF (ϱ + y ^ 2)) (iotaF (ϱ + y' ^ 2)) (-1) (hιobl y hyy) (hιobl y' hyy')
    have h2 := hbd _ (zrb_obl_add (-1) (hιobl y hyy) (hιobl y' hyy'))
    have h3 : supNorm (fun x => iotaF (ϱ + y ^ 2) x + -1 * iotaF (ϱ + y' ^ 2) x) ≤
        2 * M * c1 * |y - y'| := zrb_supNorm_le fun x => by
      have := hpt y hyy y' hyy' x
      rwa [show iotaF (ϱ + y ^ 2) x + -1 * iotaF (ϱ + y' ^ 2) x =
        iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y' ^ 2) x by ring]
    have : g y - g y' = Φ (fun x => iotaF (ϱ + y ^ 2) x + -1 * iotaF (ϱ + y' ^ 2) x) G := by
      rw [h1]; simp only [hg]; ring
    rw [this]
    calc _ ≤ Cb * supNorm _ := h2
      _ ≤ Cb * (2 * M * c1 * |y - y'|) := mul_le_mul_of_nonneg_left h3 hCb
      _ = _ := by rw [hLg]; ring
  have hg_cont : ContinuousOn g (Icc a b) := by
    have : LipschitzOnWith (Real.toNNReal Lg) g (Icc a b) := by
      refine LipschitzOnWith.of_dist_le_mul fun y hyy y' hyy' => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hLg0]
      exact hg_lip y hyy y' hyy'
    exact this.continuousOn
  have hgint : ∀ u ∈ Icc a b, IntervalIntegrable g volume a u := fun u hu =>
    (hg_cont.mono (Icc_subset_Icc_right hu.2)).intervalIntegrable_of_Icc hu.1
  have hιint : ∀ x, ∀ u ∈ Icc a b, IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume a u :=
    fun x u hu => (zrb_iota_cont hs0 hy x |>.mono (Icc_subset_Icc_right hu.2)).intervalIntegrable_of_Icc hu.1
  set E : ℝ → ℝ := fun u => Φ (Fu u) G - (2 / Real.pi) * ∫ y in a..u, g y with hE
  set K : ℝ := Cb * ((2 / Real.pi) * (2 * M * c1)) + (2 / Real.pi) * Lg with hK
  have hK0 : 0 ≤ K := by positivity
  have hest : ∀ u v, a ≤ u → u ≤ v → v ≤ b → |E v - E u| ≤ K * (v - u) ^ 2 := by
    intro u v hau huv hvb
    have hu : u ∈ Icc a b := ⟨hau, huv.trans hvb⟩
    have hv : v ∈ Icc a b := ⟨hau.trans huv, hvb⟩
    have hsub : ∀ y ∈ Set.uIoc u v, y ∈ Icc a b := fun y hyy => by
      rw [Set.uIoc_of_le huv] at hyy; exact ⟨hau.trans hyy.1.le, hyy.2.trans hvb⟩
    have hIuv : Icc u v ⊆ Icc a b := Icc_subset_Icc hau hvb
    -- the pointwise bound on D
    have hDpt : ∀ x, |(Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x| ≤
        (2 / Real.pi) * (2 * M * c1) * (v - u) ^ 2 := by
      intro x
      have e1 : Fu v x - Fu u x = (2 / Real.pi) * ∫ y in u..v, iotaF (ϱ + y ^ 2) x := by
        simp only [hFu]
        rw [← mul_sub, intervalIntegral.integral_interval_sub_left (hιint x v hv) (hιint x u hu)]
      have e2 : (v - u) * iotaF (ϱ + u ^ 2) x = ∫ y in u..v, iotaF (ϱ + u ^ 2) x := by
        rw [intervalIntegral.integral_const]; simp
      have hi1 : IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume u v :=
        ((zrb_iota_cont hs0 hy x).mono hIuv).intervalIntegrable_of_Icc huv
      have e3 : (Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x =
          (2 / Real.pi) * ∫ y in u..v, (iotaF (ϱ + y ^ 2) x - iotaF (ϱ + u ^ 2) x) := by
        rw [intervalIntegral.integral_sub hi1 intervalIntegrable_const, ← e2]
        have := e1
        linear_combination this
      rw [e3, abs_mul, abs_of_pos hp2]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
        (f := fun y => iotaF (ϱ + y ^ 2) x - iotaF (ϱ + u ^ 2) x) (C := 2 * M * c1 * (v - u))
        (fun y hyy => by
          rw [Real.norm_eq_abs]
          have h := hpt y (hsub y hyy) u hu x
          have hyu : |y - u| ≤ v - u := by
            rw [Set.uIoc_of_le huv] at hyy
            rw [abs_of_nonneg (by linarith [hyy.1])]; linarith [hyy.2]
          calc _ ≤ 2 * M * c1 * |y - u| := h
            _ ≤ _ := by gcongr)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ v - u)] at this
      calc 2 / Real.pi * |∫ y in u..v, (iotaF (ϱ + y ^ 2) x - iotaF (ϱ + u ^ 2) x)|
          ≤ 2 / Real.pi * (2 * M * c1 * (v - u) * (v - u)) := mul_le_mul_of_nonneg_left this hp2.le
        _ = _ := by ring
    have hDobl := zrb_obl_add (-(2 / Real.pi * (v - u))) (zrb_obl_add (-1) (hFobl v hv) (hFobl u hu))
      (hιobl u hu)
    have hΦD : Φ (fun x => (Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x) G =
        Φ (Fu v) G - Φ (Fu u) G - (2 / Real.pi * (v - u)) * g u := by
      rw [hlin _ _ _ (zrb_obl_add (-1) (hFobl v hv) (hFobl u hu)) (hιobl u hu),
        hlin (Fu v) (Fu u) (-1) (hFobl v hv) (hFobl u hu)]
      simp only [hg]; ring
    have hDbd : |Φ (fun x => (Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x) G| ≤
        Cb * ((2 / Real.pi) * (2 * M * c1) * (v - u) ^ 2) :=
      (hbd _ hDobl).trans (mul_le_mul_of_nonneg_left (zrb_supNorm_le hDpt) hCb)
    have hgi : (∫ y in a..v, g y) - ∫ y in a..u, g y = ∫ y in u..v, g y :=
      intervalIntegral.integral_interval_sub_left (hgint v hv) (hgint u hu)
    have hg_uv : IntervalIntegrable g volume u v := (hg_cont.mono hIuv).intervalIntegrable_of_Icc huv
    have eint : ∫ y in u..v, (g y - g u) = (∫ y in u..v, g y) - (v - u) * g u := by
      rw [intervalIntegral.integral_sub hg_uv intervalIntegrable_const, intervalIntegral.integral_const]
      simp
    have hint2 : |∫ y in u..v, (g y - g u)| ≤ Lg * (v - u) * (v - u) := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := u) (b := v)
        (f := fun y => g y - g u) (C := Lg * (v - u)) (fun y hyy => by
          rw [Real.norm_eq_abs]
          have hyu : |y - u| ≤ v - u := by
            rw [Set.uIoc_of_le huv] at hyy
            rw [abs_of_nonneg (by linarith [hyy.1])]; linarith [hyy.2]
          calc _ ≤ Lg * |y - u| := hg_lip y (hsub y hyy) u hu
            _ ≤ _ := mul_le_mul_of_nonneg_left hyu hLg0)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ v - u)] at this
      exact this
    have hEeq : E v - E u = Φ (fun x => (Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x) G
        - (2 / Real.pi) * ∫ y in u..v, (g y - g u) := by
      rw [hΦD, eint, ← hgi]
      simp only [hE]; ring
    rw [hEeq]
    calc _ ≤ |Φ (fun x => (Fu v x + (-1) * Fu u x) + (-(2 / Real.pi * (v - u))) * iotaF (ϱ + u ^ 2) x) G|
          + |(2 / Real.pi) * ∫ y in u..v, (g y - g u)| := abs_sub _ _
      _ ≤ Cb * ((2 / Real.pi) * (2 * M * c1) * (v - u) ^ 2) + (2 / Real.pi) * (Lg * (v - u) * (v - u)) := by
          rw [abs_mul, abs_of_pos hp2]
          exact add_le_add hDbd (mul_le_mul_of_nonneg_left hint2 hp2.le)
      _ = _ := by rw [hK]; ring
  have hEcont : ContinuousOn E (Icc a b) := by
    have hL0 : 0 ≤ K * (b - a) := mul_nonneg hK0 (sub_nonneg.2 hab)
    have : LipschitzOnWith (Real.toNNReal (K * (b - a))) E (Icc a b) := by
      refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ hL0]
      rcases le_total u v with h | h
      · have h1 := hest u v hu.1 h hv.2
        rw [abs_sub_comm, abs_sub_comm u v, abs_of_nonneg (sub_nonneg.2 h)]
        calc |E v - E u| ≤ K * (v - u) ^ 2 := h1
          _ = K * ((v - u) * (v - u)) := by ring
          _ ≤ K * ((b - a) * (v - u)) := by
              apply mul_le_mul_of_nonneg_left _ hK0
              exact mul_le_mul_of_nonneg_right (by linarith [hu.1, hv.2]) (sub_nonneg.2 h)
          _ = _ := by ring
      · have h1 := hest v u hv.1 h hu.2
        rw [abs_of_nonneg (sub_nonneg.2 h)]
        calc |E u - E v| ≤ K * (u - v) ^ 2 := h1
          _ = K * ((u - v) * (u - v)) := by ring
          _ ≤ K * ((b - a) * (u - v)) := by
              apply mul_le_mul_of_nonneg_left _ hK0
              exact mul_le_mul_of_nonneg_right (by linarith [hv.1, hu.2]) (sub_nonneg.2 h)
          _ = _ := by ring
    exact this.continuousOn
  have hderiv : ∀ x ∈ Ico a b, HasDerivWithinAt E 0 (Ici x) x := by
    intro x hx
    rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hcK : 0 < c / (K + 1) := by positivity
    have hmem : Icc x (min b (x + c / (K + 1))) ∈ 𝓝[≥] x :=
      Icc_mem_nhdsGE (lt_min hx.2 (by linarith))
    filter_upwards [hmem] with y hyy
    have hxy : x ≤ y := hyy.1
    have hyb : y ≤ b := hyy.2.trans (min_le_left _ _)
    have hyc : y - x ≤ c / (K + 1) := by linarith [hyy.2.trans (min_le_right _ _)]
    have h1 := hest x y hx.1 hxy hyb
    simp only [smul_zero, sub_zero, Real.norm_eq_abs]
    rw [abs_of_nonneg (sub_nonneg.2 hxy)]
    calc |E y - E x| ≤ K * (y - x) ^ 2 := h1
      _ = K * (y - x) * (y - x) := by ring
      _ ≤ K * (c / (K + 1)) * (y - x) := by
          apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 hxy)
          exact mul_le_mul_of_nonneg_left hyc hK0
      _ ≤ c * (y - x) := by
          apply mul_le_mul_of_nonneg_right _ (sub_nonneg.2 hxy)
          rw [mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have hconst := constant_of_has_deriv_right_zero hEcont hderiv b ⟨hab, le_rfl⟩
  have hFa : Φ (Fu a) G = 0 := by
    have h := hbd (Fu a) (hFobl a ⟨le_rfl, hab⟩)
    have h0 : supNorm (Fu a) ≤ 0 := zrb_supNorm_le fun x => by simp [hFu]
    have h00 : 0 ≤ supNorm (Fu a) := Real.iSup_nonneg fun _ => abs_nonneg _
    have : |Φ (Fu a) G| ≤ 0 := h.trans (by nlinarith)
    exact abs_nonpos_iff.mp this
  have hEa : E a = 0 := by simp only [hE, hFa]; simp
  have : E b = 0 := hconst.trans hEa
  have h2 : Φ (Fu b) G = (2 / Real.pi) * ∫ y in a..b, g y := by
    have := this; simp only [hE] at this; linarith
  exact h2

private lemma zrb_H2 (Φ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hlin1 : ∀ (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      Φ (fun x => f x + c * f' x) g = Φ f g + c * Φ f' g)
    (hlin2 : ∀ (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      Φ f (fun x => g x + c * g' x) = Φ f g + c * Φ f g')
    (hbd : ∀ f g : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g → |Φ f g| ≤ Cb * supNorm f * supNorm g)
    {ϱ a b s0 ϱ' a' b' s0' : ℝ} (hs0 : 0 < s0) (hab : a ≤ b) (hy : ∀ y ∈ Icc a b, s0 ≤ ϱ + y ^ 2)
    (hs0' : 0 < s0') (hab' : a' ≤ b') (hy' : ∀ y ∈ Icc a' b', s0' ≤ ϱ' + y ^ 2) :
    Φ (fun x => (2 / Real.pi) * ∫ y in a..b, iotaF (ϱ + y ^ 2) x)
        (fun x => (2 / Real.pi) * ∫ y in a'..b', iotaF (ϱ' + y ^ 2) x) =
      (2 / Real.pi) * ∫ y in a..b, (2 / Real.pi) * ∫ z in a'..b',
        Φ (iotaF (ϱ + y ^ 2)) (iotaF (ϱ' + z ^ 2)) := by
  have hF' := zrb_F_obl hs0' hab' hy'
  have h1 := zrb_H1 Φ (Cb * supNorm (fun x => (2 / Real.pi) * ∫ y in a'..b', iotaF (ϱ' + y ^ 2) x))
    (mul_nonneg hCb (Real.iSup_nonneg fun _ => abs_nonneg _)) _
    (fun f f' c hf hf' => hlin1 f f' _ c hf hf' hF')
    (fun f hf => by
      have := hbd f _ hf hF'
      calc _ ≤ _ := this
        _ = _ := by ring)
    hs0 hab hy
  rw [h1]
  congr 1
  refine intervalIntegral.integral_congr fun y hyy => ?_
  rw [Set.uIcc_of_le hab] at hyy
  have hιy : IsOddBddLip (iotaF (ϱ + y ^ 2)) := zrb_iota_obl (hs0.trans_le (hy y hyy))
  exact zrb_H1 (fun f g => Φ g f) (Cb * supNorm (iotaF (ϱ + y ^ 2)))
    (mul_nonneg hCb (Real.iSup_nonneg fun _ => abs_nonneg _)) _
    (fun f f' c hf hf' => hlin2 _ f f' c hιy hf hf')
    (fun f hf => by
      have := hbd _ f hιy hf
      calc _ ≤ _ := this
        _ = _ := by ring)
    hs0' hab' hy'


private lemma zrd_omegaF_abs {ϱ : ℝ} (hϱ : 0 < ϱ) (x : ℝ) : |omegaF ϱ x| ≤ 1 := by
  have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
  have hs : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
  unfold omegaF
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
    _ ≤ _ := Real.sqrt_le_sqrt (by linarith)

private lemma zrd_omegaT_abs {ϱ T : ℝ} (hϱ : 0 < ϱ) (hT : 0 < T) (x : ℝ) : |omegaT ϱ T x| ≤ 1 := by
  by_cases hx : x = 0
  · subst hx; simp [omegaT, iotaF]
  · have h := (Muon.Volatility.lem_app_vol_square_i ϱ T hϱ hT).1 x hx
    have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
    have hs : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
    have hω : omegaF ϱ x ≠ 0 := by
      unfold omegaF; exact div_ne_zero hx hs.ne'
    have e : omegaT ϱ T x = (omegaT ϱ T x / omegaF ϱ x) * omegaF ϱ x := by field_simp
    rw [e, abs_mul, abs_of_nonneg h.1]
    calc _ ≤ 1 * |omegaF ϱ x| := mul_le_mul_of_nonneg_right h.2 (abs_nonneg _)
      _ ≤ 1 := by rw [one_mul]; exact zrd_omegaF_abs hϱ x

private lemma zrd_a_sq {ϱ δ : ℝ} (hϱ : 0 < ϱ) (hδ : 0 < δ) (x : ℝ) :
    omegaT ϱ δ x ^ 2 ≤ 2 * (1 - omegaF (δ ^ 2) x ^ 2) := by
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hP : 0 < x ^ 2 + δ ^ 2 := by positivity
  have hω2 : omegaF (δ ^ 2) x ^ 2 = x ^ 2 / (x ^ 2 + δ ^ 2) := by
    unfold omegaF
    rw [div_pow, Real.sq_sqrt hP.le]
  have h1 : 1 - omegaF (δ ^ 2) x ^ 2 = δ ^ 2 / (x ^ 2 + δ ^ 2) := by
    rw [hω2]; field_simp; ring
  rw [h1]
  have ha1 : omegaT ϱ δ x ^ 2 ≤ 1 := by
    have := zrd_omegaT_abs hϱ hδ x
    nlinarith [abs_nonneg (omegaT ϱ δ x), sq_abs (omegaT ϱ δ x)]
  by_cases hxd : x ^ 2 ≤ δ ^ 2
  · refine ha1.trans ?_
    rw [← mul_div_assoc, le_div_iff₀ hP]
    nlinarith
  · push_neg at hxd
    have hx0 : x ≠ 0 := by rintro rfl; simp at hxd; nlinarith
    have hxpos : 0 < |x| := abs_pos.mpr hx0
    have hbound : |omegaT ϱ δ x| ≤ (2 / Real.pi) * (1 / |x| * δ) := by
      unfold omegaT
      rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := δ)
        (f := fun y => iotaF (ϱ + y ^ 2) x) (C := 1 / |x|) (fun y hy => by
          rw [Real.norm_eq_abs]
          unfold iotaF
          have hP' : 0 < x ^ 2 + (ϱ + y ^ 2) := by nlinarith [sq_nonneg x, sq_nonneg y]
          rw [abs_div, abs_of_pos (by nlinarith [sq_nonneg x, sq_nonneg y] : 0 < x ^ 2 + (ϱ + y ^ 2))]
          rw [div_le_div_iff₀ (by nlinarith [sq_nonneg x, sq_nonneg y]) hxpos]
          have : |x| * |x| = x ^ 2 := by rw [← sq, sq_abs]
          nlinarith [sq_nonneg y, hϱ])
      rw [Real.norm_eq_abs, sub_zero, abs_of_pos hδ] at this
      exact this
    have hsq : omegaT ϱ δ x ^ 2 ≤ ((2 / Real.pi) * (1 / |x| * δ)) ^ 2 := by
      rw [← sq_abs (omegaT ϱ δ x)]
      exact pow_le_pow_left₀ (abs_nonneg _) hbound 2
    refine hsq.trans ?_
    have hpi : 3 < Real.pi := Real.pi_gt_three
    have hxx : |x| ^ 2 = x ^ 2 := sq_abs x
    have e : ((2 / Real.pi) * (1 / |x| * δ)) ^ 2 = 4 / Real.pi ^ 2 * (δ ^ 2 / x ^ 2) := by
      rw [← hxx]; field_simp; norm_num
    rw [e]
    have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
    have hq : 4 / Real.pi ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have hx2 : 0 < x ^ 2 := by positivity
    have key : δ ^ 2 / x ^ 2 ≤ 2 * (δ ^ 2 / (x ^ 2 + δ ^ 2)) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hx2 hP]
      nlinarith [sq_nonneg δ]
    calc 4 / Real.pi ^ 2 * (δ ^ 2 / x ^ 2) ≤ 1 * (δ ^ 2 / x ^ 2) :=
          mul_le_mul_of_nonneg_right hq (by positivity)
      _ ≤ _ := by rw [one_mul]; exact key


end ZrInt


section ZrSharp
open scoped Matrix MatrixOrder
open Matrix
open Muon.Foundations (hermDilation upperRight)
open Muon.Volatility (oddSharp)

/-- Spectrum of a block-diagonal matrix lies in the union of the block spectra. Private helper. -/
private lemma zrs_spectrum_fromBlocks_diag_sub {m n : ℕ} (P : Mat m m) (R : Mat n n) :
    spectrum ℝ (Matrix.fromBlocks P 0 0 R) ⊆ spectrum ℝ P ∪ spectrum ℝ R := by
  intro l hl
  by_contra hc
  simp only [Set.mem_union, not_or] at hc
  have hU1 : IsUnit (algebraMap ℝ (Mat m m) l - P) := spectrum.notMem_iff.mp hc.1
  have hU2 : IsUnit (algebraMap ℝ (Mat n n) l - R) := spectrum.notMem_iff.mp hc.2
  apply spectrum.mem_iff.mp hl
  have hdiag : algebraMap ℝ (Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) l - Matrix.fromBlocks P 0 0 R
      = Matrix.fromBlocks (algebraMap ℝ (Mat m m) l - P) 0 0 (algebraMap ℝ (Mat n n) l - R) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.algebraMap_matrix_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [hdiag, Matrix.isUnit_iff_isUnit_det, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hU1).mul ((Matrix.isUnit_iff_isUnit_det _).mp hU2)

/-- Powers of a block-diagonal matrix are block-diagonal. Private helper. -/
private lemma zrs_fromBlocks_diag_pow {m n : ℕ} (P : Mat m m) (R : Mat n n) (k : ℕ) :
    (Matrix.fromBlocks P 0 0 R) ^ k = Matrix.fromBlocks (P ^ k) 0 0 (R ^ k) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih =>
    rw [pow_succ, ih, Matrix.fromBlocks_multiply]
    simp [pow_succ]

/-- Lower-right block of a polynomial evaluated at a block-diagonal matrix. Private helper. -/
private lemma zrs_aeval_fromBlocks_inr {m n : ℕ} (P : Mat m m) (R : Mat n n) (q : Polynomial ℝ)
    (i j : Fin n) :
    (Polynomial.aeval (Matrix.fromBlocks P 0 0 R) q) (Sum.inr i) (Sum.inr j)
      = (Polynomial.aeval R q) i j := by
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial k a =>
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, zrs_fromBlocks_diag_pow,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_mul, smul_mul,
      one_mul, one_mul]
    simp

private lemma zrs_ur (h : ℝ → ℝ) {m n : ℕ} (K : Mat m n) :
    upperRight (cfc (fun x : ℝ => x * h (x ^ 2)) (hermDilation K)) = K * cfc h (Kᵀ * K) := by
  have hsaR : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hsaX : IsSelfAdjoint (hermDilation K) := Muon.Foundations.hermDilation_isHermitian K
  have hX : hermDilation K
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 K Kᵀ 0) := rfl
  have hmul : ∀ M N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ,
      Matrix.reindex finSumFinEquiv finSumFinEquiv M * Matrix.reindex finSumFinEquiv finSumFinEquiv N
        = Matrix.reindex finSumFinEquiv finSumFinEquiv (M * N) :=
    fun M N => (map_mul (reindexAlgEquiv ℝ ℝ finSumFinEquiv) M N).symm
  have hX2 : hermDilation K ^ 2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) := by
    rw [sq, hX, hmul]
    congr 1
    rw [Matrix.fromBlocks_multiply]
    simp
  have hspec2 : spectrum ℝ (hermDilation K ^ 2) ⊆ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K) := by
    intro x hx
    have h1 : spectrum ℝ (Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K))) = spectrum ℝ (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) :=
      AlgEquiv.spectrum_eq (reindexAlgEquiv ℝ ℝ finSumFinEquiv) _
    rw [hX2, h1] at hx
    exact zrs_spectrum_fromBlocks_diag_sub _ _ hx
  have hPf : (spectrum ℝ (K * Kᵀ)).Finite := Matrix.finite_real_spectrum
  have hRf : (spectrum ℝ (Kᵀ * K)).Finite := Matrix.finite_real_spectrum
  set s : Finset ℝ := (hPf.union hRf).toFinset with hs
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Set.injOn_id _
  set q : Polynomial ℝ := Lagrange.interpolate s id h with hq
  have hqU : ∀ y ∈ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K),
      q.eval y = h y := by
    intro y hy
    have hys : y ∈ s := (hPf.union hRf).mem_toFinset.mpr hy
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id)
      (r := h) hinj hys
    simpa [hq] using this
  have hR_eq : cfc h (Kᵀ * K) = Polynomial.aeval (Kᵀ * K) q := by
    rw [← cfc_polynomial q (Kᵀ * K) hsaR]
    exact cfc_congr' fun y hy => (hqU y (Or.inr hy)).symm
  have hφ : cfc (fun x : ℝ => x * h (x ^ 2)) (hermDilation K)
      = hermDilation K * Polynomial.aeval (hermDilation K ^ 2) q := by
    have hcongr : cfc (fun x : ℝ => x * h (x ^ 2)) (hermDilation K)
        = cfc (fun x : ℝ => (Polynomial.X * q.comp (Polynomial.X ^ 2)).eval x) (hermDilation K) := by
      apply cfc_congr'
      intro x hx
      have hx2 : x ^ 2 ∈ spectrum ℝ (K * Kᵀ) ∪ spectrum ℝ (Kᵀ * K) :=
        hspec2 (spectrum.pow_image_subset (hermDilation K) 2 ⟨x, hx, rfl⟩)
      simp only [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_pow, hqU _ hx2]
    rw [hcongr, cfc_polynomial _ _ hsaX, Polynomial.aeval_mul, Polynomial.aeval_X,
      Polynomial.aeval_comp, Polynomial.aeval_X_pow]
  have hA : Polynomial.aeval (hermDilation K ^ 2) q = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Polynomial.aeval (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) q) := by
    rw [hX2]
    exact Polynomial.aeval_algHom_apply (reindexAlgEquiv ℝ ℝ finSumFinEquiv).toAlgHom _ q
  rw [hφ, hA, hX, hmul]
  rw [hR_eq]
  ext i j
  simp [upperRight, Matrix.reindex_apply, Matrix.mul_apply, Fintype.sum_sum_type,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    zrs_aeval_fromBlocks_inr]


private lemma zr_sharp_svd (φ : ℝ → ℝ) (hodd : ∀ x, φ (-x) = -φ x) {m n r : ℕ} (K : Mat m n)
    (s : Fin r → ℝ) (p : Fin r → Vec m) (q : Fin r → Vec n) (hs : ∀ k, 0 < s k)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    oddSharp φ K = ∑ k, φ (s k) • outer (p k) (q k) := by
  set h : ℝ → ℝ := fun y => φ (Real.sqrt y) / Real.sqrt y with hh
  have hφ : φ = fun x : ℝ => x * h (x ^ 2) := by
    funext x
    simp only [hh]
    rw [Real.sqrt_sq_eq_abs]
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [abs_of_neg hx]
      have : φ (-x) = -φ x := hodd x
      rw [this]
      have hx0 : x ≠ 0 := hx.ne
      field_simp
    · subst hx
      have : φ 0 = 0 := by have := hodd 0; simp at this; linarith
      simp [this]
    · rw [abs_of_pos hx]; field_simp
  have hsa : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set C := cfc h (Kᵀ * K) with hC
  have hCt : Cᵀ = C := by
    have h : IsSelfAdjoint C := cfc_predicate h (Kᵀ * K)
    have h2 := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hvec : ∀ l, vecMul (q l) C = h (s l ^ 2) • q l := by
    intro l
    obtain ⟨h1, h2⟩ := zr_svd_mulVec K s p q hp hq hK l
    have hev : (Kᵀ * K) *ᵥ q l = (s l ^ 2) • q l := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul, sq]
    rw [← Matrix.mulVec_transpose, hCt]
    exact zr_cfc_mulVec_eq_smul h _ _ _ hsa hev
  have hsq : ∀ k, s k * h (s k ^ 2) = φ (s k) := fun k => by
    conv_rhs => rw [hφ]
  unfold oddSharp
  rw [hφ, zrs_ur h K, ← hC]
  conv_lhs => rw [hK]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.vecMulVec_mul, hvec k, Matrix.vecMulVec_smul, smul_smul]

end ZrSharp


section ZrSharpIp
open scoped Matrix
open Muon.Volatility (oddSharp)

private lemma zr_sharp_data {m n : ℕ} (P : Mat m m) (K : Mat m n) :
    ∃ (r : ℕ) (s c : Fin r → ℝ), (∀ k, 0 ≤ c k) ∧ ∑ k, c k ≤ zr_ip P P ∧
      ∀ φ : ℝ → ℝ, (∀ x, φ (-x) = -φ x) →
        zr_ip (P * oddSharp φ K) (P * oddSharp φ K) = ∑ k, φ (s k) ^ 2 * c k := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  have hs : ∀ k : Fin K.rank, 0 < (Matrix.toEuclideanLin K).singularValues (k : ℕ) :=
    fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.2
  set sv : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hsv
  refine ⟨K.rank, sv, fun k => (P *ᵥ p k) ⬝ᵥ (P *ᵥ p k), fun k => ?_, ?_, ?_⟩
  · simp only [dotProduct]
    exact Finset.sum_nonneg fun a _ => mul_self_nonneg _
  · rw [zr_ip_eq]
    have e : ∀ k, (P *ᵥ p k) ⬝ᵥ (P *ᵥ p k) = ∑ a, (p k ⬝ᵥ (fun b => P a b)) ^ 2 := by
      intro k
      simp only [dotProduct, Matrix.mulVec, sq]
      refine Finset.sum_congr rfl fun a _ => ?_
      congr 1 <;> exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    simp_rw [e]
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum fun a _ => ?_
    have := zr_bessel p hp (fun b => P a b)
    simpa [dotProduct, sq] using this
  · intro φ hφ
    rw [zr_sharp_svd φ hφ K sv p r hs hp hr hK, Matrix.mul_sum]
    have hPQ : ∀ k, P * (φ (sv k) • outer (p k) (r k)) = φ (sv k) • outer (P *ᵥ p k) (r k) := by
      intro k
      rw [Matrix.mul_smul, Matrix.mul_vecMulVec]
    simp_rw [hPQ]
    rw [zr_ip_outer_sum _ _ _ hr]

private lemma zr_dom_mat {m n : ℕ} (P : Mat m m) (K : Mat m n) (φ ψ : ℝ → ℝ)
    (hφ : ∀ x, φ (-x) = -φ x) (hψ : ∀ x, ψ (-x) = -ψ x) (lam : ℝ)
    (hdom : ∀ x, φ x ^ 2 ≤ lam * (1 - ψ x ^ 2)) (hψ1 : ∀ x, ψ x ^ 2 ≤ 1) :
    zr_ip (P * oddSharp φ K) (P * oddSharp φ K) ≤
      lam * (zr_ip P P - zr_ip (P * oddSharp ψ K) (P * oddSharp ψ K)) := by
  obtain ⟨r, s, c, hc0, hcs, hf⟩ := zr_sharp_data P K
  rw [hf φ hφ, hf ψ hψ]
  have hlam : 0 ≤ lam := by
    have := hdom 0
    have h0 : φ 0 = 0 := by have := hφ 0; simp at this; linarith
    have h1 : ψ 0 = 0 := by have := hψ 0; simp at this; linarith
    rw [h0, h1] at this; linarith
  calc ∑ k, φ (s k) ^ 2 * c k ≤ ∑ k, lam * ((1 - ψ (s k) ^ 2) * c k) :=
        Finset.sum_le_sum fun k _ => by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hdom _) (hc0 k)
    _ = lam * ∑ k, ((1 - ψ (s k) ^ 2) * c k) := by rw [Finset.mul_sum]
    _ ≤ lam * (zr_ip P P - ∑ k, ψ (s k) ^ 2 * c k) := by
        apply mul_le_mul_of_nonneg_left _ hlam
        have : ∑ k, ((1 - ψ (s k) ^ 2) * c k) = ∑ k, c k - ∑ k, ψ (s k) ^ 2 * c k := by
          rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun k _ => by ring
        linarith

private lemma zr_sharp_bound {m n : ℕ} (P : Mat m m) (K : Mat m n) (φ : ℝ → ℝ)
    (hφ : ∀ x, φ (-x) = -φ x) (C : ℝ) (hC : ∀ x, φ x ^ 2 ≤ C) :
    zr_ip (P * oddSharp φ K) (P * oddSharp φ K) ≤ C * zr_ip P P := by
  obtain ⟨r, s, c, hc0, hcs, hf⟩ := zr_sharp_data P K
  rw [hf φ hφ]
  calc ∑ k, φ (s k) ^ 2 * c k ≤ ∑ k, C * c k :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hC _) (hc0 k)
    _ = C * ∑ k, c k := by rw [Finset.mul_sum]
    _ ≤ C * zr_ip P P := by
        apply mul_le_mul_of_nonneg_left hcs
        have := hC 0
        have := sq_nonneg (φ 0)
        linarith

end ZrSharpIp


section ZrModelGen
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_fro_cont {m n : ℕ} : Continuous (fun K : Mat m n => fro K) := by
  unfold fro
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  have : Continuous fun K : Mat m n => K i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (continuous_norm.comp this).pow 2

private lemma zr_sharp_cont {m n : ℕ} (φ : ℝ → ℝ) (hφ : IsOddBddLip φ) :
    Continuous (fun K : Mat m n => oddSharp φ K) := by
  refine continuous_iff_continuousAt.mpr fun K0 => ?_
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_dist_tendsto_zero]
  have hb : Continuous fun K : Mat m n => lipConst φ * fro (K - K0) :=
    continuous_const.mul (zr_fro_cont.comp (continuous_id.sub continuous_const))
  have h0 := hb.tendsto K0
  have hz : fro (K0 - K0) = 0 := by simp [fro]
  rw [hz, mul_zero] at h0
  refine squeeze_zero (fun K => dist_nonneg) (fun K => ?_) h0
  rw [Real.dist_eq]
  have h1 := (lem_app_vol_sharp_i φ hφ K K0).2.2
  have h2 : |(oddSharp φ K - oddSharp φ K0) i j| ≤ fro (oddSharp φ K - oddSharp φ K0) := by
    unfold fro
    refine Real.abs_le_sqrt ?_
    calc (oddSharp φ K - oddSharp φ K0) i j ^ 2 = ‖(oddSharp φ K - oddSharp φ K0) i j‖ ^ 2 := by
          rw [Real.norm_eq_abs, sq_abs]
      _ ≤ ∑ j', ‖(oddSharp φ K - oddSharp φ K0) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖(oddSharp φ K - oddSharp φ K0) i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖(oddSharp φ K - oddSharp φ K0) i' j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', ‖(oddSharp φ K - oddSharp φ K0) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  simpa using h2.trans h1

private lemma zr_obl_le {φ : ℝ → ℝ} (hφ : IsOddBddLip φ) (x : ℝ) : |φ x| ≤ supNorm φ := by
  obtain ⟨M, hM⟩ := hφ.2.1
  exact le_ciSup (f := fun x => |φ x|) ⟨M, by rintro _ ⟨y, rfl⟩; exact hM y⟩ x

private lemma zr_sharp_meas {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (φ : ℝ → ℝ)
    (hφ : IsOddBddLip φ) (P : Mat m m) {U : Ω → Mat m n} (hU : Measurable U) :
    Measurable (fun ω => P * oddSharp φ (U ω)) := by
  haveI := zr_borel m n
  haveI := zr_sc m n
  have hc : Continuous (fun K : Mat m n => P * oddSharp φ K) :=
    continuous_const.matrix_mul (zr_sharp_cont φ hφ)
  exact hc.measurable.comp hU

end ZrModelGen


section ZrModelGen2
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_model_gen (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    ∃ c : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℤ → ℤ → ℝ,
      (∀ φ1 φ2 : ℝ → ℝ, IsOddBddLip φ1 → IsOddBddLip φ2 → ∀ (t : ℤ) (ℓ : ℕ),
        Tendsto (fun k => c k φ1 φ2 t (t + (ℓ : ℤ))) atTop
          (𝓝 ((B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
            (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) φ1 φ2))) ∧
      (∀ k φ1 φ2 t t', IsOddBddLip φ1 → IsOddBddLip φ2 →
        c k φ1 φ2 t t' ^ 2 ≤ c k φ1 φ1 t t * c k φ2 φ2 t' t') ∧
      (∀ k φ ψ lam t, IsOddBddLip φ → IsOddBddLip ψ → (∀ x, φ x ^ 2 ≤ lam * (1 - ψ x ^ 2)) →
        (∀ x, ψ x ^ 2 ≤ 1) → c k φ φ t t ≤ lam * (1 - c k ψ ψ t t)) ∧
      (∀ k φ t, IsOddBddLip φ → 0 ≤ c k φ φ t t) := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS, hSout, hSin⟩ := zr_setup' hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  obtain ⟨R, hmR, hnR, hBR, hγR, hCR, hβR, hloR, hhiR, hR⟩ :=
    def_app_vol_replication_regime Fp S γstar CSig 1 1 hC1 hS hN hN ⟨one_pos, le_rfl⟩
  rcases R with ⟨rm, rn, rB, rF, rprop, rγ, rC, rhC, rdims, rnormO, rnormI,
    rβ, rhβ, rlo, rhi, rhϱ, rdiff⟩
  dsimp only at hmR hnR hBR hγR hCR hβR hloR hhiR hR
  subst rm rn rB rγ rC rβ rlo rhi
  have hCov : ∀ k, (rF k).C = replCov Fp.C (k + 1) := fun k => eq_of_heq (hR k).1
  have hspec : ∀ k, ∃ Sp : SpectralData (rF k).C,
      Sp.μ = replVec (k + 1) S.μ ∧ Sp.lam = replVec (k + 1) S.lam := by
    intro k
    rw [hCov k]
    obtain ⟨Sp, -, -, hμ, hl⟩ := zr_exists_replSpec Fp.C S (k + 1)
    exact ⟨Sp, hμ, hl⟩
  choose Sp hSpμ hSpl using hspec
  have hSize : SizeSeq (B := fun k => (k + 1) * B) (fun k => (rF k).C) γstar CSig
      rprop.γout rprop.γin :=
    ⟨fun k => ⟨rdims k, rnormO k, rnormI k⟩, rprop.B_top, rprop.ratio_in, rprop.ratio_out⟩
  have hbeta : ∀ k, (rF k).β ≤ β := fun k => by rw [rhβ k, hβ]
  obtain ⟨Fd, hFd⟩ : ∃ Fd : ∀ k, Fin ((k + 1) * N) → ℝ,
      ∀ k, Fd k = replVec (k + 1) (Pi.single i (1 : ℝ) : Fin N → ℝ) := ⟨fun k => _, fun _ => rfl⟩
  obtain ⟨Gd, hGd⟩ : ∃ Gd : ∀ k, Fin ((k + 1) * N) → ℝ,
      ∀ k, Gd k = replVec (k + 1) (fun _ : Fin N => (1 : ℝ)) := ⟨fun k => _, fun _ => rfl⟩
  have hd01 : ∀ k j, Fd k j = 0 ∨ Fd k j = 1 := by
    intro k j
    rw [hFd]
    simp only [replVec, Pi.single_apply]
    split_ifs <;> simp
  have hGone : ∀ k j, Gd k j = 1 := by
    intro k j
    rw [hGd]
    rfl
  have hGm : ∀ k, (Sp k).vIn * Matrix.diagonal (Gd k) * (Sp k).vInᵀ = 1 := by
    intro k
    have h1 : Matrix.diagonal (Gd k) = 1 := by
      have : Gd k = fun _ => 1 := funext (hGone k)
      rw [this]
      exact Matrix.diagonal_one
    rw [h1, Matrix.mul_one]
    exact mul_eq_one_comm.mp (Sp k).hvIn
  have hsumF : ∀ k, ∑ j, Fd k j = ((k : ℝ) + 1) := by
    intro k
    rw [hFd, zr_sum_repl]
    simp
  obtain ⟨P, hP⟩ : ∃ P : ∀ k, Mat ((k + 1) * N) ((k + 1) * N),
      ∀ k, P k = (Sp k).uOut * Matrix.diagonal (Fd k) * (Sp k).uOutᵀ := ⟨fun k => _, fun _ => rfl⟩
  have hPf : ∀ k, (P k)ᵀ = P k ∧ P k * P k = P k ∧ zr_ip (P k) (P k) = (k : ℝ) + 1 := by
    intro k
    obtain ⟨h1, h2, h3⟩ := zr_proj_facts (Sp k).uOut (Sp k).huOut (Fd k) (hd01 k)
    rw [hP]
    exact ⟨h1, h2, h3.trans (hsumF k)⟩
  have hnpos : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := fun k => by positivity
  obtain ⟨T, hT⟩ : ∃ T : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℤ → ℤ → ℝ, ∀ k φ1 φ2 t t', T k φ1 φ2 t t' =
      ∫ ω, Matrix.trace (P k * oddSharp φ1 (def_app_vol_product (rF k) ω t) *
        (1 : Mat ((k + 1) * N) ((k + 1) * N)) *
        (oddSharp φ2 (def_app_vol_product (rF k) ω t'))ᵀ) ∂(indepSpaceLaw ((k + 1) * N) ((k + 1) * N) ((k + 1) * B)) :=
    ⟨fun k φ1 φ2 t t' => _, fun _ _ _ _ _ => rfl⟩
  have hT' : ∀ k φ1 φ2 t t', T k φ1 φ2 t t' =
      ∫ ω, zr_ip (P k * oddSharp φ1 (def_app_vol_product (rF k) ω t))
        (P k * oddSharp φ2 (def_app_vol_product (rF k) ω t')) ∂(indepSpaceLaw ((k + 1) * N) ((k + 1) * N) ((k + 1) * B)) := by
    intro k φ1 φ2 t t'
    rw [hT]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Matrix.mul_one]
    exact zr_trace_proj (P k) (hPf k).1 (hPf k).2.1 _ _
  have hmeas : ∀ k (φ : ℝ → ℝ), IsOddBddLip φ → ∀ t, Measurable (fun ω =>
      P k * oddSharp φ (def_app_vol_product (rF k) ω t)) :=
    fun k φ hφ t => zr_sharp_meas φ hφ (P k) (zr_prod_meas (rF k) t)
  have hbdd : ∀ k (φ : ℝ → ℝ), IsOddBddLip φ → ∀ ω t,
      zr_ip (P k * oddSharp φ (def_app_vol_product (rF k) ω t))
        (P k * oddSharp φ (def_app_vol_product (rF k) ω t)) ≤ supNorm φ ^ 2 * ((k : ℝ) + 1) := by
    intro k φ hφ ω t
    have := zr_sharp_bound (P k) (def_app_vol_product (rF k) ω t) φ hφ.1 (supNorm φ ^ 2)
      (fun x => by
        rw [← sq_abs (φ x)]
        exact pow_le_pow_left₀ (abs_nonneg _) (zr_obl_le hφ x) 2)
    rwa [(hPf k).2.2] at this
  refine ⟨fun k φ1 φ2 t t' => ((k : ℝ) + 1)⁻¹ * T k φ1 φ2 t t', ?_, ?_, ?_, ?_⟩
  · intro φ1 φ2 h1 h2 t ℓ
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hBpos : (0 : ℝ) < B := Nat.cast_pos.mpr hB
    have h := lag_closure_generic cert γstar CSig rprop.γout rprop.γin hC1
      (fun k => (k + 1) * N) (fun k => (k + 1) * N) (fun k => (k + 1) * B) rF Sp hSize β hβ1 hbeta
      ℓ φ1 φ2 h1 h2 (ε / (2 * B)) (by positivity)
    filter_upwards [h] with k hk
    have hk' := hk t (Fd k) (Gd k) (P k) ((Sp k).vIn * Matrix.diagonal (Gd k) * (Sp k).vInᵀ)
      (hP k) rfl (by rw [hP]; exact zr_opNorm_conj_diag _ (Sp k).huOut _ (fun j => by
        rcases hd01 k j with h | h <;> simp [h]))
      (zr_opNorm_conj_diag _ (Sp k).hvIn _ (fun j => by simp [hGone k j]))
    rw [hGm k] at hk'
    have hrepl := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hC1 ℓ
      φ1 φ2 h1 h2).2.2.2.2.2 (k + 1) (Nat.succ_pos k)
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
    rw [rhβ k, hSpμ k, hSpl k, hFd, hGd, hrepl, hβ, hμ, hlam] at hk'
    simp only [contraction, MeasureTheory.integral_const_mul] at hk'
    rw [← hT k φ1 φ2 t (t + (ℓ : ℤ))] at hk'
    rw [Real.dist_eq]
    set L := lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) φ1 φ2 with hL
    have hn := hnpos k
    have e : ((k : ℝ) + 1)⁻¹ * T k φ1 φ2 t (t + (ℓ : ℤ)) - (B : ℝ) * L =
        (B : ℝ) * ((((k + 1) * B : ℕ) : ℝ)⁻¹ * T k φ1 φ2 t (t + (ℓ : ℤ)) - L) := by
      push_cast
      field_simp
    rw [e, abs_mul, abs_of_pos hBpos]
    calc (B : ℝ) * |(((k + 1) * B : ℕ) : ℝ)⁻¹ * T k φ1 φ2 t (t + (ℓ : ℤ)) - L|
        ≤ (B : ℝ) * (ε / (2 * B)) := mul_le_mul_of_nonneg_left hk' hBpos.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  · intro k φ1 φ2 t t' h1 h2
    have hn := hnpos k
    haveI := zr_prob ((k + 1) * N) ((k + 1) * N) ((k + 1) * B)
    have hρ0 : 0 ≤ supNorm φ2 ^ 2 * ((k : ℝ) + 1) := by positivity
    have hρ1 : 0 ≤ supNorm φ1 ^ 2 * ((k : ℝ) + 1) := by positivity
    have cs := zr_int_cs (μ := indepSpaceLaw ((k + 1) * N) ((k + 1) * N) ((k + 1) * B))
      (hmeas k φ1 h1 t) (hmeas k φ2 h2 t')
      (supNorm φ1 ^ 2 * ((k : ℝ) + 1) + supNorm φ2 ^ 2 * ((k : ℝ) + 1))
      (fun ω => (hbdd k φ1 h1 ω t).trans (by linarith))
      (fun ω => (hbdd k φ2 h2 ω t').trans (by linarith))
    rw [← hT' k φ1 φ2 t t', ← hT' k φ1 φ1 t t, ← hT' k φ2 φ2 t' t'] at cs
    calc (((k : ℝ) + 1)⁻¹ * T k φ1 φ2 t t') ^ 2 = (((k : ℝ) + 1)⁻¹) ^ 2 * T k φ1 φ2 t t' ^ 2 := by ring
      _ ≤ (((k : ℝ) + 1)⁻¹) ^ 2 * (T k φ1 φ1 t t * T k φ2 φ2 t' t') :=
          mul_le_mul_of_nonneg_left cs (sq_nonneg _)
      _ = _ := by ring
  · intro k φ ψ lam t hφ hψ hdom hψ1
    have hn := hnpos k
    haveI := zr_prob ((k + 1) * N) ((k + 1) * N) ((k + 1) * B)
    set μk := indepSpaceLaw ((k + 1) * N) ((k + 1) * N) ((k + 1) * B) with hμk
    have iφ := zr_int_ip (μ := μk) (hmeas k φ hφ t) (hmeas k φ hφ t) (supNorm φ ^ 2 * ((k : ℝ) + 1))
      (fun ω => hbdd k φ hφ ω t) (fun ω => hbdd k φ hφ ω t)
    have iψ := zr_int_ip (μ := μk) (hmeas k ψ hψ t) (hmeas k ψ hψ t) (supNorm ψ ^ 2 * ((k : ℝ) + 1))
      (fun ω => hbdd k ψ hψ ω t) (fun ω => hbdd k ψ hψ ω t)
    have hpt : ∀ ω, zr_ip (P k * oddSharp φ (def_app_vol_product (rF k) ω t))
          (P k * oddSharp φ (def_app_vol_product (rF k) ω t)) ≤
        lam * (((k : ℝ) + 1) - zr_ip (P k * oddSharp ψ (def_app_vol_product (rF k) ω t))
          (P k * oddSharp ψ (def_app_vol_product (rF k) ω t))) := fun ω => by
      have := zr_dom_mat (P k) (def_app_vol_product (rF k) ω t) φ ψ hφ.1 hψ.1 lam hdom hψ1
      rwa [(hPf k).2.2] at this
    have hint : T k φ φ t t ≤ lam * (((k : ℝ) + 1) - T k ψ ψ t t) := by
      rw [hT', hT']
      calc _ ≤ ∫ ω, lam * (((k : ℝ) + 1) - zr_ip (P k * oddSharp ψ (def_app_vol_product (rF k) ω t))
              (P k * oddSharp ψ (def_app_vol_product (rF k) ω t))) ∂μk :=
            integral_mono iφ ((integrable_const _).sub iψ |>.const_mul lam) hpt
        _ = _ := by
            rw [integral_const_mul, integral_sub (integrable_const _) iψ]
            simp
            exact Or.inl rfl
    calc ((k : ℝ) + 1)⁻¹ * T k φ φ t t ≤ ((k : ℝ) + 1)⁻¹ * (lam * (((k : ℝ) + 1) - T k ψ ψ t t)) :=
          mul_le_mul_of_nonneg_left hint (inv_nonneg.2 hn.le)
      _ = lam * (1 - ((k : ℝ) + 1)⁻¹ * T k ψ ψ t t) := by field_simp
  · intro k φ t hφ
    have hn := hnpos k
    show 0 ≤ ((k : ℝ) + 1)⁻¹ * T k φ φ t t
    rw [hT']
    exact mul_nonneg (inv_nonneg.2 hn.le) (integral_nonneg fun ω => zr_ip_self_nonneg _)

end ZrModelGen2


section ZrRprops
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_Rprops (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ)
    (hR : ∀ ℓ f g, R ℓ f g = (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g) :
    (∀ (φ1 φ2 : ℝ → ℝ) (ℓ : ℕ), IsOddBddLip φ1 → IsOddBddLip φ2 →
      R ℓ φ1 φ2 ^ 2 ≤ R 0 φ1 φ1 * R 0 φ2 φ2) ∧
    (∀ (φ ψ : ℝ → ℝ) (lam : ℝ), IsOddBddLip φ → IsOddBddLip ψ →
      (∀ x, φ x ^ 2 ≤ lam * (1 - ψ x ^ 2)) → (∀ x, ψ x ^ 2 ≤ 1) →
      R 0 φ φ ≤ lam * (1 - R 0 ψ ψ)) ∧
    (∀ (φ : ℝ → ℝ), IsOddBddLip φ → 0 ≤ R 0 φ φ) ∧
    (∀ (ℓ : ℕ) (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      R ℓ (fun x => f x + c * f' x) g = R ℓ f g + c * R ℓ f' g) ∧
    (∀ (ℓ : ℕ) (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      R ℓ f (fun x => g x + c * g' x) = R ℓ f g + c * R ℓ f g') ∧
    (∀ (ℓ : ℕ) (f g : ℝ → ℝ), IsOddBddLip f → IsOddBddLip g →
      |R ℓ f g| ≤ ((B : ℝ) * γstar) * supNorm f * supNorm g) := by
  classical
  obtain ⟨c, hlim, hcs, hdom, hnn⟩ := zr_model_gen cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro φ1 φ2 ℓ h1 h2
    have a12 := hlim φ1 φ2 h1 h2 0 ℓ
    have a11 := hlim φ1 φ1 h1 h1 0 0
    have a22 := hlim φ2 φ2 h2 h2 (ℓ : ℤ) 0
    simp only [Nat.cast_zero, add_zero, zero_add] at a12 a11 a22
    rw [hR, hR, hR]
    exact le_of_tendsto_of_tendsto' (a12.pow 2) (a11.mul a22) fun k => by
      simpa using hcs k φ1 φ2 0 (ℓ : ℤ) h1 h2
  · intro φ ψ lam h1 h2 hd hψ
    have a1 := hlim φ φ h1 h1 0 0
    have a2 := hlim ψ ψ h2 h2 0 0
    simp only [Nat.cast_zero, add_zero] at a1 a2
    rw [hR, hR]
    exact le_of_tendsto_of_tendsto' a1 ((tendsto_const_nhds.sub a2).const_mul lam) fun k =>
      hdom k φ ψ lam 0 h1 h2 hd hψ
  · intro φ h1
    have a1 := hlim φ φ h1 h1 0 0
    simp only [Nat.cast_zero, add_zero] at a1
    rw [hR]
    exact ge_of_tendsto' a1 fun k => hnn k φ 0 h1
  all_goals
    obtain ⟨Fp, S, hβ, hμ, hlam, hS, -, -⟩ := zr_setup' hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  · intro ℓ f f' g c hf hf' hg
    have := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hC1 ℓ f g hf hg).2.2.2.1
      c f' hf' (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
    simp only [hβ, hμ, hlam] at this
    rw [hR, hR, hR, this]; ring
  · intro ℓ f g g' c hf hg hg'
    have := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hC1 ℓ f g hf hg).2.2.2.2.1
      c g' hg' (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
    simp only [hβ, hμ, hlam] at this
    rw [hR, hR, hR, this]; ring
  · intro ℓ f g hf hg
    have h := (thm_app_vol_lag_kernel_bilinear_bound_replication cert γstar CSig Fp S hS hC1 ℓ f g hf hg).1
      (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ)
      (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ)
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) rfl rfl
    simp only [hβ, hμ, hlam] at h
    have hF : opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) ≤ 1 :=
      zr_opNorm_conj_diag _ S.huOut _ (fun j => by
        by_cases h : j = i <;> simp [Pi.single_apply, h])
    have hG : opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) ≤ 1 :=
      zr_opNorm_conj_diag _ S.hvIn _ (fun j => by simp)
    have hF0 : 0 ≤ opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) := by
      open scoped Matrix.Norms.L2Operator in
      rw [opNorm_eq_norm]; exact norm_nonneg _
    have hG0 : 0 ≤ opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) := by
      open scoped Matrix.Norms.L2Operator in
      rw [opNorm_eq_norm]; exact norm_nonneg _
    have hγ0 : 0 ≤ γstar := by
      have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
      linarith
    have hf0 : 0 ≤ supNorm f := Real.iSup_nonneg fun _ => abs_nonneg _
    have hg0 : 0 ≤ supNorm g := Real.iSup_nonneg fun _ => abs_nonneg _
    rw [hR, abs_mul, abs_of_nonneg (Nat.cast_nonneg B)]
    have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
    calc (B : ℝ) * |lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) f g|
        ≤ (B : ℝ) * (γstar * opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) *
          opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) * supNorm f * supNorm g) :=
          mul_le_mul_of_nonneg_left h hB0
      _ ≤ (B : ℝ) * (γstar * 1 * 1 * supNorm f * supNorm g) := by
          apply mul_le_mul_of_nonneg_left _ hB0
          gcongr
      _ = _ := by ring

end ZrRprops


section ZrMain
open Muon.Volatility (supNorm IsOddBddLip omegaT)

private lemma zr_main_est (R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hcs : ∀ (φ1 φ2 : ℝ → ℝ) (ℓ : ℕ), IsOddBddLip φ1 → IsOddBddLip φ2 →
      R ℓ φ1 φ2 ^ 2 ≤ R 0 φ1 φ1 * R 0 φ2 φ2)
    (hdom : ∀ (φ ψ : ℝ → ℝ) (lam : ℝ), IsOddBddLip φ → IsOddBddLip ψ →
      (∀ x, φ x ^ 2 ≤ lam * (1 - ψ x ^ 2)) → (∀ x, ψ x ^ 2 ≤ 1) →
      R 0 φ φ ≤ lam * (1 - R 0 ψ ψ))
    (hnn : ∀ φ : ℝ → ℝ, IsOddBddLip φ → 0 ≤ R 0 φ φ)
    (hlin1 : ∀ (ℓ : ℕ) (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      R ℓ (fun x => f x + c * f' x) g = R ℓ f g + c * R ℓ f' g)
    (hlin2 : ∀ (ℓ : ℕ) (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      R ℓ f (fun x => g x + c * g' x) = R ℓ f g + c * R ℓ f g')
    (hbd : ∀ (ℓ : ℕ) (f g : ℝ → ℝ), IsOddBddLip f → IsOddBddLip g →
      |R ℓ f g| ≤ Cb * supNorm f * supNorm g)
    (ℓ : ℕ) {ϱ δ T : ℝ} (hϱ : 0 < ϱ) (hδ : 0 < δ) (hδT : δ ≤ T) :
    |R ℓ (omegaT ϱ T) (omegaT ϱ T) -
        R ℓ (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)
          (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)| ≤
      2 * Real.sqrt (8 * Cb * (1 - R 0 (omegaF (δ ^ 2)) (omegaF (δ ^ 2)))) := by
  have hT : 0 < T := hδ.trans_le hδT
  set b : ℝ → ℝ := fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x with hb
  set a : ℝ → ℝ := omegaT ϱ δ with ha
  set w : ℝ → ℝ := omegaT ϱ T with hw
  have haobl : IsOddBddLip a := zrb_F_obl (s0 := ϱ) hϱ hδ.le (fun y _ => by nlinarith [sq_nonneg y])
  have hwobl : IsOddBddLip w := zrb_F_obl (s0 := ϱ) hϱ hT.le (fun y _ => by nlinarith [sq_nonneg y])
  have hbobl : IsOddBddLip b := zrb_F_obl (s0 := ϱ) hϱ hδT (fun y _ => by nlinarith [sq_nonneg y])
  have hψobl : IsOddBddLip (omegaF (δ ^ 2)) :=
    (Muon.Volatility.lem_app_vol_sharp_ii one_pos (by positivity : 0 < δ ^ 2)).2.1
  have hwab : w = fun x => a x + 1 * b x := by
    funext x
    simp only [hw, ha, hb, omegaT, one_mul]
    have i1 : IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume 0 δ :=
      ((zrb_iota_cont (s0 := ϱ) hϱ (fun y _ => by nlinarith [sq_nonneg y]) x).mono
        (Icc_subset_Icc le_rfl (le_refl δ))).intervalIntegrable_of_Icc hδ.le
    have i2 : IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume δ T :=
      ((zrb_iota_cont (a := δ) (b := T) (s0 := ϱ) hϱ (fun y _ => by nlinarith [sq_nonneg y]) x)).intervalIntegrable_of_Icc hδT
    rw [← mul_add, intervalIntegral.integral_add_adjacent_intervals i1 i2]
  have hwn : ∀ x, |w x| ≤ 1 := fun x => zrd_omegaT_abs hϱ hT x
  have han : ∀ x, |a x| ≤ 1 := fun x => zrd_omegaT_abs hϱ hδ x
  have hbn : ∀ x, |b x| ≤ 2 := fun x => by
    have : b x = w x - a x := by
      have := congrFun hwab x
      simp only [one_mul] at this; linarith
    rw [this]
    calc |w x - a x| ≤ |w x| + |a x| := abs_sub _ _
      _ ≤ 1 + 1 := add_le_add (hwn x) (han x)
      _ = 2 := by norm_num
  have sw : supNorm w ≤ 1 := zrb_supNorm_le hwn
  have sa : supNorm a ≤ 1 := zrb_supNorm_le han
  have sb : supNorm b ≤ 2 := zrb_supNorm_le hbn
  have hs0 : ∀ f : ℝ → ℝ, 0 ≤ supNorm f := fun f => Real.iSup_nonneg fun _ => abs_nonneg _
  -- squared-norm bounds
  have R0w : R 0 w w ≤ Cb := by
    have := hbd 0 w w hwobl hwobl
    calc R 0 w w ≤ |R 0 w w| := le_abs_self _
      _ ≤ Cb * supNorm w * supNorm w := this
      _ ≤ Cb * 1 * 1 := mul_le_mul (mul_le_mul_of_nonneg_left sw hCb) sw (hs0 w) (by positivity)
      _ = Cb := by ring
  have R0b : R 0 b b ≤ 4 * Cb := by
    have := hbd 0 b b hbobl hbobl
    calc R 0 b b ≤ |R 0 b b| := le_abs_self _
      _ ≤ Cb * supNorm b * supNorm b := this
      _ ≤ Cb * 2 * 2 := mul_le_mul (mul_le_mul_of_nonneg_left sb hCb) sb (hs0 b) (by positivity)
      _ = 4 * Cb := by ring
  set D := 1 - R 0 (omegaF (δ ^ 2)) (omegaF (δ ^ 2)) with hD
  have R0a : R 0 a a ≤ 2 * D := hdom a (omegaF (δ ^ 2)) 2 haobl hψobl (zrd_a_sq hϱ hδ)
    (fun x => by
      have := zrd_omegaF_abs (ϱ := δ ^ 2) (by positivity) x
      nlinarith [abs_nonneg (omegaF (δ ^ 2) x), sq_abs (omegaF (δ ^ 2) x)])
  have R0a0 := hnn a haobl
  have hD0 : 0 ≤ D := by linarith
  have R0w0 := hnn w hwobl
  have R0b0 := hnn b hbobl
  have e1 : R ℓ w w = R ℓ a w + R ℓ b w := by
    have := hlin1 ℓ a b w 1 haobl hbobl hwobl
    rw [one_mul] at this
    calc R ℓ w w = R ℓ (fun x => a x + 1 * b x) w := by rw [← hwab]
      _ = _ := this
  have e2 : R ℓ b w = R ℓ b a + R ℓ b b := by
    have := hlin2 ℓ b a b 1 hbobl haobl hbobl
    rw [one_mul] at this
    calc R ℓ b w = R ℓ b (fun x => a x + 1 * b x) := by rw [← hwab]
      _ = _ := this
  have c1 : |R ℓ a w| ≤ Real.sqrt (8 * Cb * D) := by
    refine Real.abs_le_sqrt ?_
    calc R ℓ a w ^ 2 ≤ R 0 a a * R 0 w w := hcs a w ℓ haobl hwobl
      _ ≤ (2 * D) * Cb := mul_le_mul R0a R0w R0w0 (by positivity)
      _ ≤ 8 * Cb * D := by nlinarith [mul_nonneg hCb hD0]
  have c2 : |R ℓ b a| ≤ Real.sqrt (8 * Cb * D) := by
    refine Real.abs_le_sqrt ?_
    calc R ℓ b a ^ 2 ≤ R 0 b b * R 0 a a := hcs b a ℓ hbobl haobl
      _ ≤ (4 * Cb) * (2 * D) := mul_le_mul R0b R0a R0a0 (by positivity)
      _ = 8 * Cb * D := by ring
  have : R ℓ w w - R ℓ b b = R ℓ a w + R ℓ b a := by rw [e1, e2]; ring
  show |R ℓ w w - R ℓ b b| ≤ _
  rw [this]
  calc _ ≤ |R ℓ a w| + |R ℓ b a| := abs_add_le _ _
    _ ≤ _ := by linarith

end ZrMain


section ZrSqTrunc
open scoped Matrix
open Muon.Setup Muon.Volatility

private lemma zr_sq_trunc (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) {ϱ T : ℝ} (hϱ : 0 < ϱ) (hT : 1 ≤ T) :
    |(B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) -
      (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) (omegaT ϱ T) (omegaT ϱ T)| ≤
      4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * T) := by
  classical
  obtain ⟨Fp, S, hβ, hμ, hlam, hS, -, -⟩ := zr_setup' hB μ hpos hβ0 hβ1 hγ hμC hC1 i
  obtain ⟨R, hR⟩ : ∃ R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ, ∀ ℓ f g, R ℓ f g = (B : ℝ) *
      lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) f g := ⟨fun ℓ f g => _, fun _ _ _ => rfl⟩
  obtain ⟨-, -, -, h1, h2, h3⟩ := zr_Rprops cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i R hR
  have hTpos : 0 < T := by linarith
  have hH := zrb_H2 (R ℓ) ((B : ℝ) * γstar) (by
      have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
      have : 0 ≤ γstar := by linarith
      positivity)
    (fun f f' g c hf hf' hg => h1 ℓ f f' g c hf hf' hg)
    (fun f g g' c hf hg hg' => h2 ℓ f g g' c hf hg hg')
    (fun f g hf hg => h3 ℓ f g hf hg)
    (ϱ := ϱ) (a := 0) (b := T) (s0 := ϱ) (ϱ' := ϱ) (a' := 0) (b' := T) (s0' := ϱ)
    hϱ hTpos.le (fun y _ => by nlinarith [sq_nonneg y]) hϱ hTpos.le
    (fun y _ => by nlinarith [sq_nonneg y])
  have hint := Muon.Volatility.thm_app_vol_integrated_i cert γstar CSig Fp S hS hC1 ℓ T hT
    (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ)
    (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ)
    (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) rfl rfl ϱ ϱ hϱ hϱ
  simp only [hβ, hμ, hlam] at hint
  have hF : opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) ≤ 1 :=
    zr_opNorm_conj_diag _ S.huOut _ (fun j => by
      by_cases h : j = i <;> simp [Pi.single_apply, h])
  have hG : opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) ≤ 1 :=
    zr_opNorm_conj_diag _ S.hvIn _ (fun j => by simp)
  have hF0 : 0 ≤ opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) := by
    open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm]; exact norm_nonneg _
  have hG0 : 0 ≤ opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) := by
    open scoped Matrix.Norms.L2Operator in
    rw [opNorm_eq_norm]; exact norm_nonneg _
  have hγ0 : 0 ≤ γstar := by
    have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
    linarith
  have hconst : 4 * CSig * (γstar * Real.sqrt γstar) *
      opNorm (S.uOut * Matrix.diagonal (Pi.single i (1 : ℝ)) * S.uOutᵀ) *
      opNorm (S.vIn * Matrix.diagonal (fun _ : Fin N => (1 : ℝ)) * S.vInᵀ) / (Real.pi * T) ≤
      4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T) := by
    have hC0 : 0 ≤ CSig := by linarith
    apply div_le_div_of_nonneg_right _ (by positivity)
    have h0 : 0 ≤ 4 * CSig * (γstar * Real.sqrt γstar) := by positivity
    calc 4 * CSig * (γstar * Real.sqrt γstar) * _ * _ ≤ 4 * CSig * (γstar * Real.sqrt γstar) * 1 * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left hF h0) hG hG0 (by positivity)
      _ = _ := by ring
  have hmain := hint.2.trans hconst
  -- translate to R
  have e : R ℓ (omegaT ϱ T) (omegaT ϱ T) = (B : ℝ) * ((4 / Real.pi ^ 2) *
      ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2))) := by
    have := hH
    simp only [hR] at this
    show R ℓ (fun x => (2 / Real.pi) * ∫ y in (0 : ℝ)..T, iotaF (ϱ + y ^ 2) x)
      (fun x => (2 / Real.pi) * ∫ y in (0 : ℝ)..T, iotaF (ϱ + y ^ 2) x) = _
    rw [hR, this]
    simp only [intervalIntegral.integral_const_mul]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have goal' : |R ℓ (omegaF ϱ) (omegaF ϱ) - R ℓ (omegaT ϱ T) (omegaT ϱ T)| ≤
      4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * T) := by
    rw [e, hR ℓ (omegaF ϱ) (omegaF ϱ)]
    have : (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) -
        (B : ℝ) * ((4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2))) =
        (B : ℝ) * (lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) (omegaF ϱ) (omegaF ϱ) - (4 / Real.pi ^ 2) *
          ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (ϱ + x ^ 2)) (iotaF (ϱ + y ^ 2))) := by ring
    rw [this, abs_mul, abs_of_nonneg hB0]
    calc (B : ℝ) * _ ≤ (B : ℝ) * (4 * CSig * (γstar * Real.sqrt γstar) / (Real.pi * T)) :=
          mul_le_mul_of_nonneg_left hmain hB0
      _ = _ := by ring
  simpa only [hR] using goal'

end ZrSqTrunc


section ZrBCont
open Muon.Volatility (supNorm IsOddBddLip omegaT)

private lemma zr_R_diff (Rl : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hlin1 : ∀ (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      Rl (fun x => f x + c * f' x) g = Rl f g + c * Rl f' g)
    (hlin2 : ∀ (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      Rl f (fun x => g x + c * g' x) = Rl f g + c * Rl f g')
    (hbd : ∀ (f g : ℝ → ℝ), IsOddBddLip f → IsOddBddLip g →
      |Rl f g| ≤ Cb * supNorm f * supNorm g)
    {f g : ℝ → ℝ} (hf : IsOddBddLip f) (hg : IsOddBddLip g) {ε M : ℝ}
    (hε : ∀ x, |f x - g x| ≤ ε) (hMf : ∀ x, |f x| ≤ M) (hMg : ∀ x, |g x| ≤ M) :
    |Rl f f - Rl g g| ≤ Cb * ε * (M + M) := by
  have hd : IsOddBddLip (fun x => f x + (-1) * g x) := zrb_obl_add (-1) hf hg
  have h1 := hlin1 f g f (-1) hf hg hf
  have h2 := hlin2 g f g (-1) hg hf hg
  have sd : supNorm (fun x => f x + (-1) * g x) ≤ ε := zrb_supNorm_le fun x => by
    have := hε x
    rwa [show f x + (-1) * g x = f x - g x by ring]
  have sf : supNorm f ≤ M := zrb_supNorm_le hMf
  have sg : supNorm g ≤ M := zrb_supNorm_le hMg
  have s0 : ∀ h : ℝ → ℝ, 0 ≤ supNorm h := fun h => Real.iSup_nonneg fun _ => abs_nonneg _
  have b1 := hbd _ f hd hf
  have b2 := hbd g _ hg hd
  have e : Rl f f - Rl g g = Rl (fun x => f x + (-1) * g x) f + Rl g (fun x => f x + (-1) * g x) := by
    rw [h1, h2]; ring
  rw [e]
  have c1 : |Rl (fun x => f x + (-1) * g x) f| ≤ Cb * ε * M :=
    b1.trans (mul_le_mul (mul_le_mul_of_nonneg_left sd hCb) sf (s0 f) (by
      have : 0 ≤ supNorm (fun x => f x + (-1) * g x) := s0 _
      nlinarith))
  have c2 : |Rl g (fun x => f x + (-1) * g x)| ≤ Cb * M * ε :=
    b2.trans (mul_le_mul (mul_le_mul_of_nonneg_left sg hCb) sd (s0 _) (by
      have : 0 ≤ supNorm g := s0 _
      nlinarith))
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ Cb * ε * M + Cb * M * ε := add_le_add c1 c2
    _ = _ := by ring

private lemma zr_b_pt {ϱ δ T : ℝ} (hϱ : 0 ≤ ϱ) (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    |((2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x) -
      ((2 / Real.pi) * ∫ y in δ..T, iotaF (0 + y ^ 2) x)| ≤
      (2 / Real.pi) * ((T - δ) * (ϱ / (δ ^ 2 * δ))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hy1 : ∀ y ∈ Icc δ T, δ ^ 2 ≤ ϱ + y ^ 2 := fun y hy => by
    nlinarith [hy.1, sq_nonneg y, mul_self_nonneg (y - δ), hϱ]
  have hy0 : ∀ y ∈ Icc δ T, δ ^ 2 ≤ 0 + y ^ 2 := fun y hy => by
    nlinarith [hy.1]
  have i1 : IntervalIntegrable (fun y => iotaF (ϱ + y ^ 2) x) volume δ T :=
    (zrb_iota_cont hδ2 hy1 x).intervalIntegrable_of_Icc hδT
  have i0 : IntervalIntegrable (fun y => iotaF (0 + y ^ 2) x) volume δ T :=
    (zrb_iota_cont hδ2 hy0 x).intervalIntegrable_of_Icc hδT
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi),
    ← intervalIntegral.integral_sub i1 i0]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := δ) (b := T)
    (f := fun y => iotaF (ϱ + y ^ 2) x - iotaF (0 + y ^ 2) x) (C := ϱ / (δ ^ 2 * δ))
    (fun y hyy => by
      rw [Set.uIoc_of_le hδT] at hyy
      have hyI : y ∈ Icc δ T := ⟨hyy.1.le, hyy.2⟩
      rw [Real.norm_eq_abs]
      have h := zrb_iota_param (x := x) hδ2 (hy1 y hyI) (hy0 y hyI)
      have hs : Real.sqrt (δ ^ 2) = δ := Real.sqrt_sq hδ.le
      rw [hs] at h
      have e : |(ϱ + y ^ 2) - (0 + y ^ 2)| = ϱ := by
        rw [show (ϱ + y ^ 2) - (0 + y ^ 2) = ϱ by ring, abs_of_nonneg hϱ]
      rwa [e] at h)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hδT)] at this
  calc _ ≤ ϱ / (δ ^ 2 * δ) * (T - δ) := this
    _ = _ := by ring

end ZrBCont


section ZrKappa
open Muon.Volatility (supNorm IsOddBddLip omegaT)

private lemma zr_R_diff2 (Rl : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hlin1 : ∀ (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      Rl (fun x => f x + c * f' x) g = Rl f g + c * Rl f' g)
    (hlin2 : ∀ (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      Rl f (fun x => g x + c * g' x) = Rl f g + c * Rl f g')
    (hbd : ∀ (f g : ℝ → ℝ), IsOddBddLip f → IsOddBddLip g →
      |Rl f g| ≤ Cb * supNorm f * supNorm g)
    {f g f' g' : ℝ → ℝ} (hf : IsOddBddLip f) (hg : IsOddBddLip g) (hf' : IsOddBddLip f')
    (hg' : IsOddBddLip g') {ε1 ε2 M1 M2 : ℝ}
    (hε1 : ∀ x, |f x - f' x| ≤ ε1) (hε2 : ∀ x, |g x - g' x| ≤ ε2)
    (hMg : ∀ x, |g x| ≤ M2) (hMf' : ∀ x, |f' x| ≤ M1) :
    |Rl f g - Rl f' g'| ≤ Cb * ε1 * M2 + Cb * M1 * ε2 := by
  have hd1 : IsOddBddLip (fun x => f x + (-1) * f' x) := zrb_obl_add (-1) hf hf'
  have hd2 : IsOddBddLip (fun x => g x + (-1) * g' x) := zrb_obl_add (-1) hg hg'
  have h1 := hlin1 f f' g (-1) hf hf' hg
  have h2 := hlin2 f' g g' (-1) hf' hg hg'
  have s1 : supNorm (fun x => f x + (-1) * f' x) ≤ ε1 := zrb_supNorm_le fun x => by
    have := hε1 x
    rwa [show f x + (-1) * f' x = f x - f' x by ring]
  have s2 : supNorm (fun x => g x + (-1) * g' x) ≤ ε2 := zrb_supNorm_le fun x => by
    have := hε2 x
    rwa [show g x + (-1) * g' x = g x - g' x by ring]
  have sg : supNorm g ≤ M2 := zrb_supNorm_le hMg
  have sf' : supNorm f' ≤ M1 := zrb_supNorm_le hMf'
  have s0 : ∀ h : ℝ → ℝ, 0 ≤ supNorm h := fun h => Real.iSup_nonneg fun _ => abs_nonneg _
  have b1 := hbd _ g hd1 hg
  have b2 := hbd f' _ hf' hd2
  have e : Rl f g - Rl f' g' = Rl (fun x => f x + (-1) * f' x) g +
      Rl f' (fun x => g x + (-1) * g' x) := by rw [h1, h2]; ring
  rw [e]
  have c1 : |Rl (fun x => f x + (-1) * f' x) g| ≤ Cb * ε1 * M2 :=
    b1.trans (mul_le_mul (mul_le_mul_of_nonneg_left s1 hCb) sg (s0 g) (by
      have := s0 (fun x => f x + (-1) * f' x)
      nlinarith))
  have c2 : |Rl f' (fun x => g x + (-1) * g' x)| ≤ Cb * M1 * ε2 :=
    b2.trans (mul_le_mul (mul_le_mul_of_nonneg_left sf' hCb) s2 (s0 _) (by
      have := s0 f'
      nlinarith))
  exact (abs_add_le _ _).trans (add_le_add c1 c2)

private lemma zr_kappa_cont (Rl : (ℝ → ℝ) → (ℝ → ℝ) → ℝ) (Cb : ℝ) (hCb : 0 ≤ Cb)
    (hlin1 : ∀ (f f' g : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip f' → IsOddBddLip g →
      Rl (fun x => f x + c * f' x) g = Rl f g + c * Rl f' g)
    (hlin2 : ∀ (f g g' : ℝ → ℝ) (c : ℝ), IsOddBddLip f → IsOddBddLip g → IsOddBddLip g' →
      Rl f (fun x => g x + c * g' x) = Rl f g + c * Rl f g')
    (hbd : ∀ (f g : ℝ → ℝ), IsOddBddLip f → IsOddBddLip g →
      |Rl f g| ≤ Cb * supNorm f * supNorm g) :
    ContinuousOn (fun p : ℝ × ℝ => Rl (iotaF (p.1 ^ 2)) (iotaF (p.2 ^ 2))) (Ioi 0 ×ˢ Ioi 0) := by
  intro p0 hp0
  have hx0 : 0 < p0.1 := hp0.1
  have hy0 : 0 < p0.2 := hp0.2
  set s0 : ℝ := min (p0.1 ^ 2) (p0.2 ^ 2) / 2 with hs0
  have hs0pos : 0 < s0 := by positivity
  set c1 : ℝ := 1 / (s0 * Real.sqrt s0) with hc1
  set Mb : ℝ := 1 / (2 * Real.sqrt s0) with hMb
  have hc10 : 0 ≤ c1 := by positivity
  have hMb0 : 0 ≤ Mb := by positivity
  rw [ContinuousWithinAt]
  refine tendsto_iff_dist_tendsto_zero.mpr ?_
  have hlim : Tendsto (fun p : ℝ × ℝ => Cb * (c1 * |p.1 ^ 2 - p0.1 ^ 2|) * Mb +
      Cb * Mb * (c1 * |p.2 ^ 2 - p0.2 ^ 2|)) (𝓝[Ioi 0 ×ˢ Ioi 0] p0) (𝓝 0) := by
    have hc : Continuous (fun p : ℝ × ℝ => Cb * (c1 * |p.1 ^ 2 - p0.1 ^ 2|) * Mb +
        Cb * Mb * (c1 * |p.2 ^ 2 - p0.2 ^ 2|)) := by fun_prop
    have := hc.tendsto p0
    simp only [sub_self, abs_zero, mul_zero, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  have hev : ∀ᶠ p in 𝓝[Ioi 0 ×ˢ Ioi 0] p0, s0 ≤ p.1 ^ 2 ∧ s0 ≤ p.2 ^ 2 := by
    have h1 : Tendsto (fun p : ℝ × ℝ => p.1 ^ 2) (𝓝 p0) (𝓝 (p0.1 ^ 2)) :=
      (continuous_fst.pow 2).tendsto p0
    have h2 : Tendsto (fun p : ℝ × ℝ => p.2 ^ 2) (𝓝 p0) (𝓝 (p0.2 ^ 2)) :=
      (continuous_snd.pow 2).tendsto p0
    have a1 : ∀ᶠ p in 𝓝 p0, s0 < p.1 ^ 2 := h1.eventually (lt_mem_nhds (by
      have := min_le_left (p0.1 ^ 2) (p0.2 ^ 2)
      have : 0 < min (p0.1 ^ 2) (p0.2 ^ 2) := by positivity
      simp only [hs0]; linarith [min_le_left (p0.1 ^ 2) (p0.2 ^ 2)]))
    have a2 : ∀ᶠ p in 𝓝 p0, s0 < p.2 ^ 2 := h2.eventually (lt_mem_nhds (by
      have : 0 < min (p0.1 ^ 2) (p0.2 ^ 2) := by positivity
      simp only [hs0]; linarith [min_le_right (p0.1 ^ 2) (p0.2 ^ 2)]))
    exact nhdsWithin_le_nhds ((a1.and a2).mono fun p hp => ⟨hp.1.le, hp.2.le⟩)
  filter_upwards [hev] with p hp
  rw [Real.dist_eq]
  have hsp1 : 0 < p.1 ^ 2 := hs0pos.trans_le hp.1
  have hsp2 : 0 < p.2 ^ 2 := hs0pos.trans_le hp.2
  have hu1 : 0 < p0.1 ^ 2 := by positivity
  have hu2 : 0 < p0.2 ^ 2 := by positivity
  have hmin1 : s0 ≤ p0.1 ^ 2 := by simp only [hs0]; linarith [min_le_left (p0.1 ^ 2) (p0.2 ^ 2), (by positivity : 0 < min (p0.1 ^ 2) (p0.2 ^ 2))]
  have hmin2 : s0 ≤ p0.2 ^ 2 := by simp only [hs0]; linarith [min_le_right (p0.1 ^ 2) (p0.2 ^ 2), (by positivity : 0 < min (p0.1 ^ 2) (p0.2 ^ 2))]
  have := zr_R_diff2 Rl Cb hCb hlin1 hlin2 hbd (zrb_iota_obl hsp1) (zrb_iota_obl hsp2)
    (zrb_iota_obl hu1) (zrb_iota_obl hu2)
    (ε1 := c1 * |p.1 ^ 2 - p0.1 ^ 2|) (ε2 := c1 * |p.2 ^ 2 - p0.2 ^ 2|) (M1 := Mb) (M2 := Mb)
    (fun x => by
      exact (zrb_iota_param (x := x) hs0pos hp.1 hmin1).trans (le_of_eq (by rw [hc1]; ring)))
    (fun x => by
      exact (zrb_iota_param (x := x) hs0pos hp.2 hmin2).trans (le_of_eq (by rw [hc1]; ring)))
    (fun x => zrb_iota_abs hs0pos hp.2 (x := x))
    (fun x => zrb_iota_abs hs0pos hmin1 (x := x))
  convert this using 1

end ZrKappa


private lemma zr_sqint2 (f : ℝ × ℝ → ℝ) (L : ℝ)
    (hpos : ∀ p ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), 0 ≤ f p)
    (hfi : ∀ δ T : ℝ, 0 < δ → δ ≤ T → IntegrableOn f (Icc δ T ×ˢ Icc δ T))
    (hlim : Tendsto (fun n : ℕ => (4 / Real.pi ^ 2) *
      ∫ x in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1), ∫ y in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1), f (x, y))
      atTop (𝓝 L)) :
    IntegrableOn f (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
      (4 / Real.pi ^ 2) * (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y)) = L := by
  let R : Set (ℝ × ℝ) := Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)
  have hn0 : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hn1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n => by
    have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc 1 / ((n : ℝ) + 1) ≤ 1 := by rw [div_le_one (by positivity)]; exact this
      _ ≤ _ := this
  let φ : ℕ → Set (ℝ × ℝ) := fun n =>
    Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1) ×ˢ Ioc (1 / ((n : ℝ) + 1)) ((n : ℝ) + 1)
  have hsub (n : ℕ) : φ n ⊆ R := fun p hp => ⟨(hn0 n).trans hp.1.1, (hn0 n).trans hp.2.1⟩
  have hm (n : ℕ) : MeasurableSet (φ n) := measurableSet_Ioc.prod measurableSet_Ioc
  have hcov : AECover (volume.restrict R) atTop φ := by
    refine ⟨?_, hm⟩
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
    obtain ⟨N, hN⟩ := exists_nat_ge (max (max p.1 p.2) (max (1 / p.1) (1 / p.2)))
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnN : (N : ℝ) ≤ n := Nat.cast_le.mpr hn
    have hb : max (max p.1 p.2) (max (1 / p.1) (1 / p.2)) < (n : ℝ) + 1 := by linarith
    have hp1 : 0 < p.1 := hp.1
    have hp2 : 0 < p.2 := hp.2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · have h1 : 1 / p.1 < (n : ℝ) + 1 := lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hb
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hp1).1 h1
      nlinarith
    · exact ((le_max_left _ _).trans (le_max_left _ _)).trans hb.le
    · have h1 : 1 / p.2 < (n : ℝ) + 1 := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hb
      rw [div_lt_iff₀ (by positivity)]
      have := (div_lt_iff₀ hp2).1 h1
      nlinarith
    · exact ((le_max_right _ _).trans (le_max_left _ _)).trans hb.le
  have hlocal (n : ℕ) : IntegrableOn f (φ n) :=
    (hfi _ _ (hn0 n) (hn1 n)).mono_set (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hrestrict (n : ℕ) : (volume.restrict R).restrict (φ n) = volume.restrict (φ n) := by
    rw [Measure.restrict_restrict (hm n), inter_eq_left.mpr (hsub n)]
  have heq (n : ℕ) : (∫ p in φ n, f p ∂(volume.restrict R)) =
      ∫ x in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1), ∫ y in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1), f (x, y) := by
    rw [hrestrict]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    rw [setIntegral_prod f (by simpa only [← Measure.volume_eq_prod] using hlocal n)]
    simp only [intervalIntegral.integral_of_le (hn1 n)]
  have hc : (4 / Real.pi ^ 2 : ℝ) ≠ 0 := by positivity
  have hlim' : Tendsto (fun n : ℕ => ∫ p in φ n, f p ∂(volume.restrict R)) atTop
      (𝓝 (L / (4 / Real.pi ^ 2))) := by
    convert hlim.div_const (4 / Real.pi ^ 2) using 1
    ext n
    rw [heq]
    exact (mul_div_cancel_left₀ _ hc).symm
  have hint : Integrable f (volume.restrict R) :=
    hcov.integrable_of_integral_tendsto_of_nonneg_ae _
      (fun n => by simpa only [IntegrableOn, hrestrict] using hlocal n)
      ((ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)).2 (Eventually.of_forall hpos))
      hlim'
  refine ⟨hint, ?_⟩
  have hval := tendsto_nhds_unique (hcov.integral_tendsto_of_countably_generated hint) hlim'
  have hprod : (∫ p in R, f p) = ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), f (x, y) := by
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    exact setIntegral_prod f (by simpa only [IntegrableOn, ← Measure.volume_eq_prod, R] using hint)
  rw [← hprod, hval, mul_div_cancel₀ _ hc]


section ZrFinal
open Muon.Volatility (supNorm IsOddBddLip omegaT)

private lemma zr_b_bound {ϱ δ T : ℝ} (hϱ : 0 ≤ ϱ) (hδ : 0 < δ) (hδT : δ ≤ T) (x : ℝ) :
    |(2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x| ≤ (2 / Real.pi) * ((T - δ) * (1 / (2 * δ))) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hδ2 : 0 < δ ^ 2 := by positivity
  rw [abs_mul, abs_of_pos (by positivity : 0 < 2 / Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := δ) (b := T)
    (f := fun y => iotaF (ϱ + y ^ 2) x) (C := 1 / (2 * δ)) (fun y hyy => by
      rw [Set.uIoc_of_le hδT] at hyy
      rw [Real.norm_eq_abs]
      have h := zrb_iota_abs (s0 := δ ^ 2) (s := ϱ + y ^ 2) (x := x) hδ2 (by nlinarith [hyy.1])
      rwa [Real.sqrt_sq hδ.le] at h)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.2 hδT)] at this
  calc _ ≤ 1 / (2 * δ) * (T - δ) := this
    _ = _ := by ring


private lemma zr_hmain (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) {δ T : ℝ} (hδ : 0 < δ) (hT : 1 ≤ T) (hδT : δ ≤ T) :
    |cbarZero cert γstar CSig β B μ i ℓ - (4 / Real.pi ^ 2) *
        ∫ x in δ..T, ∫ y in δ..T, (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2))| ≤
      4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * T) +
        2 * Real.sqrt (8 * ((B : ℝ) * γstar) *
          (1 - lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i (δ ^ 2) (δ ^ 2))) := by
  classical
  obtain ⟨R, hR⟩ : ∃ R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ, ∀ ℓ f g, R ℓ f g = (B : ℝ) *
      lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) f g := ⟨fun ℓ f g => _, fun _ _ _ => rfl⟩
  obtain ⟨hcs, hdom, hnnR, h1, h2, h3⟩ := zr_Rprops cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i R hR
  have hγ0 : 0 ≤ γstar := by
    have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
    linarith
  have hCb : 0 ≤ (B : ℝ) * γstar := by positivity
  have hpi : 0 < Real.pi := Real.pi_pos
  have hT0 : 0 < T := by linarith
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hrow : ∀ ℓ ϱ, lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      R ℓ (omegaF ϱ) (omegaF ϱ) := fun ℓ ϱ => (hR ℓ _ _).symm
  set E : ℝ := 4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * T) +
    2 * Real.sqrt (8 * ((B : ℝ) * γstar) * (1 - R 0 (omegaF (δ ^ 2)) (omegaF (δ ^ 2)))) with hE
  -- positive-ridge comparison
  have hpos_ridge : ∀ ϱ : ℝ, 0 < ϱ →
      |R ℓ (omegaF ϱ) (omegaF ϱ) - R ℓ (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)
        (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)| ≤ E := by
    intro ϱ hϱ
    have a1 := zr_sq_trunc cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i ℓ hϱ hT
    have a2 := zr_main_est R ((B : ℝ) * γstar) hCb hcs hdom hnnR h1 h2 h3 ℓ hϱ hδ hδT
    simp only [← hR] at a1
    calc _ = |(R ℓ (omegaF ϱ) (omegaF ϱ) - R ℓ (omegaT ϱ T) (omegaT ϱ T)) +
          (R ℓ (omegaT ϱ T) (omegaT ϱ T) - R ℓ (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)
        (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x))| := by ring_nf
      _ ≤ _ := abs_add_le _ _
      _ ≤ _ := add_le_add a1 a2
  -- the limit ϱ → 0
  set b0 : ℝ → ℝ := fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (0 + y ^ 2) x with hb0
  have hs0 : ∀ y ∈ Icc δ T, δ ^ 2 ≤ 0 + y ^ 2 := fun y hy => by nlinarith [hy.1]
  have hb0obl : IsOddBddLip b0 := zrb_F_obl hδ2 hδT hs0
  have hbtend : Tendsto (fun ϱ : ℝ => R ℓ (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)
        (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x)) (𝓝[>] (0 : ℝ)) (𝓝 (R ℓ b0 b0)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hbound : Tendsto (fun ϱ : ℝ => (B : ℝ) * γstar * ((2 / Real.pi) * ((T - δ) * (ϱ / (δ ^ 2 * δ)))) *
        ((2 / Real.pi) * ((T - δ) * (1 / (2 * δ))) + (2 / Real.pi) * ((T - δ) * (1 / (2 * δ)))))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : Continuous (fun ϱ : ℝ => (B : ℝ) * γstar * ((2 / Real.pi) * ((T - δ) * (ϱ / (δ ^ 2 * δ)))) *
        ((2 / Real.pi) * ((T - δ) * (1 / (2 * δ))) + (2 / Real.pi) * ((T - δ) * (1 / (2 * δ))))) := by
        fun_prop
      have := hc.tendsto 0
      simp only [zero_div, mul_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hbound
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    have hϱ' : (0 : ℝ) < ϱ := hϱ
    rw [Real.dist_eq]
    have hobl : IsOddBddLip (fun x => (2 / Real.pi) * ∫ y in δ..T, iotaF (ϱ + y ^ 2) x) :=
      zrb_F_obl hδ2 hδT (fun y hy => by nlinarith [hy.1])
    exact zr_R_diff (R ℓ) ((B : ℝ) * γstar) hCb (fun f f' g c hf hf' hg => h1 ℓ f f' g c hf hf' hg)
      (fun f g g' c hf hg hg' => h2 ℓ f g g' c hf hg hg') (fun f g hf hg => h3 ℓ f g hf hg)
      hobl hb0obl (fun x => zr_b_pt hϱ'.le hδ hδT x) (fun x => zr_b_bound hϱ'.le hδ hδT x)
      (fun x => zr_b_bound (le_refl (0 : ℝ)) hδ hδT x)
  have hz0 : 0 < plZ1 β B μ :=
    (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ hB hN hpos).1.mapsTo (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  obtain ⟨-, hlimC, -, -, -⟩ := prop_app_pl_vol_zero_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  have hC : Tendsto (fun ϱ : ℝ => R ℓ (omegaF ϱ) (omegaF ϱ)) (𝓝[>] (0 : ℝ))
      (𝓝 (cbarZero cert γstar CSig β B μ i ℓ)) := by
    simpa only [hrow] using hlimC ℓ
  have hu := (hC.sub hbtend).abs
  have hle : |cbarZero cert γstar CSig β B μ i ℓ - R ℓ b0 b0| ≤ E :=
    le_of_tendsto hu (by filter_upwards [self_mem_nhdsWithin] with ϱ hϱ; exact hpos_ridge ϱ hϱ)
  have hH := zrb_H2 (R ℓ) ((B : ℝ) * γstar) hCb (fun f f' g c hf hf' hg => h1 ℓ f f' g c hf hf' hg)
    (fun f g g' c hf hg hg' => h2 ℓ f g g' c hf hg hg') (fun f g hf hg => h3 ℓ f g hf hg)
    (ϱ := 0) (a := δ) (b := T) (s0 := δ ^ 2) (ϱ' := 0) (a' := δ) (b' := T) (s0' := δ ^ 2)
    hδ2 hδT hs0 hδ2 hδT hs0
  have hid : R ℓ b0 b0 = (4 / Real.pi ^ 2) *
      ∫ x in δ..T, ∫ y in δ..T, (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2)) := by
    rw [hb0, hH]
    simp only [zero_add, hR, intervalIntegral.integral_const_mul]
    have hpi' : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [← hid, hrow 0 (δ ^ 2)]
  exact hle

end ZrFinal


section ZrPw
open Muon.DetEquiv

private lemma zrp_delta (γ m1 m2 Q1 Q2 L1 L2 b e T : ℝ) (hγ : 0 < γ)
    (hm1 : 0 < m1) (hm1γ : m1 < γ) (hm2 : 0 < m2) (hm2γ : m2 < γ)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2) (hL1 : 0 < L1) (hL2 : 0 < L2) :
    let s1 := (γ - m1) * m1 / (Q1 * L1)
    let s2 := (γ - m2) * m2 / (Q2 * L2)
    (1 - s1 * s2 * (T / ((s1 * L1) * (s2 * L2))) * ((γ - m1) / s1) * ((γ - m2) / s2) * e) *
      (1 - s1 * s2 * (γ / ((s1 + s1 * m1 / (γ - m1)) * (s2 + s2 * m2 / (γ - m2)))) *
        (m1 / (s1 * L1)) * (m2 / (s2 * L2)) * e) -
      s1 * s2 * (T / ((s1 * L1) * (s2 * L2))) *
        (γ / ((s1 + s1 * m1 / (γ - m1)) * (s2 + s2 * m2 / (γ - m2)))) * b ^ 2 =
    (1 - T * (Q1 * Q2 * e) / (m1 * m2)) * (1 - (Q1 * Q2 * e) / γ) -
      T * (Real.sqrt (Q1 * Q2) * b) ^ 2 / (γ * m1 * m2) := by
  intro s1 s2
  have hg1 : 0 < γ - m1 := sub_pos.2 hm1γ
  have hg2 : 0 < γ - m2 := sub_pos.2 hm2γ
  have hs1 : 0 < s1 := by positivity
  have hs2 : 0 < s2 := by positivity
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  have e1 : s1 + s1 * m1 / (γ - m1) = s1 * γ / (γ - m1) := by field_simp; ring
  have e2 : s2 + s2 * m2 / (γ - m2) = s2 * γ / (γ - m2) := by field_simp; ring
  rw [e1, e2]
  simp only [s1, s2]
  field_simp


private lemma zrp_num (γ μ m1 m2 Q1 Q2 L1 L2 th1 th2 b : ℝ) (hγ : 0 < γ) (hμ : 0 < μ)
    (hm1 : 0 < m1) (hm1γ : m1 < γ) (hm2 : 0 < m2) (hm2γ : m2 < γ)
    (hQ1 : 0 < Q1) (hQ2 : 0 < Q2) (hL1 : 0 < L1) (hL2 : 0 < L2)
    (hb : 0 ≤ b) (h1 : 0 ≤ th1) (h2 : 0 ≤ th2) :
    let s1 := (γ - m1) * m1 / (Q1 * L1)
    let s2 := (γ - m2) * m2 / (Q2 * L2)
    (Real.sqrt (μ * L1) / (Real.sqrt m1 * (1 + μ * L1)) * Real.sqrt (1 - m1 / γ) * th1) *
      (Real.sqrt (μ * L2) / (Real.sqrt m2 * (1 + μ * L2)) * Real.sqrt (1 - m2 / γ) * th2) *
      (Real.sqrt (Q1 * Q2) * b) =
    γ * s1 * s2 * μ * b / ((s1 + s1 * L1 * μ) * (s2 + s2 * L2 * μ) * (s1 + s1 * m1 / (γ - m1)) *
      (s2 + s2 * m2 / (γ - m2))) * (Real.sqrt (s1 * s2) * th1 * th2) := by
  intro s1 s2
  have hg1 : 0 < γ - m1 := sub_pos.2 hm1γ
  have hg2 : 0 < γ - m2 := sub_pos.2 hm2γ
  have hs1 : 0 < s1 := by positivity
  have hs2 : 0 < s2 := by positivity
  have hd1 : 0 ≤ 1 - m1 / γ := by
    rw [sub_nonneg, div_le_one hγ]; exact hm1γ.le
  have hd2 : 0 ≤ 1 - m2 / γ := by
    rw [sub_nonneg, div_le_one hγ]; exact hm2γ.le
  have e1 : s1 + s1 * m1 / (γ - m1) = s1 * γ / (γ - m1) := by simp only [s1]; field_simp; ring
  have e2 : s2 + s2 * m2 / (γ - m2) = s2 * γ / (γ - m2) := by simp only [s2]; field_simp; ring
  rw [e1, e2]
  have hL : 0 ≤ Real.sqrt (μ * L1) / (Real.sqrt m1 * (1 + μ * L1)) * Real.sqrt (1 - m1 / γ) * th1 *
      (Real.sqrt (μ * L2) / (Real.sqrt m2 * (1 + μ * L2)) * Real.sqrt (1 - m2 / γ) * th2) *
      (Real.sqrt (Q1 * Q2) * b) := by positivity
  have hR : 0 ≤ γ * s1 * s2 * μ * b / ((s1 + s1 * L1 * μ) * (s2 + s2 * L2 * μ) * (s1 * γ / (γ - m1)) *
      (s2 * γ / (γ - m2))) * (Real.sqrt (s1 * s2) * th1 * th2) := by positivity
  rw [← pow_left_inj₀ hL hR (two_ne_zero)]
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt (by positivity : 0 ≤ μ * L1), Real.sq_sqrt (by positivity : 0 ≤ μ * L2),
    Real.sq_sqrt hm1.le, Real.sq_sqrt hm2.le, Real.sq_sqrt hd1, Real.sq_sqrt hd2,
    Real.sq_sqrt (by positivity : 0 ≤ Q1 * Q2), Real.sq_sqrt (by positivity : 0 ≤ s1 * s2)]
  simp only [s1, s2]
  field_simp


private lemma zrp_assoc (X P Y D : ℝ) : X / P * Y / D = X / (P * D) * Y := by ring

private lemma zrp_DL (β Q1 Q2 : ℝ) (n : ℕ) :
    DLag β Q1 Q2 (n : ℤ) = Real.sqrt (Q1 * Q2) * bLag β Q1 Q2 n := by
  unfold DLag DLagNat bLag
  rw [if_pos (Int.natCast_nonneg n), Int.toNat_natCast, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  ring

private lemma zrp_ML (β Q1 Q2 : ℝ) (n : ℕ) :
    MLag β Q1 Q2 (n : ℤ) = Q1 * Q2 * eLag β Q1 Q2 n := by
  unfold MLag MLagNat eLag
  rw [if_pos (Int.natCast_nonneg n), Int.toNat_natCast, ← tsum_mul_left]
  refine tsum_congr fun j => ?_
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  simp only
  ring

private lemma zrp_b_nonneg (β Q1 Q2 : ℝ) (hβ : 0 ≤ β) (hQ1 : 0 ≤ Q1) (hQ2 : 0 ≤ Q2) (n : ℕ) :
    0 ≤ bLag β Q1 Q2 n := by
  unfold bLag
  apply tsum_nonneg
  intro j
  apply integral_nonneg
  intro g
  positivity

end ZrPw


section ZrPw2
open Muon.DetEquiv

private lemma zr_pw {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) {Cs : ℝ}
    (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (n : ℕ) (i : Fin N) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    lagIntegrand β B μ i (n : ℤ) m₁ m₂ =
      respRHS β B μ ν ν' n i (sN β B μ m₁) (sN β B μ m₂) *
        (Real.sqrt (sN β B μ m₁ * sN β B μ m₂) * thetaN β B μ m₁ * thetaN β B μ m₂) := by
  classical
  have hγ : 0 < gammaOf N B := by
    unfold gammaOf; exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hbij := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hLam := (def_app_pl_participation_bij μ hB hN hpos).2.1
  have key : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < sN β B μ m ∧ 0 < partLam B μ m ∧ 0 < Qm β m ∧
      0 < thetaN β B μ m ∧
      (sN β B μ m * (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).1 *
          (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).2.1 = Qm β m) ∧
      (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).2.2.1 = sN β B μ m * partLam B μ m ∧
      (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).2.2.2 =
        sN β B μ m * m / (gammaOf N B - m) ∧
      (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).1 = m / (sN β B μ m * partLam B μ m) ∧
      (branchSol (Fw (emaW β)) ν ν' (sN β B μ m)).2.1 = (gammaOf N B - m) / sN β B μ m := by
    intro m hm
    have hs : 0 < sN β B μ m := hbij.2.2.1.mapsTo hm
    have hL : 0 < partLam B μ m := hLam.mapsTo hm
    have hQ : 0 < Qm β m := by
      by_contra hQ
      push Not at hQ
      have : sN β B μ m ≤ 0 := by
        unfold sN
        exact div_nonpos_of_nonneg_of_nonpos
          (mul_pos (sub_pos.2 hm.2) hm.1).le (mul_nonpos_of_nonpos_of_nonneg hQ hL.le)
      linarith
    obtain ⟨b1, b2, b3, b4, b5, -⟩ := prop_app_pl_branch_ii μ hβ0 hβ1 hB hN hanti hpos hν hν' hμCs h1Cs
      (s := sN β B μ m) hs hm rfl
    exact ⟨hs, hL, hQ, (hbij.2.2.2 m hm).2, b1, b2, b3, b4, b5⟩
  obtain ⟨hs1, hL1, hQ1, hth1, q1, t1, u1, σ1, σt1⟩ := key m₁ hm₁
  obtain ⟨hs2, hL2, hQ2, hth2, q2, t2, u2, σ2, σt2⟩ := key m₂ hm₂
  have hU : respU β B μ ν ν' (sN β B μ m₁) (sN β B μ m₂) =
      TNpart B μ m₁ m₂ / ((sN β B μ m₁ * partLam B μ m₁) * (sN β B μ m₂ * partLam B μ m₂)) := by
    unfold respU TNpart
    rw [t1, t2, mul_div_assoc, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold partF
    have hμj := hpos j
    have h1 : 0 < 1 + partLam B μ m₁ * μ j := by nlinarith [mul_pos hL1 hμj]
    have h2 : 0 < 1 + partLam B μ m₂ * μ j := by nlinarith [mul_pos hL2 hμj]
    field_simp
  have hb := zrp_b_nonneg β (Qm β m₁) (Qm β m₂) hβ0.le hQ1.le hQ2.le n
  have hq1 : respQ β ν ν' (sN β B μ m₁) = Qm β m₁ := q1
  have hq2 : respQ β ν ν' (sN β B μ m₂) = Qm β m₂ := q2
  unfold respRHS respDelta respV
  rw [hU, hq1, hq2]
  unfold lagIntegrand lagNumer Wpart deltaN
  rw [zrp_DL, zrp_ML]
  simp only [t1, t2, u1, u2, σ1, σ2, σt1, σt2]
  have hmm1 := hm₁
  have hmm2 := hm₂
  have hD := zrp_delta (gammaOf N B) m₁ m₂ (Qm β m₁) (Qm β m₂) (partLam B μ m₁) (partLam B μ m₂)
    (bLag β (Qm β m₁) (Qm β m₂) n) (eLag β (Qm β m₁) (Qm β m₂) n) (TNpart B μ m₁ m₂) hγ hm₁.1 hm₁.2
    hm₂.1 hm₂.2 hQ1 hQ2 hL1 hL2
  have hN1 := zrp_num (gammaOf N B) (μ i) m₁ m₂ (Qm β m₁) (Qm β m₂) (partLam B μ m₁) (partLam B μ m₂)
    (thetaN β B μ m₁) (thetaN β B μ m₂) (bLag β (Qm β m₁) (Qm β m₂) n) hγ (hpos i) hm₁.1 hm₁.2
    hm₂.1 hm₂.2 hQ1 hQ2 hL1 hL2 hb hth1.le hth2.le
  simp only [] at hD hN1
  unfold sN
  rw [hN1, ← hD]
  exact zrp_assoc _ _ _ _

end ZrPw2


section ZrCov

private lemma zr_det_prod (a b : ℝ) :
    ((ContinuousLinearMap.toSpanSingleton ℝ a).prodMap (ContinuousLinearMap.toSpanSingleton ℝ b)).det
      = a * b := by
  rw [ContinuousLinearMap.det]
  have : (((ContinuousLinearMap.toSpanSingleton ℝ a).prodMap (ContinuousLinearMap.toSpanSingleton ℝ b) :
      ℝ × ℝ →L[ℝ] ℝ × ℝ) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ a : ℝ →L[ℝ] ℝ).toLinearMap.prodMap
        (ContinuousLinearMap.toSpanSingleton ℝ b : ℝ →L[ℝ] ℝ).toLinearMap := rfl
  rw [this, LinearMap.det_prodMap]
  simp

private lemma zr_cov_data {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) :
    (∀ m ∈ Ioo 0 (gammaOf N B), HasDerivAt (fun m => Real.sqrt (sN β B μ m))
      (-(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2)) m) ∧
    InjOn (fun m => Real.sqrt (sN β B μ m)) (Ioo 0 (gammaOf N B)) ∧
    (fun m => Real.sqrt (sN β B μ m)) '' Ioo 0 (gammaOf N B) = Ioi 0 ∧
    (∀ m ∈ Ioo 0 (gammaOf N B), |-(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2)| =
      thetaN β B μ m * Real.sqrt (sN β B μ m) / 2) := by
  have hbij := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hcd := hbij.1
  have hanti' := hbij.2.1
  have hbij' := hbij.2.2.1
  have hderiv : ∀ m ∈ Ioo 0 (gammaOf N B), HasDerivAt (fun m => Real.sqrt (sN β B μ m))
      (-(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2)) m := by
    intro m hm
    have hs : 0 < sN β B μ m := hbij'.mapsTo hm
    have hd : DifferentiableAt ℝ (sN β B μ) m :=
      (hcd.differentiableOn (by simp)).differentiableAt (Ioo_mem_nhds hm.1 hm.2)
    have h1 := (hbij.2.2.2 m hm).1
    have hder : deriv (sN β B μ) m = -(thetaN β B μ m * sN β B μ m) := by
      have : deriv (sN β B μ) m / sN β B μ m = -thetaN β B μ m := by linarith
      rw [div_eq_iff hs.ne'] at this
      linarith
    have := hd.hasDerivAt.sqrt hs.ne'
    rw [hder] at this
    have e : -(thetaN β B μ m * sN β B μ m) / (2 * Real.sqrt (sN β B μ m)) =
        -(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2) := by
      have hr : 0 < Real.sqrt (sN β B μ m) := Real.sqrt_pos.mpr hs
      have hr2 : Real.sqrt (sN β B μ m) ^ 2 = sN β B μ m := Real.sq_sqrt hs.le
      field_simp
      linear_combination thetaN β B μ m * hr2
    rw [e] at this
    exact this
  have hinj : InjOn (fun m => Real.sqrt (sN β B μ m)) (Ioo 0 (gammaOf N B)) := by
    intro a ha b hb hab
    have h1 : sN β B μ a = sN β B μ b := by
      have := congrArg (fun x => x ^ 2) hab
      simp only at this
      rwa [Real.sq_sqrt (hbij'.mapsTo ha).le, Real.sq_sqrt (hbij'.mapsTo hb).le] at this
    exact hbij'.injOn ha hb h1
  have himg : (fun m => Real.sqrt (sN β B μ m)) '' Ioo 0 (gammaOf N B) = Ioi 0 := by
    ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact Real.sqrt_pos.mpr (hbij'.mapsTo hm)
    · intro hy
      have h0 : 0 < y := hy
      obtain ⟨m, hm, hmy⟩ := hbij'.surjOn (show y ^ 2 ∈ Ioi (0 : ℝ) from pow_pos h0 2)
      exact ⟨m, hm, by show Real.sqrt (sN β B μ m) = y; rw [hmy]; exact Real.sqrt_sq h0.le⟩
  have habs : ∀ m ∈ Ioo 0 (gammaOf N B), |-(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2)| =
      thetaN β B μ m * Real.sqrt (sN β B μ m) / 2 := by
    intro m hm
    have hs : 0 < sN β B μ m := hbij'.mapsTo hm
    have hth := (hbij.2.2.2 m hm).2
    rw [abs_neg, abs_of_pos (by have := Real.sqrt_pos.mpr hs; positivity)]
  exact ⟨hderiv, hinj, himg, habs⟩

private lemma zr_cov {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i) :
    (∀ g : ℝ × ℝ → ℝ, ∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), g p =
      ∫ m in Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B),
        (thetaN β B μ m.1 * Real.sqrt (sN β B μ m.1) / 2) *
          (thetaN β B μ m.2 * Real.sqrt (sN β B μ m.2) / 2) *
          g (Real.sqrt (sN β B μ m.1), Real.sqrt (sN β B μ m.2))) ∧
    (∀ g : ℝ × ℝ → ℝ, IntegrableOn g (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ↔
      IntegrableOn (fun m : ℝ × ℝ => (thetaN β B μ m.1 * Real.sqrt (sN β B μ m.1) / 2) *
          (thetaN β B μ m.2 * Real.sqrt (sN β B μ m.2) / 2) *
          g (Real.sqrt (sN β B μ m.1), Real.sqrt (sN β B μ m.2)))
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B))) := by
  obtain ⟨hderiv, hinj, himg, habs⟩ := zr_cov_data μ hβ0 hβ1 hB hN hanti hpos
  set s := Ioo 0 (gammaOf N B) with hs
  set xf : ℝ → ℝ := fun m => Real.sqrt (sN β B μ m) with hxf
  set d : ℝ → ℝ := fun m => -(thetaN β B μ m * Real.sqrt (sN β B μ m) / 2) with hd
  let Ψ : ℝ × ℝ → ℝ × ℝ := fun m => (xf m.1, xf m.2)
  let Ψ' : ℝ × ℝ → (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fun m =>
    (ContinuousLinearMap.toSpanSingleton ℝ (d m.1)).prodMap (ContinuousLinearMap.toSpanSingleton ℝ (d m.2))
  have hΨ' : ∀ m ∈ s ×ˢ s, HasFDerivWithinAt Ψ (Ψ' m) (s ×ˢ s) m := by
    intro m hm
    exact (((hderiv m.1 hm.1).hasFDerivAt).prodMap m ((hderiv m.2 hm.2).hasFDerivAt)).hasFDerivWithinAt
  have hΨinj : InjOn Ψ (s ×ˢ s) := by
    intro a ha b hb hab
    have h1 := congrArg Prod.fst hab
    have h2 := congrArg Prod.snd hab
    exact Prod.ext (hinj ha.1 hb.1 h1) (hinj ha.2 hb.2 h2)
  have hΨimg : Ψ '' (s ×ˢ s) = Ioi 0 ×ˢ Ioi 0 := by
    rw [← himg]
    exact Set.prod_image_image_eq.symm
  have hdet : ∀ m ∈ s ×ˢ s, |(Ψ' m).det| = (thetaN β B μ m.1 * Real.sqrt (sN β B μ m.1) / 2) *
          (thetaN β B μ m.2 * Real.sqrt (sN β B μ m.2) / 2) := by
    intro m hm
    have : (Ψ' m).det = d m.1 * d m.2 := zr_det_prod _ _
    rw [this, abs_mul, hd]
    simp only
    rw [habs m.1 hm.1, habs m.2 hm.2]
  refine ⟨fun g => ?_, fun g => ?_⟩
  · have := integral_image_eq_integral_abs_det_fderiv_smul volume (measurableSet_Ioo.prod measurableSet_Ioo) hΨ' hΨinj g
    rw [hΨimg] at this
    rw [this]
    refine setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo) fun m hm => ?_
    simp only [smul_eq_mul]
    rw [hdet m hm]
  · have := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume (measurableSet_Ioo.prod measurableSet_Ioo) hΨ' hΨinj g
    rw [hΨimg] at this
    rw [this]
    refine integrableOn_congr_fun (fun m hm => ?_) (measurableSet_Ioo.prod measurableSet_Ioo)
    simp only [smul_eq_mul]
    rw [hdet m hm]

end ZrCov

private lemma zr_vol_zero_iii_a_basic (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) :
    plKerExists cert γstar CSig β B μ i ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      0 ≤ (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2))) := by
  classical
  have hker := (eqn_app_pl_Cil_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i ℓ (show (0 : ℝ) < 1 by norm_num)).2.1
  refine ⟨hker, ?_⟩
  intro x y hx hy
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  exact (prop_app_pl_response_iii cert γstar CSig hB hN μ hpos hβ0.le hβ1
    hγ hμC hC1 (ν := ν) (ν' := ν') rfl rfl ℓ (sq_pos_of_pos hx) (sq_pos_of_pos hy) i).2

private lemma zr_square_integral (f : ℝ × ℝ → ℝ) (L : ℝ)
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
    (hfi (max 1 T) (le_max_left _ _)).mono_set
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hrestrict (T : ℝ) : (volume.restrict R).restrict (φ T) = volume.restrict (φ T) := by
    rw [Measure.restrict_restrict (hm T), inter_eq_left.mpr (hsub T)]
  have heq (T : ℝ) : (∫ p in φ T, f p ∂(volume.restrict R)) =
      ∫ x in (0 : ℝ)..(max 1 T), ∫ y in (0 : ℝ)..(max 1 T), f (x, y) := by
    rw [hrestrict]
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    rw [setIntegral_prod f (by simpa only [← Measure.volume_eq_prod] using hlocal T)]
    simp only [intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ max 1 T by linarith [le_max_left 1 T])]
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

/-- `prop:app-pl-vol-zero`(iii), first equality (the integral over `(0,∞)²` of the row kernel), snapshot
`cr-2026-10-23`. Declaration of record: the lag-`ℓ` kernel is integrable on `(0,∞)²` and nonnegative
(conjuncts 2–3), and `C̄_{i,ℓ}(0) = (4/π²) ∫_0^∞∫_0^∞ 𝔨_{i,ℓ}(x²,y²)`. Existence of the lag responses
for `s, s' > 0` is conjunct 1. LaTeX, verbatim:

\begin{proposition}[Volatility at zero ridge]\label{prop:app-pl-vol-zero}
Let $0<\bar z\le z_1$ and $E_i\defeq A_N\bar z^{-1/2}+2\sqrt{D_i}\,\bar z^{1/4}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ the limit $\overline C_{i,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{i,\ell}(\ridge)$
exists, $\overline C_{i,0}(0)=1$, and $\abs{\overline C_{i,\ell}(\ridge)}\le E_i\,\bmom^{\ell/3}$ for
$0\le\ridge\le\bar z$ and $\ell\ge1$.
\item The series $\mathfrak v_i(0)\defeq1+2\sum_{\ell\ge1}\overline C_{i,\ell}(0)$ converges
absolutely, $\mathfrak v_i(\ridge)\to\mathfrak v_i(0)$ as $\ridge\downarrow0$, and for every
integer $H\ge0$ and $0<\ridge\le\bar z$,
\begin{equation}\label{eqn:app-pl-vol-ridge}
\abs{\mathfrak v_i(\ridge)-\mathfrak v_i(0)}\le2(1+2H)\sqrt{D_i}\,\ridge^{1/4}+\frac{4E_i\,\bmom^{(H+1)/3}}{1-\bmom^{1/3}} .
\end{equation}
\item For every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
all terms are nonnegative, and $\mathfrak v_i(0)=\sum_{\ell\in\mathbb Z}\overline C_{i,\ell}(0)\ge1$ with
$\overline C_{i,-\ell}(0)\defeq\overline C_{i,\ell}(0)$, which is the integral
\cref{eqn:app-pl-vol-zero} with the kernels of the lag $-\ell$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_vol_zero_iii_a (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℕ) :
    plKerExists cert γstar CSig β B μ i ∧
    (∀ x y : ℝ, 0 < x → 0 < y →
      0 ≤ (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2))) ∧
    IntegrableOn (fun p : ℝ × ℝ => (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (p.1 ^ 2)) (iotaF (p.2 ^ 2)))
      (Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ)) ∧
    cbarZero cert γstar CSig β B μ i ℓ = (4 / Real.pi ^ 2) *
      ∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ),
        (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2)) := by
  classical
  obtain ⟨hker, hnnK⟩ := zr_vol_zero_iii_a_basic cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i ℓ
  obtain ⟨R, hR⟩ : ∃ R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ, ∀ ℓ f g, R ℓ f g = (B : ℝ) *
      lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
        (fun _ : Fin N => (1 : ℝ)) f g := ⟨fun ℓ f g => _, fun _ _ _ => rfl⟩
  obtain ⟨hcs, hdom, hnnR, h1, h2, h3⟩ := zr_Rprops cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1 i R hR
  have hγ0 : 0 ≤ γstar := by
    have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
    linarith
  have hCb : 0 ≤ (B : ℝ) * γstar := by positivity
  have hrow : ∀ ℓ ϱ, lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      R ℓ (omegaF ϱ) (omegaF ϱ) := fun ℓ ϱ => (hR ℓ _ _).symm
  have hz0 : 0 < plZ1 β B μ :=
    (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ hB hN hpos).1.mapsTo (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  obtain ⟨-, hlimC, hzero1, -, -⟩ := prop_app_pl_vol_zero_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  have hcont : ContinuousOn (fun p : ℝ × ℝ => (B : ℝ) * lagResp cert γstar CSig β ℓ B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
      (iotaF (p.1 ^ 2)) (iotaF (p.2 ^ 2))) (Ioi 0 ×ˢ Ioi 0) := by
    have := zr_kappa_cont (R ℓ) ((B : ℝ) * γstar) hCb
      (fun f f' g c hf hf' hg => h1 ℓ f f' g c hf hf' hg)
      (fun f g g' c hf hg hg' => h2 ℓ f g g' c hf hg hg') (fun f g hf hg => h3 ℓ f g hf hg)
    simpa only [hR] using this
  have hfi : ∀ δ T : ℝ, 0 < δ → δ ≤ T → IntegrableOn (fun p : ℝ × ℝ => (B : ℝ) *
      lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
      (fun _ : Fin N => (1 : ℝ)) (iotaF (p.1 ^ 2)) (iotaF (p.2 ^ 2))) (Icc δ T ×ˢ Icc δ T) := by
    intro δ T hδ hδT
    refine (hcont.mono ?_).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    intro p hp
    exact ⟨lt_of_lt_of_le hδ hp.1.1, lt_of_lt_of_le hδ hp.2.1⟩
  have hsq : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hone : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ (n : ℝ) + 1 := fun n =>
    (div_le_one (by positivity)).2 (hone n) |>.trans (hone n)
  have hdelta : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2) atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => by
      simp only [mem_Ioi]; exact pow_pos (hsq n) 2⟩
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2
  have hrow0 : Tendsto (fun n : ℕ => lagRowBar cert γstar CSig β 0 B μ (fun _ : Fin N => (1 : ℝ)) i
      ((1 / ((n : ℝ) + 1)) ^ 2) ((1 / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 1) := by
    have := (hlimC 0).comp hdelta
    rwa [hzero1] at this
  have hErr : Tendsto (fun n : ℕ => 4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * ((n : ℝ) + 1)) +
      2 * Real.sqrt (8 * ((B : ℝ) * γstar) * (1 - lagRowBar cert γstar CSig β 0 B μ
        (fun _ : Fin N => (1 : ℝ)) i ((1 / ((n : ℝ) + 1)) ^ 2) ((1 / ((n : ℝ) + 1)) ^ 2)))) atTop (𝓝 0) := by
    have t1 : Tendsto (fun n : ℕ => 4 * CSig * (γstar * Real.sqrt γstar) * B / (Real.pi * ((n : ℝ) + 1)))
        atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (4 * CSig * (γstar * Real.sqrt γstar) * B / Real.pi)
      simp only [mul_zero] at this
      refine this.congr fun n => ?_
      field_simp
    have t2 : Tendsto (fun n : ℕ => 2 * Real.sqrt (8 * ((B : ℝ) * γstar) * (1 - lagRowBar cert γstar CSig β 0 B μ
        (fun _ : Fin N => (1 : ℝ)) i ((1 / ((n : ℝ) + 1)) ^ 2) ((1 / ((n : ℝ) + 1)) ^ 2)))) atTop (𝓝 0) := by
      have := ((((tendsto_const_nhds (x := (1 : ℝ))).sub hrow0).const_mul (8 * ((B : ℝ) * γstar))).sqrt).const_mul 2
      simpa using this
    simpa using t1.add t2
  have hlim : Tendsto (fun n : ℕ => (4 / Real.pi ^ 2) *
      ∫ x in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1), ∫ y in (1 / ((n : ℝ) + 1))..((n : ℝ) + 1),
        (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ))
          (fun _ : Fin N => (1 : ℝ)) (iotaF (x ^ 2)) (iotaF (y ^ 2))) atTop
      (𝓝 (cbarZero cert γstar CSig β B μ i ℓ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun _ => dist_nonneg) (fun n => ?_) hErr
    rw [Real.dist_eq, abs_sub_comm]
    exact zr_hmain cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i ℓ (hsq n)
      (by linarith [hone n]) (hn1 n)
  obtain ⟨hint, hval⟩ := zr_sqint2 _ _ (fun p hp => hnnK p.1 p.2 hp.1 hp.2) hfi hlim
  exact ⟨hker, hnnK, hint, hval.symm⟩


section ZrIiibNat

private lemma zr_iiib_nat (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (n : ℕ) :
    (∀ m₁ ∈ Ioo 0 (gammaOf N B), ∀ m₂ ∈ Ioo 0 (gammaOf N B),
      0 ≤ lagIntegrand β B μ i (n : ℤ) m₁ m₂) ∧
    IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i (n : ℤ) p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) ∧
    cbarZero cert γstar CSig β B μ i n = CbarPart β B μ i (n : ℤ) := by
  classical
  obtain ⟨-, -, hintF, hval⟩ := prop_app_pl_vol_zero_iii_a cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i n
  obtain ⟨-, hnnF⟩ := zr_vol_zero_iii_a_basic cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i n
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := rfl
  have hCs : ∀ j, μ j ≤ CSig := hμC
  obtain ⟨hcov1, hcov2⟩ := zr_cov (β := β) μ hβ0 hβ1 hB hN hanti hpos
  have hbij := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  set F : ℝ × ℝ → ℝ := fun p => (B : ℝ) * lagResp cert γstar CSig β n B μ (fun _ : Fin N => (1 : ℝ))
    (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) (iotaF (p.1 ^ 2)) (iotaF (p.2 ^ 2)) with hF
  have hΦ : ∀ m₁ ∈ Ioo 0 (gammaOf N B), ∀ m₂ ∈ Ioo 0 (gammaOf N B),
      lagIntegrand β B μ i (n : ℤ) m₁ m₂ =
        4 * ((thetaN β B μ m₁ * Real.sqrt (sN β B μ m₁) / 2) *
          (thetaN β B μ m₂ * Real.sqrt (sN β B μ m₂) / 2) *
          F (Real.sqrt (sN β B μ m₁), Real.sqrt (sN β B μ m₂))) := by
    intro m₁ hm₁ m₂ hm₂
    rw [zr_pw μ hβ0 hβ1 hB hN hanti hpos hCs hC1 hν hν' n i hm₁ hm₂]
    have hs1 : 0 < sN β B μ m₁ := hbij.2.2.1.mapsTo hm₁
    have hs2 : 0 < sN β B μ m₂ := hbij.2.2.1.mapsTo hm₂
    have hFe : F (Real.sqrt (sN β B μ m₁), Real.sqrt (sN β B μ m₂)) =
        respRHS β B μ ν ν' n i (sN β B μ m₁) (sN β B μ m₂) := by
      simp only [hF]
      rw [Real.sq_sqrt hs1.le, Real.sq_sqrt hs2.le]
      exact prop_app_pl_response_ii cert γstar CSig hB hN μ hpos hβ0.le hβ1 hγ hμC hC1 hν hν' n hs1 hs2 i
    rw [hFe, Real.sqrt_mul hs1.le]
    ring
  have hc0 : ∀ m ∈ Ioo 0 (gammaOf N B), 0 ≤ thetaN β B μ m * Real.sqrt (sN β B μ m) / 2 := by
    intro m hm
    have := (hbij.2.2.2 m hm).2
    positivity
  have hxpos : ∀ m ∈ Ioo 0 (gammaOf N B), 0 < Real.sqrt (sN β B μ m) := fun m hm =>
    Real.sqrt_pos.mpr (hbij.2.2.1.mapsTo hm)
  have hint : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i (n : ℤ) p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
    have h : IntegrableOn (fun p : ℝ × ℝ => 4 * ((thetaN β B μ p.1 * Real.sqrt (sN β B μ p.1) / 2) *
          (thetaN β B μ p.2 * Real.sqrt (sN β B μ p.2) / 2) *
          F (Real.sqrt (sN β B μ p.1), Real.sqrt (sN β B μ p.2))))
        (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := ((hcov2 F).1 hintF).const_mul 4
    refine h.congr_fun (fun p hp => ?_) (measurableSet_Ioo.prod measurableSet_Ioo)
    exact (hΦ p.1 hp.1 p.2 hp.2).symm
  refine ⟨fun m₁ hm₁ m₂ hm₂ => ?_, hint, ?_⟩
  · rw [hΦ m₁ hm₁ m₂ hm₂]
    have := hnnF _ _ (hxpos m₁ hm₁) (hxpos m₂ hm₂)
    have h1 := hc0 m₁ hm₁
    have h2 := hc0 m₂ hm₂
    simp only [hF] at *
    positivity
  · -- the integral identity
    have hI1 : (∫ x in Ioi (0 : ℝ), ∫ y in Ioi (0 : ℝ), F (x, y)) =
        ∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), F p := by
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      exact (setIntegral_prod F (by simpa only [IntegrableOn, ← Measure.volume_eq_prod] using hintF)).symm
    have hI2 : (∫ m₁ in Ioo 0 (gammaOf N B), ∫ m₂ in Ioo 0 (gammaOf N B),
        lagIntegrand β B μ i (n : ℤ) m₁ m₂) =
        ∫ p in Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B), lagIntegrand β B μ i (n : ℤ) p.1 p.2 := by
      rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
      exact (setIntegral_prod (fun p : ℝ × ℝ => lagIntegrand β B μ i (n : ℤ) p.1 p.2)
        (by simpa only [IntegrableOn, ← Measure.volume_eq_prod] using hint)).symm
    have hI3 : (∫ p in Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B), lagIntegrand β B μ i (n : ℤ) p.1 p.2) =
        4 * ∫ p in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), F p := by
      rw [hcov1 F, ← integral_const_mul]
      exact setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
        fun p hp => hΦ p.1 hp.1 p.2 hp.2
    unfold CbarPart lagTerm
    rw [hval, hI1, hI2, hI3]
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp

private lemma zr_lag_neg (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N) (n : ℕ) (hn : 0 < n)
    (m₁ m₂ : ℝ) :
    lagIntegrand β B μ i (-(n : ℤ)) m₁ m₂ = lagIntegrand β B μ i (n : ℤ) m₂ m₁ := by
  have h0 : ¬ (0 ≤ -(n : ℤ)) := by omega
  have h1 : (0 : ℤ) ≤ (n : ℤ) := by omega
  unfold lagIntegrand lagNumer deltaN DLag MLag TNpart
  rw [if_neg h0, if_pos h1, if_neg h0, if_pos h1]
  simp only [neg_neg, Int.toNat_natCast]
  have hT : ∑ j : Fin N, partF B μ j m₁ * partF B μ j m₂ = ∑ j : Fin N, partF B μ j m₂ * partF B μ j m₁ :=
    Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hT, mul_comm m₁ m₂, mul_comm (Wpart β B μ i m₁)]
  ring_nf

end ZrIiibNat

/-- `prop:app-pl-vol-zero`(iii), second equality (the participation form, the bridge `C̄_{i,ℓ}(0) = CbarPart`),
snapshot `cr-2026-10-23`. Declaration of record: the integrand `W_i(m₁)W_i(m₂)𝖣_ℓ/Δ^N_ℓ` is nonnegative and
integrable on `(0,γ)²` (conjuncts 1–2), and `C̄_{i,ℓ}(0) = (1/π²)∫_0^γ∫_0^γ W_i W_i 𝖣_ℓ/Δ^N_ℓ`, which is
`CbarPart` (conjunct 3). Stated for every `ℓ ∈ ℤ`: for `ℓ < 0` the left side is `C̄_{i,-ℓ}(0) ≔ C̄_{i,|ℓ|}(0)`
and the right side is the integral with the kernels of the lag `ℓ` (last sentence of (iii)). LaTeX, verbatim:

\begin{proposition}[Volatility at zero ridge]\label{prop:app-pl-vol-zero}
Let $0<\bar z\le z_1$ and $E_i\defeq A_N\bar z^{-1/2}+2\sqrt{D_i}\,\bar z^{1/4}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ the limit $\overline C_{i,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{i,\ell}(\ridge)$
exists, $\overline C_{i,0}(0)=1$, and $\abs{\overline C_{i,\ell}(\ridge)}\le E_i\,\bmom^{\ell/3}$ for
$0\le\ridge\le\bar z$ and $\ell\ge1$.
\item The series $\mathfrak v_i(0)\defeq1+2\sum_{\ell\ge1}\overline C_{i,\ell}(0)$ converges
absolutely, $\mathfrak v_i(\ridge)\to\mathfrak v_i(0)$ as $\ridge\downarrow0$, and for every
integer $H\ge0$ and $0<\ridge\le\bar z$,
\begin{equation}\label{eqn:app-pl-vol-ridge}
\abs{\mathfrak v_i(\ridge)-\mathfrak v_i(0)}\le2(1+2H)\sqrt{D_i}\,\ridge^{1/4}+\frac{4E_i\,\bmom^{(H+1)/3}}{1-\bmom^{1/3}} .
\end{equation}
\item For every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
all terms are nonnegative, and $\mathfrak v_i(0)=\sum_{\ell\in\mathbb Z}\overline C_{i,\ell}(0)\ge1$ with
$\overline C_{i,-\ell}(0)\defeq\overline C_{i,\ell}(0)$, which is the integral
\cref{eqn:app-pl-vol-zero} with the kernels of the lag $-\ell$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_vol_zero_iii_b (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (ℓ : ℤ) :
    (∀ m₁ ∈ Ioo 0 (gammaOf N B), ∀ m₂ ∈ Ioo 0 (gammaOf N B),
      0 ≤ lagIntegrand β B μ i ℓ m₁ m₂) ∧
    IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2)
      (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) ∧
    cbarZero cert γstar CSig β B μ i ℓ.natAbs = CbarPart β B μ i ℓ := by
  classical
  rcases le_or_gt 0 ℓ with h | h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simpa only [Int.natAbs_natCast] using
      zr_iiib_nat cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i n
  · obtain ⟨n, hℓ, hn⟩ : ∃ n : ℕ, ℓ = -(n : ℤ) ∧ 0 < n := ⟨ℓ.natAbs, by omega, by omega⟩
    subst hℓ
    obtain ⟨ha, hb, hc⟩ := zr_iiib_nat cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i n
    have hneg := zr_lag_neg β B μ i n hn
    have hnat : (-(n : ℤ)).natAbs = n := by simp
    rw [hnat]
    refine ⟨fun m₁ hm₁ m₂ hm₂ => ?_, ?_, ?_⟩
    · rw [hneg]; exact ha m₂ hm₂ m₁ hm₁
    · -- integrability of the swapped function
      have hsw : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i (n : ℤ) p.2 p.1)
          (Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)) := by
        unfold IntegrableOn at hb ⊢
        rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
          ← Measure.prod_restrict] at hb ⊢
        exact hb.swap
      exact hsw.congr_fun (fun p hp => (hneg p.1 p.2).symm) (measurableSet_Ioo.prod measurableSet_Ioo)
    · have hsw : Integrable (fun p : ℝ × ℝ => lagIntegrand β B μ i (n : ℤ) p.2 p.1)
          ((volume.restrict (Ioo 0 (gammaOf N B))).prod (volume.restrict (Ioo 0 (gammaOf N B)))) := by
        have hb' := hb
        unfold IntegrableOn at hb'
        rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
          ← Measure.prod_restrict] at hb'
        exact hb'.swap
      rw [hc]
      unfold CbarPart lagTerm
      congr 1
      simp only [hneg]
      exact (integral_integral_swap (f := fun a b => lagIntegrand β B μ i (n : ℤ) b a) hsw).symm ▸ rfl

/-- `prop:app-pl-vol-zero`(iii), the lag sum (`𝔳_i(0) = ∑_{ℓ∈ℤ} C̄_{i,ℓ}(0)`, `C̄_{i,-ℓ}(0) = C̄_{i,ℓ}(0)`),
snapshot `cr-2026-10-23`. Declaration of record: all terms are nonnegative (conjunct 1), the lag sum over `ℤ`
converges to `𝔳_i(0)` (conjunct 2), and `𝔳_i(0) ≥ 1` (conjunct 3). LaTeX, verbatim:

\begin{proposition}[Volatility at zero ridge]\label{prop:app-pl-vol-zero}
Let $0<\bar z\le z_1$ and $E_i\defeq A_N\bar z^{-1/2}+2\sqrt{D_i}\,\bar z^{1/4}$.
\begin{enumerate}[label=(\roman*)]
\item For every $\ell\ge0$ the limit $\overline C_{i,\ell}(0)\defeq\lim_{\ridge\downarrow0}\overline C_{i,\ell}(\ridge)$
exists, $\overline C_{i,0}(0)=1$, and $\abs{\overline C_{i,\ell}(\ridge)}\le E_i\,\bmom^{\ell/3}$ for
$0\le\ridge\le\bar z$ and $\ell\ge1$.
\item The series $\mathfrak v_i(0)\defeq1+2\sum_{\ell\ge1}\overline C_{i,\ell}(0)$ converges
absolutely, $\mathfrak v_i(\ridge)\to\mathfrak v_i(0)$ as $\ridge\downarrow0$, and for every
integer $H\ge0$ and $0<\ridge\le\bar z$,
\begin{equation}\label{eqn:app-pl-vol-ridge}
\abs{\mathfrak v_i(\ridge)-\mathfrak v_i(0)}\le2(1+2H)\sqrt{D_i}\,\ridge^{1/4}+\frac{4E_i\,\bmom^{(H+1)/3}}{1-\bmom^{1/3}} .
\end{equation}
\item For every $\ell\ge0$,
\begin{equation}\label{eqn:app-pl-vol-zero}
\overline C_{i,\ell}(0)=\frac4{\pi^2}\int_0^\infty\!\!\int_0^\infty\mathfrak k_{i,\ell}(x^2,y^2)\,\dif x\,\dif y
=\frac1{\pi^2}\int_0^\gamma\!\!\int_0^\gamma W_i(m_1)W_i(m_2)\,\frac{\mathsf D_\ell}{\Delta_\ell^N}\,\dif m_1\,\dif m_2 ,
\end{equation}
all terms are nonnegative, and $\mathfrak v_i(0)=\sum_{\ell\in\mathbb Z}\overline C_{i,\ell}(0)\ge1$ with
$\overline C_{i,-\ell}(0)\defeq\overline C_{i,\ell}(0)$, which is the integral
\cref{eqn:app-pl-vol-zero} with the kernels of the lag $-\ell$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_pl_vol_zero_iii_c (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    (∀ ℓ : ℕ, 0 ≤ cbarZero cert γstar CSig β B μ i ℓ) ∧
    HasSum (fun ℓ : ℤ => cbarZero cert γstar CSig β B μ i ℓ.natAbs)
      (vZero cert γstar CSig β B μ i) ∧
    1 ≤ vZero cert γstar CSig β B μ i := by
  classical
  have hz0 : 0 < plZ1 β B μ :=
    (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ hB hN hpos).1.mapsTo (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hnn : ∀ ℓ : ℕ, 0 ≤ cbarZero cert γstar CSig β B μ i ℓ := by
    intro ℓ
    obtain ⟨-, -, hc⟩ := zr_iiib_nat cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i ℓ
    obtain ⟨ha, -, -⟩ := zr_iiib_nat cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1 i ℓ
    rw [hc]
    unfold CbarPart lagTerm
    refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
    refine setIntegral_nonneg measurableSet_Ioo fun m₁ hm₁ => ?_
    exact setIntegral_nonneg measurableSet_Ioo fun m₂ hm₂ => ha m₁ hm₁ m₂ hm₂
  obtain ⟨-, -, hsum, -, -⟩ := prop_app_pl_vol_zero_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  have hsum' : Summable (fun k : ℕ => cbarZero cert γstar CSig β B μ i (k + 1)) :=
    Summable.of_norm (by simpa only [Real.norm_eq_abs] using hsum)
  obtain ⟨-, -, hone, -, -⟩ := prop_app_pl_vol_zero_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  have hS0 : 0 ≤ ∑' k : ℕ, cbarZero cert γstar CSig β B μ i (k + 1) := tsum_nonneg fun k => hnn _
  have hnat : HasSum (fun n : ℕ => cbarZero cert γstar CSig β B μ i n)
      (1 + ∑' k : ℕ, cbarZero cert γstar CSig β B μ i (k + 1)) := by
    have := (summable_nat_add_iff 1).mp hsum'
    have h2 := this.hasSum
    rw [this.tsum_eq_zero_add, hone] at h2
    exact h2
  have hneg : HasSum (fun n : ℕ => cbarZero cert γstar CSig β B μ i (-((n : ℤ) + 1)).natAbs)
      (∑' k : ℕ, cbarZero cert γstar CSig β B μ i (k + 1)) := by
    have : ∀ n : ℕ, (-((n : ℤ) + 1)).natAbs = n + 1 := fun n => by omega
    simp only [this]
    exact hsum'.hasSum
  have hZ := HasSum.of_nat_of_neg_add_one
    (f := fun ℓ : ℤ => cbarZero cert γstar CSig β B μ i ℓ.natAbs)
    (by simpa only [Int.natAbs_natCast] using hnat) hneg
  refine ⟨hnn, ?_, ?_⟩
  · convert hZ using 1
    unfold vZero
    ring
  · unfold vZero
    linarith

/-! ## Coefficients at zero ridge are limits (`def:app-pl-coefficients`) -/

/-- Drift limit of `def:app-pl-coefficients` (the sentence "they are the limits as `ϱ↓0` of the coefficients"),
snapshot `cr-2026-10-23`: `𝔡_i(ϱ) → 𝔡_i(0) = dZero` as `ϱ ↓ 0`, with `𝔡_i(ϱ) = Muon.Drift.kernel` and
`dZero` of `def:app-pl-coefficients`. LaTeX, verbatim:

\begin{definition}[Coefficients at zero normalized ridge]\label{def:app-pl-coefficients}
At a finite dimension with positive spectrum, the zero-ridge drift
coefficient $\mathfrak d_i(0)$ is the integral \cref{eqn:app-pl-drift-zero}, and the
zero-ridge lag and integrated volatility coefficients $\overline C_{i,\ell}(0)$ and
$\mathfrak v_i(0)$ are those of \cref{prop:app-pl-vol-zero}. By
\cref{prop:app-pl-drift-zero,prop:app-pl-vol-zero} they are the limits as
$\ridge\downarrow0$ of the coefficients $\mathfrak d_i(\ridge)$, $\overline C_{i,\ell}(\ridge)$
and $\mathfrak v_i(\ridge)$ of \cref{sec:app-drift,sec:app-vol}.
\end{definition}
-/
theorem def_app_pl_coefficients_i {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    {Cs : ℝ} (hμCs : ∀ i, μ i ≤ Cs) (h1Cs : 1 ≤ Cs) (i : Fin N) :
    Tendsto (fun ϱ : ℝ => Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1) (𝓝[>] (0 : ℝ))
      (𝓝 (dZero β B μ i)) := by
  obtain ⟨C, hC⟩ := prop_app_pl_drift_zero_ii_kernel hβ0 hβ1
  have hbd : ∀ ϱ : ℝ, 0 < ϱ →
      |Muon.Drift.kernel (emaW β) ν ν' ϱ (μ i) 1 - dZero β B μ i| ≤
        C / gammaOf N B * Real.sqrt ϱ * (1 + Real.sqrt (Qm β (gammaOf N B))) :=
    fun ϱ hϱ => hC N B μ ν ν' Cs hB hN hanti hpos hμCs h1Cs hν hν' ϱ hϱ i
  have hlim : Tendsto (fun ϱ : ℝ => C / gammaOf N B * Real.sqrt ϱ *
      (1 + Real.sqrt (Qm β (gammaOf N B)))) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h0 : Tendsto (fun ϱ : ℝ => Real.sqrt ϱ) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    simpa using (h0.const_mul (C / gammaOf N B)).mul_const (1 + Real.sqrt (Qm β (gammaOf N B)))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
  rw [Real.dist_eq]
  exact hbd ϱ hϱ

/-- Volatility limits of `def:app-pl-coefficients` (`C̄_{i,ℓ}(0)` and `𝔳_i(0)` are the `ϱ ↓ 0` limits of the
D-coefficients), snapshot `cr-2026-10-23`. The same limit clauses as `prop:app-pl-vol-zero`(i),(ii), recorded
against the definitions `cbarZero`, `vZero`. LaTeX, verbatim:

\begin{definition}[Coefficients at zero normalized ridge]\label{def:app-pl-coefficients}
At a finite dimension with positive spectrum, the zero-ridge drift
coefficient $\mathfrak d_i(0)$ is the integral \cref{eqn:app-pl-drift-zero}, and the
zero-ridge lag and integrated volatility coefficients $\overline C_{i,\ell}(0)$ and
$\mathfrak v_i(0)$ are those of \cref{prop:app-pl-vol-zero}. By
\cref{prop:app-pl-drift-zero,prop:app-pl-vol-zero} they are the limits as
$\ridge\downarrow0$ of the coefficients $\mathfrak d_i(\ridge)$, $\overline C_{i,\ell}(\ridge)$
and $\mathfrak v_i(\ridge)$ of \cref{sec:app-drift,sec:app-vol}.
\end{definition}
-/
theorem def_app_pl_coefficients_ii (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) :
    plRowExists cert γstar CSig β B μ i ∧
    (∀ ℓ : ℕ, Tendsto (fun ϱ : ℝ => lagRowBar cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (cbarZero cert γstar CSig β B μ i ℓ))) ∧
    (∀ ϱ : ℝ, 0 < ϱ →
      Summable (fun ℓ : ℕ => lagRowBar cert γstar CSig β (ℓ + 1) B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)) ∧
    Tendsto (fun ϱ : ℝ => rowVBar cert γstar CSig β B μ (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ)
      (𝓝[>] (0 : ℝ)) (𝓝 (vZero cert γstar CSig β B μ i)) := by
  have hz0 : 0 < plZ1 β B μ :=
    (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ hB hN hpos).1.mapsTo (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  obtain ⟨h1, h2, -, -, -⟩ := prop_app_pl_vol_zero_i cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  obtain ⟨-, -, -, h4, -⟩ := prop_app_pl_vol_zero_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hz0 le_rfl
  exact ⟨h1, h2, fun ϱ hϱ => (eqn_app_pl_Cil_ii cert γstar CSig hB hN μ hanti hpos hβ0 hβ1
    hγ hμC hC1 i hϱ).2.1, h4⟩

/-! ## Spectral amplitude (`lem:app-pl-amplitude`) -/

private lemma zr_amp_partMN {N B : ℕ} (μ : Fin N → ℝ) {c : ℝ} (hc : 0 < c)
    (Λ : ℝ) :
    partMN B (fun j => c * μ j) (Λ / c) = partMN B μ Λ := by
  unfold partMN
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  field_simp [hc.ne']

private lemma zr_amp_partLam {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {c : ℝ} (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partLam B (fun j => c * μ j) m = partLam B μ m / c := by
  have hposc : ∀ i, 0 < c * μ i := fun i => mul_pos hc (hpos i)
  obtain ⟨hb, hbL, -, -⟩ := def_app_pl_participation_bij μ hB hN hpos
  obtain ⟨hbc, hbcL, -, -⟩ :=
    def_app_pl_participation_bij (fun j => c * μ j) hB hN hposc
  apply hbc.injOn (hbcL.mapsTo hm) (Set.mem_Ioi.2 (div_pos (hbL.mapsTo hm) hc))
  have hec := hbc.invOn_invFunOn.2 hm
  have he := hb.invOn_invFunOn.2 hm
  change partMN B (fun j => c * μ j) (partLam B (fun j => c * μ j) m) = m at hec
  change partMN B μ (partLam B μ m) = m at he
  rw [hec, zr_amp_partMN μ hc, he]

private lemma zr_amp_partF {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {c : ℝ} (hc : 0 < c)
    (i : Fin N) {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    partF B (fun j => c * μ j) i m = partF B μ i m := by
  unfold partF
  rw [zr_amp_partLam hB hN μ hpos hc hm]
  field_simp [hc.ne']

private lemma zr_amp_sN {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i) {β c : ℝ} (hc : 0 < c)
    {m : ℝ} (hm : m ∈ Ioo 0 (gammaOf N B)) :
    sN β B (fun j => c * μ j) m = c * sN β B μ m := by
  unfold sN
  rw [zr_amp_partLam hB hN μ hpos hc hm]
  field_simp [hc.ne']

private lemma zr_amp_mOf {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) {s : ℝ} (hs : 0 < s) :
    mOf β B (fun j => c * μ j) (c * s) = mOf β B μ s := by
  have hposc : ∀ i, 0 < c * μ i := fun i => mul_pos hc (hpos i)
  have hantic : Antitone (fun j => c * μ j) := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hanti hij) hc.le
  have hb := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  have hbc := (prop_app_pl_branch_i (fun j => c * μ j) hβ0 hβ1 hB hN hantic hposc).2.2.1
  obtain ⟨m, hm, hms⟩ := hb.surjOn (Set.mem_Ioi.2 hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨m, hm, hms⟩
  have hmOf : mOf β B μ s ∈ Ioo (0 : ℝ) (gammaOf N B) ∧
      sN β B μ (mOf β B μ s) = s := by
    unfold mOf
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  have hexc : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B),
      sN β B (fun j => c * μ j) a = c * s :=
    ⟨mOf β B μ s, hmOf.1, by rw [zr_amp_sN hB hN μ hpos hc hmOf.1, hmOf.2]⟩
  have hmOfc : mOf β B (fun j => c * μ j) (c * s) ∈ Ioo (0 : ℝ) (gammaOf N B) ∧
      sN β B (fun j => c * μ j) (mOf β B (fun j => c * μ j) (c * s)) = c * s := by
    unfold mOf
    exact ⟨Function.invFunOn_mem hexc, Function.invFunOn_eq hexc⟩
  exact hbc.injOn hmOfc.1 hmOf.1 (hmOfc.2.trans
    (by rw [zr_amp_sN hB hN μ hpos hc hmOf.1, hmOf.2]))

private lemma zr_amp_Gfun {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (i : Fin N) {s : ℝ} (hs : 0 < s) :
    Gfun β B (fun j => c * μ j) i (c * s) = Gfun β B μ i s := by
  have hb := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨m, hm, hms⟩ := hb.surjOn (Set.mem_Ioi.2 hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨m, hm, hms⟩
  have hm : mOf β B μ s ∈ Ioo (0 : ℝ) (gammaOf N B) := by
    unfold mOf
    exact Function.invFunOn_mem hex
  unfold Gfun
  rw [zr_amp_mOf hB hN hβ0 hβ1 μ hanti hpos hc hs,
    zr_amp_partF hB hN μ hpos hc i hm]

private lemma zr_amp_G_integral {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (i : Fin N) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    (∫ u in Ioi (0 : ℝ), Gfun β B (fun j => c * μ j) i (ϱ + u ^ 2)) =
      Real.sqrt c * ∫ u in Ioi (0 : ℝ), Gfun β B μ i (ϱ / c + u ^ 2) := by
  have ha : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hac : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  have hchange := integral_comp_mul_left_Ioi'
    (fun u : ℝ => Gfun β B (fun j => c * μ j) i (ϱ + u ^ 2)) 0 ha
  simp only [mul_zero] at hchange
  rw [← hchange, smul_eq_mul]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hs : 0 < ϱ / c + u ^ 2 :=
    add_pos_of_nonneg_of_pos (div_nonneg hϱ hc.le) (sq_pos_of_pos hu)
  have he : ϱ + (Real.sqrt c * u) ^ 2 = c * (ϱ / c + u ^ 2) := by
    rw [mul_pow, hac]
    field_simp [hc.ne']
  change Gfun β B (fun j => c * μ j) i (ϱ + (Real.sqrt c * u) ^ 2) =
    Gfun β B μ i (ϱ / c + u ^ 2)
  rw [he, zr_amp_Gfun hB hN hβ0 hβ1 μ hanti hpos hc i hs]

private lemma zr_amp_dPart {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (i : Fin N) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) :
    dPart β B (fun j => c * μ j) i ϱ = Real.sqrt c * dPart β B μ i (ϱ / c) := by
  unfold dPart
  rw [zr_amp_G_integral hB hN hβ0 hβ1 μ hanti hpos hc i hϱ]
  ring

private lemma zr_amp_dZero {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (i : Fin N) :
    dZero β B (fun j => c * μ j) i = Real.sqrt c * dZero β B μ i := by
  unfold dZero
  have h := zr_amp_G_integral hB hN hβ0 hβ1 μ hanti hpos hc i
    (show (0 : ℝ) ≤ 0 by rfl)
  simp only [zero_add, zero_div] at h
  rw [h]
  ring

private lemma zr_amp_branch {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) {ν νc ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hνc : (νc : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (c * μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    {CS1 CS2 : ℝ} (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    {s : ℝ} (hs : 0 < s) :
    respQ β νc ν' (c * s) = respQ β ν ν' s ∧
    (Muon.DetEquiv.branchSol (Fw (emaW β)) νc ν' (c * s)).2.2.1 =
      (Muon.DetEquiv.branchSol (Fw (emaW β)) ν ν' s).2.2.1 ∧
    (Muon.DetEquiv.branchSol (Fw (emaW β)) νc ν' (c * s)).2.2.2 =
      c * (Muon.DetEquiv.branchSol (Fw (emaW β)) ν ν' s).2.2.2 ∧
    (Muon.DetEquiv.branchSol (Fw (emaW β)) νc ν' (c * s)).1 =
      (Muon.DetEquiv.branchSol (Fw (emaW β)) ν ν' s).1 ∧
    (Muon.DetEquiv.branchSol (Fw (emaW β)) νc ν' (c * s)).2.1 =
      (Muon.DetEquiv.branchSol (Fw (emaW β)) ν ν' s).2.1 / c := by
  have hposc : ∀ i, 0 < c * μ i := fun i => mul_pos hc (hpos i)
  have hantic : Antitone (fun j => c * μ j) := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hanti hij) hc.le
  have hb := (prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos).2.2.1
  obtain ⟨m, hm, hms⟩ := hb.surjOn (Set.mem_Ioi.2 hs)
  have hex : ∃ a ∈ Ioo (0 : ℝ) (gammaOf N B), sN β B μ a = s := ⟨m, hm, hms⟩
  have hmOf : mOf β B μ s ∈ Ioo (0 : ℝ) (gammaOf N B) ∧
      sN β B μ (mOf β B μ s) = s := by
    unfold mOf
    exact ⟨Function.invFunOn_mem hex, Function.invFunOn_eq hex⟩
  obtain ⟨hq, ht, hs1, hσ, hσt, -⟩ := prop_app_pl_branch_ii μ hβ0 hβ1 hB hN
    hanti hpos hν hν' hμC1 hC11 hs hmOf.1 hmOf.2
  have hsmc : sN β B (fun j => c * μ j) (mOf β B μ s) = c * s := by
    rw [zr_amp_sN hB hN μ hpos hc hmOf.1, hmOf.2]
  obtain ⟨hqc, htc, hs1c, hσc, hσtc, -⟩ :=
    prop_app_pl_branch_ii (fun j => c * μ j) hβ0 hβ1 hB hN hantic hposc
      hνc hν' hμC2 hC12 (mul_pos hc hs) hmOf.1 hsmc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · unfold respQ
    rw [hqc, hq]
  · rw [htc, ht, zr_amp_partLam hB hN μ hpos hc hmOf.1]
    field_simp [hc.ne']
  · rw [hs1c, hs1]
    ring
  · rw [hσc, hσ, zr_amp_partLam hB hN μ hpos hc hmOf.1]
    field_simp [hc.ne']
  · rw [hσtc, hσt]
    field_simp [hc.ne']

private lemma zr_amp_respRHS {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) {ν νc ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hνc : (νc : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (c * μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    {CS1 CS2 : ℝ} (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    (ℓ : ℕ) (i : Fin N) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    respRHS β B (fun j => c * μ j) νc ν' ℓ i (c * s) (c * t) =
      c⁻¹ * respRHS β B μ ν ν' ℓ i s t := by
  have hbs := zr_amp_branch hB hN hβ0 hβ1 μ hanti hpos hc hν hνc hν'
    hμC1 hC11 hμC2 hC12 hs
  have hbt := zr_amp_branch hB hN hβ0 hβ1 μ hanti hpos hc hν hνc hν'
    hμC1 hC11 hμC2 hC12 ht
  have hU : respU β B (fun j => c * μ j) νc ν' (c * s) (c * t) =
      respU β B μ ν ν' s t := by
    unfold respU
    rw [hbs.2.1, hbt.2.1]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hc.ne']
  have hV : respV β B N νc ν' (c * s) (c * t) =
      c⁻¹ ^ 2 * respV β B N ν ν' s t := by
    unfold respV
    rw [hbs.2.2.1, hbt.2.2.1]
    field_simp [hc.ne']
  have hΔ : respDelta β B (fun j => c * μ j) νc ν' ℓ (c * s) (c * t) =
      respDelta β B μ ν ν' ℓ s t := by
    unfold respDelta
    rw [hU, hV, hbs.1, hbt.1, hbs.2.2.2.1, hbt.2.2.2.1,
      hbs.2.2.2.2, hbt.2.2.2.2]
    field_simp [hc.ne']
  unfold respRHS
  rw [hbs.1, hbt.1, hbs.2.1, hbt.2.1, hbs.2.2.1, hbt.2.2.1, hΔ]
  field_simp [hc.ne']

private lemma zr_amp_kernel (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (γs1 CS1 γs2 CS2 : ℝ)
    (hγ1 : gammaOf N B ≤ γs1) (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (hγ2 : gammaOf N B ≤ γs2) (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    {ν νc ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hνc : (νc : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (c * μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) (i : Fin N) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    (B : ℝ) * lagResp cert γs2 CS2 β ℓ B (fun j => c * μ j)
        (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (iotaF (c * s)) (iotaF (c * t)) =
      c⁻¹ * ((B : ℝ) * lagResp cert γs1 CS1 β ℓ B μ
        (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (iotaF s) (iotaF t)) := by
  rw [prop_app_pl_response_ii cert γs2 CS2 hB hN (fun j => c * μ j)
      (fun j => mul_pos hc (hpos j)) hβ0.le hβ1 hγ2 hμC2 hC12 hνc hν' ℓ
      (mul_pos hc hs) (mul_pos hc ht) i,
    prop_app_pl_response_ii cert γs1 CS1 hB hN μ hpos hβ0.le hβ1 hγ1 hμC1 hC11
      hν hν' ℓ hs ht i,
    zr_amp_respRHS hB hN hβ0 hβ1 μ hanti hpos hc hν hνc hν'
      hμC1 hC11 hμC2 hC12 ℓ i hs ht]

private lemma zr_amp_square_change (f : ℝ → ℝ → ℝ) {a : ℝ} (ha : 0 < a) (T : ℝ) :
    (∫ x in (0 : ℝ)..a * T, ∫ y in (0 : ℝ)..a * T, f x y) =
      a ^ 2 * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, f (a * x) (a * y) := by
  calc
    _ = a * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..a * T, f (a * x) y := by
      symm
      simpa only [zero_mul, mul_zero, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (fun x : ℝ => ∫ y in (0 : ℝ)..a * T, f x y) (a := 0) (b := T) a)
    _ = a * ∫ x in (0 : ℝ)..T, a * ∫ y in (0 : ℝ)..T, f (a * x) (a * y) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro x _
      symm
      simpa only [zero_mul, mul_zero, smul_eq_mul] using
        (intervalIntegral.smul_integral_comp_mul_left
          (fun y : ℝ => f (a * x) y) (a := 0) (b := T) a)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      ring

private lemma zr_amp_row (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c) (γs1 CS1 γs2 CS2 : ℝ)
    (hγ1 : gammaOf N B ≤ γs1) (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (hγ2 : gammaOf N B ≤ γs2) (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    {ν νc ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hνc : (νc : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (c * μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) (i : Fin N) {r : ℝ} (hr : 0 < r) :
    lagRowBar cert γs2 CS2 β ℓ B (fun j => c * μ j) (fun _ : Fin N => (1 : ℝ)) i
        (c * r) (c * r) =
      lagRowBar cert γs1 CS1 β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r := by
  have hposc : ∀ i, 0 < c * μ i := fun i => mul_pos hc (hpos i)
  have hantic : Antitone (fun j => c * μ j) := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hanti hij) hc.le
  have ha : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hac : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
  let Kc : ℝ → ℝ → ℝ := fun x y =>
    (B : ℝ) * lagResp cert γs2 CS2 β ℓ B (fun j => c * μ j)
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
      (iotaF (c * r + x ^ 2)) (iotaF (c * r + y ^ 2))
  let Kb : ℝ → ℝ → ℝ := fun x y =>
    (B : ℝ) * lagResp cert γs1 CS1 β ℓ B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
      (iotaF (r + x ^ 2)) (iotaF (r + y ^ 2))
  have hk (x y : ℝ) : Kc (Real.sqrt c * x) (Real.sqrt c * y) = c⁻¹ * Kb x y := by
    have ex : c * r + (Real.sqrt c * x) ^ 2 = c * (r + x ^ 2) := by
      rw [mul_pow, hac]
      ring
    have ey : c * r + (Real.sqrt c * y) ^ 2 = c * (r + y ^ 2) := by
      rw [mul_pow, hac]
      ring
    dsimp only [Kc, Kb]
    rw [ex, ey]
    exact zr_amp_kernel cert hB hN hβ0 hβ1 μ hanti hpos hc γs1 CS1 γs2 CS2
      hγ1 hμC1 hC11 hγ2 hμC2 hC12 hν hνc hν' ℓ i
      (add_pos_of_pos_of_nonneg hr (sq_nonneg x))
      (add_pos_of_pos_of_nonneg hr (sq_nonneg y))
  have hsq (T : ℝ) :
      (4 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..Real.sqrt c * T,
        ∫ y in (0 : ℝ)..Real.sqrt c * T, Kc x y) =
      (4 / Real.pi ^ 2) * (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, Kb x y) := by
    rw [zr_amp_square_change Kc ha T]
    simp_rw [hk, intervalIntegral.integral_const_mul]
    rw [hac]
    field_simp [hc.ne']
  have hLc := (eqn_app_pl_Cil_i cert γs2 CS2 hB hN (fun j => c * μ j) hantic hposc
    hβ0 hβ1 hγ2 hμC2 hC12 i ℓ (mul_pos hc hr)).2.2.2
  have hLb := (eqn_app_pl_Cil_i cert γs1 CS1 hB hN μ hanti hpos hβ0 hβ1
    hγ1 hμC1 hC11 i ℓ hr).2.2.2
  change Tendsto (fun T : ℝ => (4 / Real.pi ^ 2) *
    (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, Kc x y)) atTop
      (𝓝 (lagRowBar cert γs2 CS2 β ℓ B (fun j => c * μ j)
        (fun _ : Fin N => (1 : ℝ)) i (c * r) (c * r))) at hLc
  change Tendsto (fun T : ℝ => (4 / Real.pi ^ 2) *
    (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, Kb x y)) atTop
      (𝓝 (lagRowBar cert γs1 CS1 β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r)) at hLb
  have htop : Tendsto (fun T : ℝ => Real.sqrt c * T) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos ha).2 tendsto_id
  have hLc' := hLc.comp htop
  have hLc'' := hLc'.congr' (Eventually.of_forall hsq)
  exact tendsto_nhds_unique hLc'' hLb

/-- `lem:app-pl-amplitude`, positive ridge, snapshot `cr-2026-10-23`. Declaration of record for `ϱ > 0`:
the drift and the row coefficients of `cμ` at `ϱ` equal those of `μ` at `ϱ/c`, with the drift
carrying the factor `√c`. The row objects of `μ` and of `cμ` are taken with independent admissible
constants `(γ⋆, C_Σ)`, which is the independence asserted by the source (conjuncts 1–2 are the existence
of both row limits). LaTeX, verbatim:

\begin{lemma}[Spectral amplitude]\label{lem:app-pl-amplitude}
Write $\mathfrak d_i(\ridge;\mu)$, $\overline C_{i,\ell}(\ridge;\mu)$ and $\mathfrak v_i(\ridge;\mu)$
for the coefficients of the spectrum $\mu=(\mu_j)$. For every $c>0$ and $\ridge\ge0$,
\[
\mathfrak d_i(\ridge;c\mu)=\sqrt c\,\mathfrak d_i(\ridge/c;\mu),\qquad
\overline C_{i,\ell}(\ridge;c\mu)=\overline C_{i,\ell}(\ridge/c;\mu),\qquad
\mathfrak v_i(\ridge;c\mu)=\mathfrak v_i(\ridge/c;\mu).
\]
\end{lemma}
-/
theorem lem_app_pl_amplitude_i (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c)
    (γs1 CS1 : ℝ) (hγ1 : gammaOf N B ≤ γs1) (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (γs2 CS2 : ℝ) (hγ2 : gammaOf N B ≤ γs2) (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    {ν νc ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hνc : (νc : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (c * μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (i : Fin N) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    plRowExists cert γs1 CS1 β B μ i ∧ plRowExists cert γs2 CS2 β B (fun j => c * μ j) i ∧
    Summable (fun ℓ : ℕ => lagRowBar cert γs2 CS2 β (ℓ + 1) B (fun j => c * μ j)
      (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ) ∧
    Summable (fun ℓ : ℕ => lagRowBar cert γs1 CS1 β (ℓ + 1) B μ (fun _ : Fin N => (1 : ℝ))
      i (ϱ / c) (ϱ / c)) ∧
    Muon.Drift.kernel (emaW β) νc ν' ϱ (c * μ i) 1 =
      Real.sqrt c * Muon.Drift.kernel (emaW β) ν ν' (ϱ / c) (μ i) 1 ∧
    (∀ ℓ : ℕ, lagRowBar cert γs2 CS2 β ℓ B (fun j => c * μ j) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      lagRowBar cert γs1 CS1 β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i (ϱ / c) (ϱ / c)) ∧
    rowVBar cert γs2 CS2 β B (fun j => c * μ j) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
      rowVBar cert γs1 CS1 β B μ (fun _ : Fin N => (1 : ℝ)) i (ϱ / c) (ϱ / c) := by
  have hposc : ∀ j, 0 < c * μ j := fun j => mul_pos hc (hpos j)
  have hantic : Antitone (fun j => c * μ j) := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hanti hij) hc.le
  have hr : 0 < ϱ / c := div_pos hϱ hc
  have hbase := eqn_app_pl_Cil_ii cert γs1 CS1 hB hN μ hanti hpos hβ0 hβ1
    hγ1 hμC1 hC11 i hr
  have hscale := eqn_app_pl_Cil_ii cert γs2 CS2 hB hN (fun j => c * μ j) hantic hposc
    hβ0 hβ1 hγ2 hμC2 hC12 i hϱ
  have hrow (ℓ : ℕ) :
      lagRowBar cert γs2 CS2 β ℓ B (fun j => c * μ j) (fun _ : Fin N => (1 : ℝ)) i ϱ ϱ =
        lagRowBar cert γs1 CS1 β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i (ϱ / c) (ϱ / c) := by
    convert zr_amp_row cert hB hN hβ0 hβ1 μ hanti hpos hc
      γs1 CS1 γs2 CS2 hγ1 hμC1 hC11 hγ2 hμC2 hC12 hν hνc hν' ℓ i hr using 1 <;>
      field_simp [hc.ne']
  have hdrift : Muon.Drift.kernel (emaW β) νc ν' ϱ (c * μ i) 1 =
      Real.sqrt c * Muon.Drift.kernel (emaW β) ν ν' (ϱ / c) (μ i) 1 := by
    rw [prop_app_pl_branch_iii_kernel (fun j => c * μ j) hβ0 hβ1 hB hN hantic hposc
        hνc hν' hμC2 hC12 hϱ i,
      prop_app_pl_branch_iii_kernel μ hβ0 hβ1 hB hN hanti hpos hν hν'
        hμC1 hC11 hr i,
      zr_amp_dPart hB hN hβ0 hβ1 μ hanti hpos hc i hϱ.le]
  refine ⟨hbase.1, hscale.1, hscale.2.1, hbase.2.1, hdrift, hrow, ?_⟩
  unfold rowVBar
  simp only [hrow]

/-- `lem:app-pl-amplitude`, zero ridge, snapshot `cr-2026-10-23`. Declaration of record for `ϱ = 0`:
`𝔡_i(0;cμ) = √c 𝔡_i(0;μ)`, `C̄_{i,ℓ}(0;cμ) = C̄_{i,ℓ}(0;μ)` and `𝔳_i(0;cμ) = 𝔳_i(0;μ)`, with the
zero-ridge coefficients of `def:app-pl-coefficients` at the admissible constants of each spectrum.
LaTeX, verbatim:

\begin{lemma}[Spectral amplitude]\label{lem:app-pl-amplitude}
Write $\mathfrak d_i(\ridge;\mu)$, $\overline C_{i,\ell}(\ridge;\mu)$ and $\mathfrak v_i(\ridge;\mu)$
for the coefficients of the spectrum $\mu=(\mu_j)$. For every $c>0$ and $\ridge\ge0$,
\[
\mathfrak d_i(\ridge;c\mu)=\sqrt c\,\mathfrak d_i(\ridge/c;\mu),\qquad
\overline C_{i,\ell}(\ridge;c\mu)=\overline C_{i,\ell}(\ridge/c;\mu),\qquad
\mathfrak v_i(\ridge;c\mu)=\mathfrak v_i(\ridge/c;\mu).
\]
\end{lemma}
-/
theorem lem_app_pl_amplitude_ii (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (μ : Fin N → ℝ) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {c : ℝ} (hc : 0 < c)
    (γs1 CS1 : ℝ) (hγ1 : gammaOf N B ≤ γs1) (hμC1 : ∀ i, μ i ≤ CS1) (hC11 : 1 ≤ CS1)
    (γs2 CS2 : ℝ) (hγ2 : gammaOf N B ≤ γs2) (hμC2 : ∀ i, c * μ i ≤ CS2) (hC12 : 1 ≤ CS2)
    (i : Fin N) :
    IntegrableOn (fun u : ℝ => Gfun β B μ i (u ^ 2)) (Ioi (0 : ℝ)) ∧
    IntegrableOn (fun u : ℝ => Gfun β B (fun j => c * μ j) i (u ^ 2)) (Ioi (0 : ℝ)) ∧
    dZero β B (fun j => c * μ j) i = Real.sqrt c * dZero β B μ i ∧
    (∀ ℓ : ℕ, cbarZero cert γs2 CS2 β B (fun j => c * μ j) i ℓ = cbarZero cert γs1 CS1 β B μ i ℓ) ∧
    vZero cert γs2 CS2 β B (fun j => c * μ j) i = vZero cert γs1 CS1 β B μ i := by
  classical
  have hposc : ∀ j, 0 < c * μ j := fun j => mul_pos hc (hpos j)
  have hantic : Antitone (fun j => c * μ j) := fun _ _ hij =>
    mul_le_mul_of_nonneg_left (hanti hij) hc.le
  have hint := prop_app_pl_drift_zero_ii_fin μ hβ0 hβ1 hB hN hanti hpos i
  have hintc := prop_app_pl_drift_zero_ii_fin (fun j => c * μ j) hβ0 hβ1 hB hN
    hantic hposc i
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let νc : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (c * μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) =
      ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hνc : (νc : Measure ℝ) =
      ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (c * μ j) := rfl
  have hν' : (ν' : Measure ℝ) =
      ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := rfl
  have hmul : Tendsto (fun r : ℝ => c * r) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun r : ℝ => c * r) (𝓝 0) (𝓝 (c * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      simpa using h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact mul_pos hc hr
  have hbase := def_app_pl_coefficients_ii cert γs1 CS1 hB hN μ hanti hpos hβ0 hβ1
    hγ1 hμC1 hC11 i
  have hscale := def_app_pl_coefficients_ii cert γs2 CS2 hB hN (fun j => c * μ j)
    hantic hposc hβ0 hβ1 hγ2 hμC2 hC12 i
  have hcbar (ℓ : ℕ) : cbarZero cert γs2 CS2 β B (fun j => c * μ j) i ℓ =
      cbarZero cert γs1 CS1 β B μ i ℓ := by
    have hlimc := (hscale.2.1 ℓ).comp hmul
    have hlimc' := hlimc.congr' (by
      filter_upwards [self_mem_nhdsWithin] with r hr
      change lagRowBar cert γs2 CS2 β ℓ B (fun j => c * μ j)
        (fun _ : Fin N => (1 : ℝ)) i (c * r) (c * r) =
          lagRowBar cert γs1 CS1 β ℓ B μ (fun _ : Fin N => (1 : ℝ)) i r r
      exact zr_amp_row cert hB hN hβ0 hβ1 μ hanti hpos hc
        γs1 CS1 γs2 CS2 hγ1 hμC1 hC11 hγ2 hμC2 hC12 hν hνc hν' ℓ i hr)
    exact tendsto_nhds_unique hlimc' (hbase.2.1 ℓ)
  refine ⟨hint, hintc, zr_amp_dZero hB hN hβ0 hβ1 μ hanti hpos hc i,
    hcbar, ?_⟩
  unfold vZero
  simp only [hcbar]

/-! ## Spectral pieces (`lem:app-pl-pieces`) -/

private lemma zr_plSpec_pos {α c : ℝ} (hc : 0 < c) {N : ℕ} (i : Fin N) :
    0 < plSpec α c N i := by
  unfold plSpec
  exact mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)

private lemma zr_plSpec_anti {α c : ℝ} (hα : 0 < α) (hc : 0 < c) {N : ℕ} :
    Antitone (plSpec α c N) := by
  intro i j hij
  unfold plSpec
  refine mul_le_mul_of_nonneg_left ?_ hc.le
  have hi : 0 < ((i : ℕ) : ℝ) + 1 := by positivity
  have hj : 0 < ((j : ℕ) : ℝ) + 1 := by positivity
  have hle : ((i : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) + 1 := by
    have hcast : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hij
    linarith
  rw [Real.rpow_neg hi.le, Real.rpow_neg hj.le]
  exact inv_anti₀ (Real.rpow_pos_of_pos hi _) (Real.rpow_le_rpow hi.le hle hα.le)

private lemma zr_piece_basic (cert : Muon.External.GaussianOpNorm) {N B : ℕ}
    (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (i : Fin N) (I J : Set ℝ) (hIm : MeasurableSet I)
    (hI : I ⊆ Ioo 0 (gammaOf N B)) (hJm : MeasurableSet J)
    (hJ : J ⊆ Ioo 0 (gammaOf N B)) :
    (∀ ℓ : ℤ, IntegrableOn
      (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (I ×ˢ J)) ∧
      Summable (fun ℓ : ℤ => lagTerm β B μ i I J ℓ) ∧
      0 ≤ vIJ β B μ i I J := by
  classical
  let CSig : ℝ := max 1 (∑ j : Fin N, μ j)
  have hC1 : 1 ≤ CSig := le_max_left _ _
  have hμC : ∀ j, μ j ≤ CSig := by
    intro j
    refine (Finset.single_le_sum (fun k _ => (hpos k).le) (Finset.mem_univ j)).trans ?_
    exact le_max_right _ _
  have hbase (ℓ : ℤ) := prop_app_pl_vol_zero_iii_b cert (gammaOf N B) CSig
    hB hN μ hanti hpos hβ0 hβ1 le_rfl hμC hC1 i ℓ
  let Ω := Ioo 0 (gammaOf N B) ×ˢ Ioo 0 (gammaOf N B)
  have hΩm : MeasurableSet Ω := measurableSet_Ioo.prod measurableSet_Ioo
  have hsub : I ×ˢ J ⊆ Ω := prod_mono hI hJ
  have hint : ∀ ℓ : ℤ, IntegrableOn
      (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (I ×ˢ J) :=
    fun ℓ => (hbase ℓ).2.1.mono_set hsub
  have hprod (ℓ : ℤ) (A C : Set ℝ)
      (hAC : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2)
        (A ×ˢ C)) :
      lagTerm β B μ i A C ℓ =
        ∫ p in A ×ˢ C, lagIntegrand β B μ i ℓ p.1 p.2 := by
    unfold lagTerm
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    exact (setIntegral_prod (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2)
      (by simpa only [IntegrableOn, ← Measure.volume_eq_prod] using hAC)).symm
  have hnn : ∀ ℓ : ℤ, 0 ≤ lagTerm β B μ i I J ℓ := by
    intro ℓ
    rw [hprod ℓ I J (hint ℓ)]
    exact setIntegral_nonneg (hIm.prod hJm) fun p hp =>
      (hbase ℓ).1 p.1 (hI hp.1) p.2 (hJ hp.2)
  have hle : ∀ ℓ : ℤ,
      lagTerm β B μ i I J ℓ ≤
        lagTerm β B μ i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ := by
    intro ℓ
    rw [hprod ℓ I J (hint ℓ), hprod ℓ _ _ (hbase ℓ).2.1]
    exact setIntegral_mono_set (hbase ℓ).2.1
      (ae_restrict_of_forall_mem hΩm fun p hp => (hbase ℓ).1 p.1 hp.1 p.2 hp.2)
      (Eventually.of_forall hsub)
  have hc := prop_app_pl_vol_zero_iii_c cert (gammaOf N B) CSig hB hN μ hanti hpos
    hβ0 hβ1 le_rfl hμC hC1 i
  have hfull_eq (ℓ : ℤ) :
      lagTerm β B μ i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ =
        Real.pi ^ 2 * cbarZero cert (gammaOf N B) CSig β B μ i ℓ.natAbs := by
    rw [(hbase ℓ).2.2]
    unfold CbarPart
    field_simp [Real.pi_ne_zero]
  have hfull : Summable (fun ℓ : ℤ =>
      lagTerm β B μ i (Ioo 0 (gammaOf N B)) (Ioo 0 (gammaOf N B)) ℓ) := by
    simpa only [hfull_eq] using hc.2.1.summable.mul_left (Real.pi ^ 2)
  have hsum := Summable.of_nonneg_of_le hnn hle hfull
  refine ⟨hint, hsum, ?_⟩
  unfold vIJ
  exact mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (tsum_nonneg hnn)

private lemma zr_quadratic_cs {A D C : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hq : ∀ a b : ℝ, 0 ≤ a ^ 2 * A + 2 * a * b * D + b ^ 2 * C) :
    D ≤ Real.sqrt (A * C) := by
  have hdisc : D ^ 2 ≤ A * C := by
    have h₁ := hq C (-D)
    have h₂ := hq (-D) A
    have h₃ := hq 1 (-1)
    rcases hA.eq_or_lt with hA0 | hApos
    · rcases hC.eq_or_lt with hC0 | hCpos
      · rw [← hA0, ← hC0] at h₃ ⊢
        nlinarith
      · rw [← hA0] at h₁ ⊢
        nlinarith [sq_nonneg D]
    · rw [show A * C = C * A by ring]
      nlinarith [sq_nonneg D]
  calc
    D = Real.sqrt (D ^ 2) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hD]
    _ ≤ Real.sqrt (A * C) := Real.sqrt_le_sqrt hdisc

private lemma zr_lag_swap_all (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ)
    (i : Fin N) (ℓ : ℤ) (x y : ℝ) :
    lagIntegrand β B μ i ℓ x y = lagIntegrand β B μ i (-ℓ) y x := by
  rcases lt_trichotomy ℓ 0 with hneg | hzero | hpos
  · obtain ⟨n, hn, rfl⟩ : ∃ n : ℕ, 0 < n ∧ ℓ = -(n : ℤ) :=
      ⟨ℓ.natAbs, by omega, by omega⟩
    simpa only [neg_neg] using zr_lag_neg β B μ i n hn x y
  · subst ℓ
    have hD : DLagNat β (Qm β x) (Qm β y) 0 =
        DLagNat β (Qm β y) (Qm β x) 0 := by
      unfold DLagNat
      apply tsum_congr
      intro a
      apply integral_congr_ae
      filter_upwards with g
      simp only [pow_zero, one_mul]
      rw [mul_comm (Qm β x) (Qm β y)]
      ring
    have hM : MLagNat β (Qm β x) (Qm β y) 0 =
        MLagNat β (Qm β y) (Qm β x) 0 := by
      unfold MLagNat
      apply tsum_congr
      intro a
      apply integral_congr_ae
      filter_upwards with g
      norm_num
      ring
    unfold lagIntegrand lagNumer deltaN DLag MLag TNpart
    simp only [neg_zero, Int.reduceLE, ↓reduceIte, Int.toNat_zero]
    have hT : ∑ j : Fin N, partF B μ j x * partF B μ j y =
        ∑ j : Fin N, partF B μ j y * partF B μ j x :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hT, hD, hM, mul_comm x y, mul_comm (Wpart β B μ i x)]
    ring
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hn : 0 < n := by omega
    exact (zr_lag_neg β B μ i n hn y x).symm

private lemma zr_lagTerm_swap (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ)
    (i : Fin N) (I J : Set ℝ) (ℓ : ℤ)
    (hint : IntegrableOn
      (fun p : ℝ × ℝ => lagIntegrand β B μ i (-ℓ) p.1 p.2) (I ×ˢ J)) :
    lagTerm β B μ i J I ℓ = lagTerm β B μ i I J (-ℓ) := by
  have hint' := hint
  unfold IntegrableOn at hint'
  rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ,
    ← Measure.prod_restrict] at hint'
  have hsw : Integrable
      (fun p : ℝ × ℝ => lagIntegrand β B μ i (-ℓ) p.2 p.1)
      ((volume.restrict J).prod (volume.restrict I)) := hint'.swap
  unfold lagTerm
  calc
    (∫ x in J, ∫ y in I, lagIntegrand β B μ i ℓ x y) =
        ∫ x in J, ∫ y in I, lagIntegrand β B μ i (-ℓ) y x := by
          apply integral_congr_ae
          filter_upwards with x
          apply integral_congr_ae
          filter_upwards with y
          exact zr_lag_swap_all β B μ i ℓ x y
    _ = ∫ y in I, ∫ x in J, lagIntegrand β B μ i (-ℓ) y x :=
      (integral_integral_swap
        (f := fun a b => lagIntegrand β B μ i (-ℓ) b a) hsw)

private lemma zr_vIJ_swap (cert : Muon.External.GaussianOpNorm) {N B : ℕ}
    (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hanti : Antitone μ)
    (hpos : ∀ i, 0 < μ i) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (i : Fin N) (I J : Set ℝ) (hIm : MeasurableSet I)
    (hI : I ⊆ Ioo 0 (gammaOf N B)) (hJm : MeasurableSet J)
    (hJ : J ⊆ Ioo 0 (gammaOf N B)) :
    vIJ β B μ i J I = vIJ β B μ i I J := by
  have hb := zr_piece_basic cert hB hN μ hanti hpos hβ0 hβ1 i I J hIm hI hJm hJ
  unfold vIJ
  congr 1
  calc
    (∑' ℓ : ℤ, lagTerm β B μ i J I ℓ) =
        ∑' ℓ : ℤ, lagTerm β B μ i I J (-ℓ) := by
          apply tsum_congr
          intro ℓ
          exact zr_lagTerm_swap β B μ i I J ℓ (hb.1 (-ℓ))
    _ = ∑' ℓ : ℤ, lagTerm β B μ i I J ℓ := by
      simpa using (Equiv.tsum_eq (Equiv.neg ℤ)
        (fun ℓ : ℤ => lagTerm β B μ i I J ℓ)).symm

private lemma zr_piece_coordinate {N B : ℕ} {β : ℝ}
    (μ : Fin N → ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hB : 0 < B) (hN : 0 < N) (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {p q : ℝ} (hp : p ∈ Ioo 0 (gammaOf N B))
    (hq : q ∈ Ioo 0 (gammaOf N B)) (hpq : p ≤ q) :
    0 < Real.sqrt (sN β B μ q) ∧
    Real.sqrt (sN β B μ q) ≤ Real.sqrt (sN β B μ p) ∧
    ∀ g : ℝ → ℝ,
      (∫ u in Real.sqrt (sN β B μ q)..Real.sqrt (sN β B μ p), g u) =
        ∫ m in Icc p q, (thetaN β B μ m * Real.sqrt (sN β B μ m) / 2) *
          g (Real.sqrt (sN β B μ m)) := by
  have hb := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  obtain ⟨hd, hi, -, ha⟩ := zr_cov_data μ hβ0 hβ1 hB hN hanti hpos
  have hsub : Icc p q ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
    ⟨hp.1.trans_le hx.1, hx.2.trans_lt hq.2⟩
  have hm : AntitoneOn (fun x => Real.sqrt (sN β B μ x)) (Icc p q) := by
    intro x hx y hy hxy
    exact Real.sqrt_le_sqrt (hb.2.1.antitoneOn (hsub hx) (hsub hy) hxy)
  have hc : ContinuousOn (fun x => Real.sqrt (sN β B μ x)) (Icc p q) :=
    fun x hx => (hd x (hsub hx)).continuousAt.continuousWithinAt
  have himg := hc.image_Icc_of_antitoneOn hpq hm
  have hle := hm (left_mem_Icc.mpr hpq) (right_mem_Icc.mpr hpq) hpq
  refine ⟨Real.sqrt_pos.mpr (hb.2.2.1.mapsTo hq), hle, fun g => ?_⟩
  rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc, ← himg]
  rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun x hx => (hd x (hsub hx)).hasDerivWithinAt) (hi.mono hsub)]
  exact setIntegral_congr_fun measurableSet_Icc fun x hx => by
    rw [ha x (hsub hx), smul_eq_mul]

private lemma zr_piece_kernel (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (n : ℕ) {m₁ m₂ : ℝ}
    (hm₁ : m₁ ∈ Ioo 0 (gammaOf N B)) (hm₂ : m₂ ∈ Ioo 0 (gammaOf N B)) :
    lagIntegrand β B μ i (n : ℤ) m₁ m₂ =
      4 * ((thetaN β B μ m₁ * Real.sqrt (sN β B μ m₁) / 2) *
        (thetaN β B μ m₂ * Real.sqrt (sN β B μ m₂) / 2) *
        ((B : ℝ) * lagResp cert γstar CSig β n B μ (fun _ : Fin N => (1 : ℝ))
          (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
          (iotaF ((Real.sqrt (sN β B μ m₁)) ^ 2))
          (iotaF ((Real.sqrt (sN β B μ m₂)) ^ 2)))) := by
  classical
  let ν : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j), by
      constructor
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  let ν' : FiniteMeasure ℝ :=
    ⟨ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ), by
      constructor
      simp [Measure.smul_apply]⟩
  have hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ j, Measure.dirac (μ j) := rfl
  have hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := rfl
  have hb := prop_app_pl_branch_i μ hβ0 hβ1 hB hN hanti hpos
  have hs1 := hb.2.2.1.mapsTo hm₁
  have hs2 := hb.2.2.1.mapsTo hm₂
  rw [zr_pw μ hβ0 hβ1 hB hN hanti hpos hμC hC1 hν hν' n i hm₁ hm₂]
  rw [Real.sq_sqrt (le_of_lt hs1), Real.sq_sqrt (le_of_lt hs2),
    prop_app_pl_response_ii cert γstar CSig hB hN μ hpos hβ0.le hβ1 hγ hμC hC1
      hν hν' n hs1 hs2 i, Real.sqrt_mul (le_of_lt hs1)]
  ring

private lemma zr_piece_filter (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Muon.Volatility.IsOddBddLip (fun x => (2 / Real.pi) * ∫ y in a..b, iotaF (y ^ 2) x) := by
  simpa only [zero_add] using zrb_F_obl (ϱ := 0) (s0 := a ^ 2)
    (sq_pos_of_pos ha) hab (fun y hy => by nlinarith [hy.1])

private lemma zr_piece_lag (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    (i : Fin N) (n : ℕ) {p q r s : ℝ}
    (hp : p ∈ Ioo 0 (gammaOf N B)) (hq : q ∈ Ioo 0 (gammaOf N B)) (hpq : p ≤ q)
    (hr : r ∈ Ioo 0 (gammaOf N B)) (hs : s ∈ Ioo 0 (gammaOf N B)) (hrs : r ≤ s) :
    (B : ℝ) * lagResp cert γstar CSig β n B μ (fun _ : Fin N => (1 : ℝ))
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
      (fun x => (2 / Real.pi) * ∫ y in Real.sqrt (sN β B μ q)..Real.sqrt (sN β B μ p),
        iotaF (y ^ 2) x)
      (fun x => (2 / Real.pi) * ∫ y in Real.sqrt (sN β B μ s)..Real.sqrt (sN β B μ r),
        iotaF (y ^ 2) x) =
      (Real.pi ^ 2)⁻¹ * lagTerm β B μ i (Icc p q) (Icc r s) (n : ℤ) := by
  classical
  let R : ℕ → (ℝ → ℝ) → (ℝ → ℝ) → ℝ := fun ℓ f g =>
    (B : ℝ) * lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
      (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g
  obtain ⟨-, -, -, h1, h2, h3⟩ := zr_Rprops cert γstar CSig hB hN μ hpos hβ0 hβ1
    hγ hμC hC1 i R (fun _ _ _ => rfl)
  obtain ⟨ha, hab, hchangeI⟩ := zr_piece_coordinate μ hβ0 hβ1 hB hN hanti hpos hp hq hpq
  obtain ⟨hc, hcd, hchangeJ⟩ := zr_piece_coordinate μ hβ0 hβ1 hB hN hanti hpos hr hs hrs
  have hCb : 0 ≤ (B : ℝ) * γstar := by
    have : 0 ≤ gammaOf N B := by unfold gammaOf; positivity
    have : 0 ≤ γstar := this.trans hγ
    positivity
  have hH := zrb_H2 (R n) ((B : ℝ) * γstar) hCb (h1 n) (h2 n) (h3 n)
    (ϱ := 0) (ϱ' := 0) (sq_pos_of_pos ha) hab
    (fun y hy => by nlinarith [hy.1]) (sq_pos_of_pos hc) hcd
    (fun y hy => by nlinarith [hy.1])
  simp only [zero_add, intervalIntegral.integral_const_mul] at hH
  change R n _ _ = _
  rw [hH, hchangeI]
  have hsubI : Icc p q ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
    ⟨hp.1.trans_le hx.1, hx.2.trans_lt hq.2⟩
  have hsubJ : Icc r s ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
    ⟨hr.1.trans_le hx.1, hx.2.trans_lt hs.2⟩
  have heq : lagTerm β B μ i (Icc p q) (Icc r s) (n : ℤ) =
      4 * ∫ x in Icc p q, (thetaN β B μ x * Real.sqrt (sN β B μ x) / 2) *
        ∫ y in Real.sqrt (sN β B μ s)..Real.sqrt (sN β B μ r),
          R n (iotaF ((Real.sqrt (sN β B μ x)) ^ 2)) (iotaF (y ^ 2)) := by
    unfold lagTerm
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro x hx
    dsimp only
    rw [hchangeJ, ← integral_const_mul, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro y hy
    rw [zr_piece_kernel cert γstar CSig hB hN μ hanti hpos hβ0 hβ1 hγ hμC hC1
      i n (hsubI hx) (hsubJ hy)]
    dsimp [R]
    ring
  rw [heq]
  ring

private lemma zr_piece_gamma (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} {β : ℝ} (μ : Fin N → ℝ) (i : Fin N) (I J : Set ℝ) (f g : ℝ → ℝ)
    (hint : ∀ ℓ : ℤ, IntegrableOn
      (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (I ×ˢ J))
    (hsum : Summable (fun ℓ : ℤ => lagTerm β B μ i I J ℓ))
    (hfg : ∀ n : ℕ, (B : ℝ) * lagResp cert γstar CSig β n B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g =
        (Real.pi ^ 2)⁻¹ * lagTerm β B μ i I J (n : ℤ))
    (hgf : ∀ n : ℕ, (B : ℝ) * lagResp cert γstar CSig β n B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) g f =
        (Real.pi ^ 2)⁻¹ * lagTerm β B μ i J I (n : ℤ)) :
    (B : ℝ) * Muon.Volatility.lagGammaGen cert γstar CSig β B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g =
        vIJ β B μ i I J := by
  have hspos : Summable (fun n : ℕ => lagTerm β B μ i I J ((n : ℤ) + 1)) :=
    hsum.comp_injective (fun _ _ h => by omega)
  have hsneg : Summable (fun n : ℕ => lagTerm β B μ i I J (-((n : ℤ) + 1))) :=
    hsum.comp_injective (fun _ _ h => by omega)
  unfold Muon.Volatility.lagGammaGen vIJ
  rw [mul_add, ← tsum_mul_left]
  simp_rw [mul_add, hfg, hgf,
    zr_lagTerm_swap β B μ i I J _ (hint _), Nat.cast_add, Nat.cast_one]
  rw [(hspos.mul_left _).tsum_add (hsneg.mul_left _),
    tsum_mul_left, tsum_mul_left, tsum_of_add_one_of_neg_add_one hspos hsneg]
  simp only [Nat.cast_zero]
  ring

private lemma zr_piece_compact (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin N) {p q r s : ℝ}
    (hp : p ∈ Ioo 0 (gammaOf N B)) (hq : q ∈ Ioo 0 (gammaOf N B)) (hpq : p ≤ q)
    (hr : r ∈ Ioo 0 (gammaOf N B)) (hs : s ∈ Ioo 0 (gammaOf N B)) (hrs : r ≤ s) :
    vIJ β B μ i (Icc p q) (Icc r s) ≤
      Real.sqrt (vIJ β B μ i (Icc p q) (Icc p q) * vIJ β B μ i (Icc r s) (Icc r s)) := by
  classical
  let CSig : ℝ := max 1 (∑ j : Fin N, μ j)
  have hC1 : 1 ≤ CSig := le_max_left _ _
  have hμC : ∀ j, μ j ≤ CSig := by
    intro j
    exact (Finset.single_le_sum (fun k _ => (hpos k).le) (Finset.mem_univ j)).trans
      (le_max_right _ _)
  obtain ⟨Fp, S, hβ, hμ, hlam, hS, -, -⟩ :=
    zr_setup' hB μ hpos hβ0 hβ1 le_rfl hμC hC1 i
  let F : ℝ → ℝ → ℝ → ℝ := fun a b x =>
    (2 / Real.pi) * ∫ y in Real.sqrt (sN β B μ b)..Real.sqrt (sN β B μ a), iotaF (y ^ 2) x
  let Γ : (ℝ → ℝ) → (ℝ → ℝ) → ℝ := fun f g =>
    (B : ℝ) * Muon.Volatility.lagGammaGen cert (gammaOf N B) CSig β B μ
      (fun _ : Fin N => (1 : ℝ)) (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ)) f g
  have hFF : ∀ a b : ℝ, a ∈ Ioo 0 (gammaOf N B) → b ∈ Ioo 0 (gammaOf N B) → a ≤ b →
      Muon.Volatility.IsOddBddLip (F a b) := by
    intro a b ha hb hab
    obtain ⟨ha', hab', -⟩ := zr_piece_coordinate μ hβ0 hβ1 hB hN hanti hpos ha hb hab
    exact zr_piece_filter _ _ ha' hab'
  have hbridge : ∀ a b c d : ℝ,
      a ∈ Ioo 0 (gammaOf N B) → b ∈ Ioo 0 (gammaOf N B) → a ≤ b →
      c ∈ Ioo 0 (gammaOf N B) → d ∈ Ioo 0 (gammaOf N B) → c ≤ d →
      Γ (F a b) (F c d) = vIJ β B μ i (Icc a b) (Icc c d) := by
    intro a b c d ha hb hab hc hd hcd
    have hI : Icc a b ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
      ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
    have hJ : Icc c d ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
      ⟨hc.1.trans_le hx.1, hx.2.trans_lt hd.2⟩
    obtain ⟨hint, hsum, -⟩ := zr_piece_basic cert hB hN μ hanti hpos hβ0 hβ1 i
      (Icc a b) (Icc c d) measurableSet_Icc hI measurableSet_Icc hJ
    exact zr_piece_gamma cert (gammaOf N B) CSig μ i _ _ _ _ hint hsum
      (fun n => zr_piece_lag cert (gammaOf N B) CSig hB hN μ hanti hpos hβ0 hβ1
        le_rfl hμC hC1 i n ha hb hab hc hd hcd)
      (fun n => zr_piece_lag cert (gammaOf N B) CSig hB hN μ hanti hpos hβ0 hβ1
        le_rfl hμC hC1 i n hc hd hcd ha hb hab)
  have hI : Icc p q ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
    ⟨hp.1.trans_le hx.1, hx.2.trans_lt hq.2⟩
  have hJ : Icc r s ⊆ Ioo 0 (gammaOf N B) := fun x hx =>
    ⟨hr.1.trans_le hx.1, hx.2.trans_lt hs.2⟩
  have hnn (I J : Set ℝ) (hIm : MeasurableSet I) (hJm : MeasurableSet J)
      (hI : I ⊆ Ioo 0 (gammaOf N B)) (hJ : J ⊆ Ioo 0 (gammaOf N B)) :=
    (zr_piece_basic cert hB hN μ hanti hpos hβ0 hβ1 i I J hIm hI hJm hJ).2.2
  apply zr_quadratic_cs (hnn _ _ measurableSet_Icc measurableSet_Icc hI hI)
    (hnn _ _ measurableSet_Icc measurableSet_Icc hI hJ)
    (hnn _ _ measurableSet_Icc measurableSet_Icc hJ hJ)
  intro a b
  have hf := hFF p q hp hq hpq
  have hg := hFF r s hr hs hrs
  have hz : Muon.Volatility.IsOddBddLip (fun _ : ℝ => (0 : ℝ)) := by
    exact ⟨by simp, ⟨0, by simp⟩, ⟨0, by simp⟩⟩
  have haf : Muon.Volatility.IsOddBddLip (fun x => a * F p q x) := by
    simpa only [zero_add] using zrb_obl_add a hz hf
  have hmix := zrb_obl_add b haf hg
  have hnonneg := (Muon.Volatility.lag_gamma_generic_nonneg cert (gammaOf N B) CSig
    Fp S hS hC1 _ hmix (Pi.single i (1 : ℝ)) (fun _ => (1 : ℝ))
    (fun j => by simp [Pi.single_apply]; split_ifs <;> norm_num) (fun _ => zero_le_one)).2
  have hquad := Muon.Volatility.lag_gamma_generic_quadratic cert (gammaOf N B) CSig
    Fp S hS hC1 (F p q) (F r s) hf hg a b (Pi.single i (1 : ℝ)) (fun _ => (1 : ℝ))
  rw [hquad] at hnonneg
  simp only [hβ, hμ, hlam] at hnonneg
  have hscaled : 0 ≤
      a ^ 2 * Γ (F p q) (F p q) + a * b * (Γ (F p q) (F r s) + Γ (F r s) (F p q)) +
        b ^ 2 * Γ (F r s) (F r s) := by
    convert mul_nonneg (show (0 : ℝ) ≤ B by positivity) hnonneg using 1 <;>
      dsimp [Γ] <;> ring
  rw [hbridge p q p q hp hq hpq hp hq hpq,
    hbridge p q r s hp hq hpq hr hs hrs, hbridge r s p q hr hs hrs hp hq hpq,
    hbridge r s r s hr hs hrs hr hs hrs,
    zr_vIJ_swap cert hB hN μ hanti hpos hβ0 hβ1 i _ _ measurableSet_Icc hI
      measurableSet_Icc hJ] at hscaled
  nlinarith only [hscaled]

private lemma zr_piece_ae (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (i : Fin N)
    {I I' J J' : Set ℝ} (hI : I =ᵐ[volume] I') (hJ : J =ᵐ[volume] J') :
    vIJ β B μ i I J = vIJ β B μ i I' J' := by
  unfold vIJ
  congr 1
  apply tsum_congr
  intro ℓ
  unfold lagTerm
  rw [setIntegral_congr_set hI]
  apply integral_congr_ae
  filter_upwards with x
  exact setIntegral_congr_set hJ

private lemma zr_piece_interval {γ : ℝ} {I : Set ℝ}
    (hIo : I.OrdConnected) (hI : I ⊆ Ioo 0 γ) (hne : I.Nonempty) :
    ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ γ ∧ I =ᵐ[volume] Ioo a b := by
  have hb : BddBelow I := ⟨0, fun x hx => (hI hx).1.le⟩
  have ha : BddAbove I := ⟨γ, fun x hx => (hI hx).2.le⟩
  have hl : Ioo (sInf I) (sSup I) ⊆ I :=
    (show IsConnected I from ⟨hne, hIo.isPreconnected⟩).Ioo_csInf_csSup_subset hb ha
  have hu : I ⊆ Icc (sInf I) (sSup I) := subset_Icc_csInf_csSup hb ha
  refine ⟨sInf I, sSup I, le_csInf hne (fun x hx => (hI hx).1.le),
    csInf_le_csSup hne hb ha, csSup_le hne (fun x hx => (hI hx).2.le), ?_⟩
  filter_upwards [Ioo_ae_eq_Icc (μ := (volume : Measure ℝ)) (a := sInf I) (b := sSup I)] with x hx
  apply propext
  constructor
  · intro hxI
    rw [hx]
    exact hu hxI
  · exact fun hxI => hl hxI

private lemma zr_piece_exhaust {a b : ℝ} (hab : a < b) :
    ∃ p q : ℕ → ℝ, (∀ k, p k ∈ Ioo a b) ∧ (∀ k, q k ∈ Ioo a b) ∧
      (∀ k, p k ≤ q k) ∧ Monotone (fun k => Icc (p k) (q k)) ∧
      (⋃ k, Icc (p k) (q k)) = Ioo a b := by
  obtain ⟨p, q, hp, hq, hpm, hqm, hpq, hplim, hqlim⟩ :=
    exists_seq_strictAnti_strictMono_tendsto hab
  refine ⟨p, q, hpm, hqm, fun k => (hpq k k).le,
    fun k l hkl => Icc_subset_Icc (hp.antitone hkl) (hq.monotone hkl), ?_⟩
  apply Subset.antisymm
  · intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨(hpm k).1.trans_le hk.1, hk.2.trans_lt (hqm k).2⟩
  · intro x hx
    have hpx : ∀ᶠ k in atTop, p k < x := hplim.eventually (eventually_lt_nhds hx.1)
    have hqx : ∀ᶠ k in atTop, x < q k := hqlim.eventually (eventually_gt_nhds hx.2)
    obtain ⟨k, hk, hk'⟩ := (hpx.and hqx).exists
    exact mem_iUnion.mpr ⟨k, hk.le, hk'.le⟩

private lemma zr_piece_tendsto (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin N)
    (I J : Set ℝ) (hIm : MeasurableSet I) (hJm : MeasurableSet J)
    (hI : I ⊆ Ioo 0 (gammaOf N B)) (hJ : J ⊆ Ioo 0 (gammaOf N B))
    (K L : ℕ → Set ℝ) (hKm : ∀ k, MeasurableSet (K k)) (hLm : ∀ k, MeasurableSet (L k))
    (hK : Monotone K) (hL : Monotone L) (hKU : (⋃ k, K k) = I) (hLU : (⋃ k, L k) = J) :
    Tendsto (fun k => vIJ β B μ i (K k) (L k)) atTop (𝓝 (vIJ β B μ i I J)) := by
  have hKI : ∀ k, K k ⊆ I := fun k => hKU ▸ subset_iUnion K k
  have hLJ : ∀ k, L k ⊆ J := fun k => hLU ▸ subset_iUnion L k
  have hcover : (⋃ k, K k ×ˢ L k) = I ×ˢ J := by
    rw [iUnion_prod_of_monotone hK hL, hKU, hLU]
  have hbasic := zr_piece_basic cert hB hN μ hanti hpos hβ0 hβ1 i I J hIm hI hJm hJ
  have hprod (ℓ : ℤ) (A C : Set ℝ)
      (hint : IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (A ×ˢ C)) :
      lagTerm β B μ i A C ℓ = ∫ p in A ×ˢ C, lagIntegrand β B μ i ℓ p.1 p.2 := by
    unfold lagTerm
    rw [show (volume : Measure (ℝ × ℝ)) = volume.prod volume from Measure.volume_eq_prod ℝ ℝ]
    exact (setIntegral_prod
      (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2)
      (by simpa only [IntegrableOn, ← Measure.volume_eq_prod] using hint)).symm
  have hkint (k : ℕ) (ℓ : ℤ) := (hbasic.1 ℓ).mono_set (prod_mono (hKI k) (hLJ k))
  have hlim (ℓ : ℤ) : Tendsto (fun k => lagTerm β B μ i (K k) (L k) ℓ) atTop
      (𝓝 (lagTerm β B μ i I J ℓ)) := by
    simp_rw [hprod ℓ I J (hbasic.1 ℓ), hprod ℓ _ _ (hkint _ ℓ)]
    have ht := tendsto_setIntegral_of_monotone (fun k => (hKm k).prod (hLm k))
      (fun k l hkl => prod_mono (hK hkl) (hL hkl))
      (show IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2)
        (⋃ k, K k ×ˢ L k) from hcover.symm ▸ hbasic.1 ℓ)
    simpa only [hcover] using ht
  let CSig : ℝ := max 1 (∑ j : Fin N, μ j)
  have hC1 : 1 ≤ CSig := le_max_left _ _
  have hμC : ∀ j, μ j ≤ CSig := fun j =>
    (Finset.single_le_sum (fun k _ => (hpos k).le) (Finset.mem_univ j)).trans (le_max_right _ _)
  have hnn (ℓ : ℤ) (x y : ℝ) (hx : x ∈ I) (hy : y ∈ J) :
      0 ≤ lagIntegrand β B μ i ℓ x y :=
    (prop_app_pl_vol_zero_iii_b cert (gammaOf N B) CSig hB hN μ hanti hpos
      hβ0 hβ1 le_rfl hμC hC1 i ℓ).1 x (hI hx) y (hJ hy)
  have hbound (k : ℕ) (ℓ : ℤ) :
      ‖lagTerm β B μ i (K k) (L k) ℓ‖ ≤ lagTerm β B μ i I J ℓ := by
    rw [hprod ℓ _ _ (hkint k ℓ), hprod ℓ _ _ (hbasic.1 ℓ), Real.norm_eq_abs,
      abs_of_nonneg (setIntegral_nonneg ((hKm k).prod (hLm k))
        (fun p hp => hnn ℓ p.1 p.2 (hKI k hp.1) (hLJ k hp.2)))]
    exact setIntegral_mono_set (hbasic.1 ℓ)
      (ae_restrict_of_forall_mem (hIm.prod hJm) fun p hp => hnn ℓ p.1 p.2 hp.1 hp.2)
      (Eventually.of_forall (prod_mono (hKI k) (hLJ k)))
  exact (tendsto_tsum_of_dominated_convergence hbasic.2.1 hlim
    (Eventually.of_forall hbound)).const_mul ((Real.pi ^ 2)⁻¹)

private lemma zr_piece_open (cert : Muon.External.GaussianOpNorm)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin N) {a b c d : ℝ}
    (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ gammaOf N B)
    (hc : 0 ≤ c) (hcd : c < d) (hd : d ≤ gammaOf N B) :
    vIJ β B μ i (Ioo a b) (Ioo c d) ≤
      Real.sqrt (vIJ β B μ i (Ioo a b) (Ioo a b) * vIJ β B μ i (Ioo c d) (Ioo c d)) := by
  obtain ⟨p, q, hpm, hqm, hpq, hK, hKU⟩ := zr_piece_exhaust hab
  obtain ⟨r, s, hrm, hsm, hrs, hL, hLU⟩ := zr_piece_exhaust hcd
  have hI : Ioo a b ⊆ Ioo 0 (gammaOf N B) := Ioo_subset_Ioo ha hb
  have hJ : Ioo c d ⊆ Ioo 0 (gammaOf N B) := Ioo_subset_Ioo hc hd
  have hIJ := zr_piece_tendsto cert hB hN μ hanti hpos hβ0 hβ1 i _ _
    measurableSet_Ioo measurableSet_Ioo hI hJ _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) hK hL hKU hLU
  have hII := zr_piece_tendsto cert hB hN μ hanti hpos hβ0 hβ1 i _ _
    measurableSet_Ioo measurableSet_Ioo hI hI _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) hK hK hKU hKU
  have hJJ := zr_piece_tendsto cert hB hN μ hanti hpos hβ0 hβ1 i _ _
    measurableSet_Ioo measurableSet_Ioo hJ hJ _ _
    (fun _ => measurableSet_Icc) (fun _ => measurableSet_Icc) hL hL hLU hLU
  exact le_of_tendsto_of_tendsto' hIJ (Real.continuous_sqrt.continuousAt.tendsto.comp (hII.mul hJJ))
    (fun k => zr_piece_compact cert hB hN μ hanti hpos hβ0 hβ1 i
      (hI (hpm k)) (hI (hqm k)) (hpq k) (hJ (hrm k)) (hJ (hsm k)) (hrs k))

/-- `lem:app-pl-pieces`, snapshot `cr-2026-10-23`. Declaration of record: for intervals `I, J ⊆ (0,γ)`
(`Set.OrdConnected`), `0 ≤ 𝔳_i[I,J] ≤ (𝔳_i[I,I] 𝔳_i[J,J])^{1/2}`. Side conditions carried in the conclusion:
for every `ℓ ∈ ℤ` the lag integrand is integrable on `I × J`, and the lag series over `ℤ` is summable (so
that `vIJ` is the sum it denotes). This is the hypothesis `volHPSD` of `Muon.PowerLaw.VolMeso` for each
row. LaTeX, verbatim:

\begin{lemma}[Spectral pieces]\label{lem:app-pl-pieces}
For intervals $I,J\subset(0,\gamma)$, $0\le\mathfrak v_i[I,J]\le\big(\mathfrak v_i[I,I]\,\mathfrak v_i[J,J]\big)^{1/2}$.
\end{lemma}
-/
theorem lem_app_pl_pieces (cert : Muon.External.GaussianOpNorm) {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ)
    (hanti : Antitone μ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (i : Fin N) :
    ∀ I J : Set ℝ, I.OrdConnected → I ⊆ Ioo 0 (gammaOf N B) →
      J.OrdConnected → J ⊆ Ioo 0 (gammaOf N B) →
      (∀ ℓ : ℤ, IntegrableOn (fun p : ℝ × ℝ => lagIntegrand β B μ i ℓ p.1 p.2) (I ×ˢ J)) ∧
      Summable (fun ℓ : ℤ => lagTerm β B μ i I J ℓ) ∧
      0 ≤ vIJ β B μ i I J ∧
      vIJ β B μ i I J ≤ Real.sqrt (vIJ β B μ i I I * vIJ β B μ i J J) := by
  intro I J hIo hI hJo hJ
  obtain ⟨hint, hsum, hnn⟩ := zr_piece_basic cert hB hN μ hanti hpos hβ0 hβ1 i I J
    hIo.measurableSet hI hJo.measurableSet hJ
  refine ⟨hint, hsum, hnn, ?_⟩
  rcases I.eq_empty_or_nonempty with rfl | hIne
  · simp [vIJ, lagTerm]
  rcases J.eq_empty_or_nonempty with rfl | hJne
  · simp [vIJ, lagTerm]
  obtain ⟨a, b, ha, hab, hb, hIa⟩ := zr_piece_interval hIo hI hIne
  obtain ⟨c, d, hc, hcd, hd, hJa⟩ := zr_piece_interval hJo hJ hJne
  rw [zr_piece_ae β B μ i hIa hJa, zr_piece_ae β B μ i hIa hIa,
    zr_piece_ae β B μ i hJa hJa]
  rcases hab.eq_or_lt with hab | hab
  · subst b
    simp [vIJ, lagTerm]
  rcases hcd.eq_or_lt with hcd | hcd
  · subst d
    simp [vIJ, lagTerm]
  exact zr_piece_open cert hB hN μ hanti hpos hβ0 hβ1 i ha hab hb hc hcd hd

/-! ## Discharges of the part-form hypotheses (card §5, L-G.13 notes) -/

/-- Discharge of the hypothesis `hBound` of the part-form volatility statements (`volHBound`,
`0 ≤ C̄_{i,ℓ}(0) ≤ 1` for every row and every lag, source l.2260). Proof: `prop_app_pl_vol_zero_iii_b`
(bridge), `prop_app_pl_vol_zero_iii_c` (nonnegativity), `lem_app_pl_two_ridge_ii` (bound 1). Statement is
over the regime sequences `R`; the constants `γ⋆, C_Σ` are chosen admissibly inside the proof. -/
theorem prop_app_pl_vol_zero_hBound (cert : Muon.External.GaussianOpNorm) {α β : ℝ}
    {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c) :
    volHBound α β N B c := by
  intro n i ℓ
  let μ : Fin (N n) → ℝ := plSpec α (c n) (N n)
  let γstar : ℝ := gammaOf (N n) (B n)
  let CSig : ℝ := max (μ ⟨0, R.hNpos n⟩) 1
  have hanti : Antitone μ := by
    simpa only [μ] using zr_plSpec_anti R.hα (R.hcpos n)
  have hpos : ∀ j, 0 < μ j := by
    intro j
    simpa only [μ] using zr_plSpec_pos (R.hcpos n) j
  have hγ : gammaOf (N n) (B n) ≤ γstar := le_rfl
  have hμC : ∀ j, μ j ≤ CSig := by
    intro j
    have hj : (⟨0, R.hNpos n⟩ : Fin (N n)) ≤ j := Nat.zero_le j.val
    exact (hanti hj).trans (le_max_left _ _)
  have hC1 : 1 ≤ CSig := le_max_right _ _
  have hz0 : 0 < plZ1 β (B n) μ :=
    (prop_app_pl_branch_i μ R.hβ0 R.hβ1 (R.hBpos n) (R.hNpos n) hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ (R.hBpos n) (R.hNpos n) hpos).1.mapsTo
        (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hbridge := (prop_app_pl_vol_zero_iii_b cert γstar CSig
    (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i ℓ).2.2
  change 0 ≤ CbarPart β (B n) μ i ℓ ∧ CbarPart β (B n) μ i ℓ ≤ 1
  rw [← hbridge]
  constructor
  · exact (prop_app_pl_vol_zero_iii_c cert γstar CSig
      (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i).1 ℓ.natAbs
  · refine le_of_tendsto ((prop_app_pl_vol_zero_i cert γstar CSig
      (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i hz0 le_rfl).2.1
        ℓ.natAbs) ?_
    filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
    exact (abs_le.mp ((lem_app_pl_two_ridge_ii cert γstar CSig
      (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i).2
        ϱ ℓ.natAbs hϱ)).2

/-- Discharge of the hypothesis `hPSD` of the part-form volatility statements (`volHPSD`, the conclusion of
`lem:app-pl-pieces` for every row sequence). Proof: `lem_app_pl_pieces` for each `n`. -/
theorem prop_app_pl_vol_zero_hPSD (cert : Muon.External.GaussianOpNorm) {α β : ℝ}
    {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c) :
    volHPSD α β N B c := by
  intro n i I J hI hIγ hJ hJγ
  exact (lem_app_pl_pieces cert (R.hBpos n) (R.hNpos n) (plSpec α (c n) (N n))
    (zr_plSpec_anti R.hα (R.hcpos n)) (fun j => zr_plSpec_pos (R.hcpos n) j)
    R.hβ0 R.hβ1 i I J hI hIγ hJ hJγ).2.2

/-- Discharge of the hypothesis `volHZero` of the part-form statements (`CbarPart _ 0 = 1`, the `ℓ = 0` term of
`vPart`). Proof: `prop_app_pl_vol_zero_iii_b` (bridge) and `prop_app_pl_vol_zero_i` (`C̄_{i,0}(0) = 1`). -/
theorem prop_app_pl_vol_zero_hZero (cert : Muon.External.GaussianOpNorm) {α β : ℝ}
    {N B : ℕ → ℕ} {c : ℕ → ℝ} (R : assum_app_pl_regime α β N B c) :
    volHZero α β N B c := by
  intro n i
  let μ : Fin (N n) → ℝ := plSpec α (c n) (N n)
  let γstar : ℝ := gammaOf (N n) (B n)
  let CSig : ℝ := max (μ ⟨0, R.hNpos n⟩) 1
  have hanti : Antitone μ := by
    simpa only [μ] using zr_plSpec_anti R.hα (R.hcpos n)
  have hpos : ∀ j, 0 < μ j := by
    intro j
    simpa only [μ] using zr_plSpec_pos (R.hcpos n) j
  have hγ : gammaOf (N n) (B n) ≤ γstar := le_rfl
  have hμC : ∀ j, μ j ≤ CSig := by
    intro j
    have hj : (⟨0, R.hNpos n⟩ : Fin (N n)) ≤ j := Nat.zero_le j.val
    exact (hanti hj).trans (le_max_left _ _)
  have hC1 : 1 ≤ CSig := le_max_right _ _
  have hz0 : 0 < plZ1 β (B n) μ :=
    (prop_app_pl_branch_i μ R.hβ0 R.hβ1 (R.hBpos n) (R.hNpos n) hanti hpos).2.2.1.mapsTo
      ((def_app_pl_participation_bij μ (R.hBpos n) (R.hNpos n) hpos).1.mapsTo
        (show (1 : ℝ) ∈ Ioi 0 by norm_num))
  have hbridge := (prop_app_pl_vol_zero_iii_b cert γstar CSig
    (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i (0 : ℤ)).2.2
  change CbarPart β (B n) μ i 0 = 1
  calc
    CbarPart β (B n) μ i 0 = cbarZero cert γstar CSig β (B n) μ i (0 : ℤ).natAbs :=
      hbridge.symm
    _ = 1 := by
      simpa using (prop_app_pl_vol_zero_i cert γstar CSig
        (R.hBpos n) (R.hNpos n) μ hanti hpos R.hβ0 R.hβ1 hγ hμC hC1 i hz0 le_rfl).2.2.1

end Muon.PowerLaw

end
