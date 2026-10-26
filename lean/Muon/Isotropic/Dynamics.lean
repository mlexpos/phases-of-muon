import Muon.Dynamics.Main
import Muon.Dynamics.Corollaries
import Muon.Isotropic.Bridge
import Muon.Isotropic.ZeroRidge
import Muon.Drift.OneStep

/-!
# Appendix F, work package L-F.13: the scalar isotropic equation and the isotropic dynamics

Snapshot `cr-2026-10-23`. Source: `sections/05b-isotropic/section.tex`, `prop:app-iso-scalar` (ll. 534–559) and
`cor:app-iso-dynamics` (ll. 608–630). Card: `sections/05b-isotropic/CARD.md` §2, §3, §6 (items 4, 5) and the L-F.13 row of
§5. Interface only: every proof is `sorry`.

Reused, not redefined: `Muon.Isotropic.dIso`, `psiIso`, `isoVol` (L-F.12 bridge), `Muon.Dynamics.DynParams`, `DynHyp`,
`DynCoeff`, `IsActualCoeff`, `Tstar`, `errPath`, `dev0`, `stopTime` (Main), `def_app_dyn_ode`, `odeRisk` (ODE), and the
certificates of `Muon.External`; from `Muon.Setup`: `SetupRegime`, `FrozenSamples`, `FrozenParams`, `SpectralData`,
`riskSigma`, `pairSigma`, `Ahat`.

Representation choices (also in the result JSON `open_questions`):
* The scalar equation `eqn:app-iso-scalar` is the predicate `IsIsoScalarOde h B d v R0 T R`: `R(0) = R0`, and on `[0,T]`
  the solution is positive and has the derivative `−2h d √R + (h²/(2B)) v`. A "solution with `R > 0`" is therefore a
  predicate, and the uniqueness of `prop:app-iso-scalar`(i) is a statement about it.
* `prop:app-iso-scalar`(i) is the mode-to-risk closure for the actual coefficients: the hypothesis is `IsActualCoeff`
  (the coefficients are the drift kernel of C and the mode coefficients of D), and the constants `𝔡_iso`, `𝔳_iso` enter
  through `dIso` and `isoVol`. The uniqueness claim has its own declaration `prop_app_iso_scalar_i_unique`.
* `prop:app-iso-scalar`(ii) is stated for the actual process of `Muon.Setup.SetupRegime` with `ϱ ∈ [ϱ₋, ϱ₊]` (card §6 item 4),
  `ε_B` is the object `Muon.Drift.epsB` and `e_B` is quantified as in `thm_app_iso_volatility`(i) (every upper bound of
  the supremum). The one-step identity is stated as a two-sided bound on the residual `r_t`.
* `cor:app-iso-dynamics`: the standing `C_Σ = 1` of the source's `𝒯⋆` is `hCS : p.CSig = 1`, because `Tstar` and
  `thm_app_dyn_main` read `p.CSig`. The source's `(c)` (`‖Δ_0‖/‖Δ_0‖_F → 0`, `hdev`) is kept although `DynHyp.W0_hat`
  gives the same statement in the normalized form. The comparison solution depends on the dimension (card §6 item 5):
  the family `Rf` is indexed by `k`. The "unique solution" preamble is `cor_app_iso_dynamics_scalar`. The event of
  `cor:app-iso-dynamics`(i) is `isoEvent` (without the Frobenius bound of `thm:app-dyn-main`(i)).
* Every "→ 0 in probability" is `∀ ε > 0, Tendsto (fun k ↦ P {…}) atTop (𝓝 0)` with the supremum in `ℝ≥0∞`, as in
  `Muon.Dynamics.thm_app_dyn_main_iii`. `B → ∞` is the explicit hypothesis `hB`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup Muon.Dynamics

noncomputable section

namespace Muon.Isotropic

/-! ## Definitions -/

/-- The scalar isotropic equation `eqn:app-iso-scalar` with the initial value `R0` on `[0, T]`, for the constants
`h` (macrostep), `B` (batch), `d` (`𝔡_iso`) and `v` (`𝔳_iso`): `R(0) = R0`, and on `[0, T]` the function `R` is
positive and satisfies `R' = −2h d √R + (h²/(2B)) v`. Snapshot `cr-2026-10-23`. -/
def IsIsoScalarOde (h B d v R0 T : ℝ) (R : ℝ → ℝ) : Prop :=
  R 0 = R0 ∧ ∀ τ ∈ Icc (0 : ℝ) T, 0 < R τ ∧
    HasDerivWithinAt R (-(2 * h * d) * Real.sqrt (R τ) + h ^ 2 / (2 * B) * v) (Icc (0 : ℝ) T) τ

/-- The event of `cor:app-iso-dynamics`(i) at dimension `k`: for every integer `t ≤ BT⋆`, `t < t_stop` and
`𝓡(Δ_t) ≥ r₀/2` (the event of `thm:app-dyn-main`(i) without its Frobenius clause). Snapshot `cr-2026-10-23`. -/
def isoEvent {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ → ℕ}
    {C : ∀ k : ℕ, Covariances (m k) (n k)} (hyp : DynHyp p P m n B C) (k : ℕ) : Set Ω :=
  {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p →
    (t : ℕ∞) < stopTime hyp k ω ∧ p.r0 / 2 ≤ riskSigma (C k) (errPath hyp k t ω)}

/-! ## `prop:app-iso-scalar` -/

private lemma iso_scalar_eigenvalues {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) :
    (∀ i, S.μ i = 1) ∧ ∀ j, S.lam j = 1 := by
  constructor
  · intro i
    have h := eig_u S i
    rw [hIso.2, Matrix.one_mulVec] at h
    have hn := sum_col_sq_eq_one S.uOut S.huOut i
    have huu : S.u i ⬝ᵥ S.u i = 1 := by
      simpa [dotProduct, SpectralData.u, sq] using hn
    have h2 := congrArg (fun w => S.u i ⬝ᵥ w) h
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [huu] at h2
    linarith
  · intro j
    have h := eig_v S j
    rw [hIso.1, Matrix.one_mulVec] at h
    have hn := sum_col_sq_eq_one S.vIn S.hvIn j
    have hvv : S.v j ⬝ᵥ S.v j = 1 := by
      simpa [dotProduct, SpectralData.v, sq] using hn
    have h2 := congrArg (fun w => S.v j ⬝ᵥ w) h
    simp only [dotProduct_smul, smul_eq_mul] at h2
    rw [hvv] at h2
    linarith

private lemma iso_scalar_initial_risk {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (D : Mat m n) :
    odeRisk S.μ S.lam (B : ℝ) (odeInit (B : ℝ) S D) = riskSigma F.C D := by
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  rw [riskSigma, show pairSigma F.C D D / 2 = (1 / 2) * pairSigma F.C D D by ring,
    lem_app_setup_decomposition_ii S D]
  unfold odeRisk odeInit
  field_simp

private lemma iso_scalar_risk_deriv {m n : ℕ} (B : ℝ) (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (e f : ℝ → Fin m → Fin n → ℝ) (s : Set ℝ) (t : ℝ)
    (he : HasDerivWithinAt e (f t) s t) :
    HasDerivWithinAt (fun x => odeRisk μ lam B (e x))
      ((1 / 2) * ∑ i, ∑ j, μ i * lam j * f t i j / B ^ 2) s t := by
  unfold odeRisk
  have hij (i : Fin m) (j : Fin n) : HasDerivWithinAt (fun x => e x i j) (f t i j) s t := by
    have hi := hasFDerivWithinAt_pi'.mp he.hasFDerivWithinAt i
    have hij := hasFDerivWithinAt_pi'.mp hi j
    simpa only [ContinuousLinearMap.coe_comp', Function.comp_apply,
      ContinuousLinearMap.proj_apply, ContinuousLinearMap.toSpanSingleton_apply, one_smul]
      using hij.hasDerivWithinAt
  convert (HasDerivWithinAt.const_mul (1 / 2) (HasDerivWithinAt.sum fun i _ =>
      HasDerivWithinAt.sum fun j _ =>
        ((hij i j).const_mul (μ i * lam j)).div_const (B ^ 2))) using 1 <;> simp <;> ring

private lemma iso_scalar_dims_pos {m n B : ℕ} (F : FrozenParams m n B) : 0 < m ∧ 0 < n := by
  constructor
  · by_contra hm
    have hm0 : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    have hA := F.hA
    simp [fro] at hA
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    have hA := F.hA
    simp [fro] at hA

private lemma iso_scalar_mode_vol {m n B : ℕ} (cert : Muon.External.GaussianOpNorm)
    (p : DynParams) (F : FrozenParams m n B) (S : SpectralData F.C)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (i : Fin m) (j : Fin n) :
    Muon.Volatility.modeVij cert p.γstar p.CSig F S p.ϱ i j =
      isoVol cert p.γstar p.CSig F.β m n B p.ϱ / ((m : ℝ) * (n : ℝ)) := by
  classical
  obtain ⟨hμ, hlam⟩ := iso_scalar_eigenvalues F S hIso
  obtain ⟨hm, hn⟩ := iso_scalar_dims_pos F
  have hμf : S.μ = fun _ => (1 : ℝ) := funext hμ
  have hlamf : S.lam = fun _ => (1 : ℝ) := funext hlam
  have hmuvals : Finset.image (fun _ : Fin m => (1 : ℝ)) Finset.univ = {1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · rintro rfl
      exact ⟨⟨0, hm⟩, rfl⟩
  have hlamvals : Finset.image (fun _ : Fin n => (1 : ℝ)) Finset.univ = {1} := by
    ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, rfl⟩
      rfl
    · rintro rfl
      exact ⟨⟨0, hn⟩, rfl⟩
  unfold Muon.Volatility.modeVij Muon.Volatility.measureZeta Muon.Volatility.pairMeasure
    Muon.Volatility.muVals Muon.Volatility.lamVals Muon.Volatility.classDiag isoVol
  simp [hμf, hlamf, hmuvals, hlamvals, hm.ne', hn.ne', F.hB.ne']

private lemma iso_scalar_hermitian_eig_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ)
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

private lemma iso_scalar_spec_measures {m n B : ℕ} (F : FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) :
    ((Muon.Drift.specOutFM F : FiniteMeasure ℝ) : Measure ℝ) =
        isoSpecMeasure ((m : ℝ) / (B : ℝ)) ∧
      ((Muon.Drift.specInFM F : FiniteMeasure ℝ) : Measure ℝ) =
        isoSpecMeasure ((n : ℝ) / (B : ℝ)) := by
  have hout : ∀ i, F.C.psdOut.isHermitian.eigenvalues i = 1 :=
    iso_scalar_hermitian_eig_one F.C.Sout F.C.psdOut.isHermitian hIso.2
  have hin : ∀ i, F.C.psdIn.isHermitian.eigenvalues i = 1 :=
    iso_scalar_hermitian_eig_one F.C.Sin F.C.psdIn.isHermitian hIso.1
  constructor <;> ext A hA <;>
    simp [Muon.Drift.specOutFM, Muon.Drift.specInFM, Muon.Oversampled.nuOutFM,
      Muon.nuOut, Muon.nuIn, isoSpecMeasure, hout, hin, Measure.smul_apply, hA,
      ENNReal.ofReal_div_of_pos (by exact_mod_cast F.hB : (0 : ℝ) < (B : ℝ))] <;>
    simp only [div_eq_mul_inv] <;> ac_rfl

private lemma iso_scalar_branch {m n B : ℕ} (F : FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {β s : ℝ} (hβ : 0 ≤ β ∧ β < 1) (hs : 0 < s) :
    Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s
      (Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β))
        (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) s) := by
  obtain ⟨hm, hn⟩ := iso_scalar_dims_pos F
  obtain ⟨hout, hin⟩ := iso_scalar_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
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
        ENNReal.ofReal_le_ofReal (le_max_left ((m : ℝ) / (B : ℝ)) ((n : ℝ) / (B : ℝ)))
    · constructor
      · simp [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply]
      · constructor
        · simpa [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply] using
            ENNReal.ofReal_le_ofReal (le_max_right ((m : ℝ) / (B : ℝ)) ((n : ℝ) / (B : ℝ)))
        · simp [Muon.DetEquiv.classK, isoSpecMeasure, Measure.smul_apply]
  · exact hs

private lemma iso_scalar_kernel {m n B : ℕ} (F : FrozenParams m n B)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) {β ϱ : ℝ} (hβ : 0 ≤ β ∧ β < 1) (hϱ : 0 < ϱ) :
    Muon.Drift.kernel (Muon.emaW β) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ 1 1 =
      dIso β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ := by
  obtain ⟨hm, hn⟩ := iso_scalar_dims_pos F
  obtain ⟨hout, hin⟩ := iso_scalar_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
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
    iso_scalar_branch F hIso hβ hs
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

/-- `prop:app-iso-scalar`(i), existence part, snapshot `cr-2026-10-23`. Let `(𝔔_ij)` (`e`) solve the mode-energy
equations `def:app-dyn-ode` on `[0, T]` for the actual coefficients (`IsActualCoeff`) of the isotropic covariances
`Σ_in = Σ_out = Id`, with the initial value `Δ_0`. Then `𝓡 = ½ ∑ μ_i λ_j 𝔔_ij` solves `eqn:app-iso-scalar`, with
`𝔡_iso = dIso` and `𝔳_iso = isoVol` and the initial value `cR(0) = riskSigma Δ_0`, positively on `[0, T]`.
Source, `section.tex` ll. 534–559, verbatim:
```latex
\begin{proposition}[Scalar reduction]\label{prop:app-iso-scalar}
Let $\Sigmain=\Id_{\Nin}$ and $\Sigmaout=\Id_{\Nout}$, let $\bmom\in[0,1)$,
$\ridge>0$ and $\macrostep>0$, and write $\mathfrak d_{\mathrm{iso}}$ and
$\mathfrak v_{\mathrm{iso}}=\mathfrak v_{\mathrm{iso}}(\ridge)$ for the
numbers of \cref{thm:app-iso-drift,thm:app-iso-volatility}.
\begin{enumerate}[label=(\roman*)]
\item The deterministic mode-energy equations \cref{eqn:app-dyn-ode} close
on the risk: if $(\fQ_{ij})$ solves them on an interval on which $\fRisk>0$,
then $\fRisk=\frac12\sum_{i,j}\fQ_{ij}$ solves
\begin{equation}\label{eqn:app-iso-scalar}
\frac{\dif\fRisk}{\dif\macrotime}=-2\macrostep\,\mathfrak d_{\mathrm{iso}}\sqrt{\fRisk}+\frac{\macrostep^2}{2B}\,\mathfrak v_{\mathrm{iso}},\qquad
\fRisk(0)=\cR(0),
\end{equation}
and \cref{eqn:app-iso-scalar} has at most one solution with $\fRisk>0$ on
any interval $[0,T]$.
\item Under \cref{assum:app-setup-regime}, one step of size $\lr\ge0$ from a
frozen state, $\Delta^+=\Dt-\lr\,\Qridge\ridge(\Mt)$, satisfies
\begin{equation}\label{eqn:app-iso-onestep}
\begin{gathered}
\EE\,\cR(\Delta^+)-\cR(t)=-2\lr\,\mathfrak d_{\mathrm{iso}}\sqrt{\cR(t)}+\frac{\lr^2B}{2}\,\psi(\ridge)+r_t,\\
\abs{r_t}\le\lr\sqrt{2\cR(t)}\,\varepsilon_B+\frac{\lr^2B}{2}\,\gamma_\star\ridge_+e_B ,
\end{gathered}
\end{equation}
with $\varepsilon_B$ of \cref{thm:app-drift-mean} and $e_B$ of \cref{thm:app-vol-half-same}.
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_iso_scalar_i (cert : Muon.External.GaussianOpNorm) (p : DynParams)
    {m n B : ℕ} (F : FrozenParams m n B) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    (S : SpectralData F.C) (c : DynCoeff p S B) (hc : IsActualCoeff cert F S c)
    (Δ0 : Mat m n) (T : ℝ) (e : ℝ → Fin m → Fin n → ℝ) (he : def_app_dyn_ode p S c Δ0 T e) :
    IsIsoScalarOde p.h (B : ℝ) (dIso p.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) p.ϱ)
      (isoVol cert p.γstar p.CSig p.β m n B p.ϱ) (riskSigma F.C Δ0) T
      (fun τ => odeRisk S.μ S.lam (B : ℝ) (e τ)) := by
  obtain ⟨hμ, hlam⟩ := iso_scalar_eigenvalues F S hIso
  obtain ⟨hm, hn⟩ := iso_scalar_dims_pos F
  have hB : (B : ℝ) ≠ 0 := by exact_mod_cast F.hB.ne'
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : c.d (1, 1) = dIso p.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) p.ϱ := by
    calc
      c.d (1, 1) = Muon.Drift.kernel (Muon.emaW p.β) (Muon.Drift.specOutFM F)
          (Muon.Drift.specInFM F) p.ϱ 1 1 := hc.2.1 (1, 1) ⟨⟨zero_le_one, p.hC⟩, ⟨zero_le_one, p.hC⟩⟩
      _ = _ := iso_scalar_kernel F hIso p.hβ p.hϱ
  have hv : ∀ i j, c.v i j =
      isoVol cert p.γstar p.CSig p.β m n B p.ϱ / ((m : ℝ) * (n : ℝ)) := by
    intro i j
    rw [hc.2.2.1 i j, ← hc.1]
    exact iso_scalar_mode_vol cert p F S hIso i j
  refine ⟨?_, ?_⟩
  · change odeRisk S.μ S.lam (B : ℝ) (e 0) = riskSigma F.C Δ0
    rw [he.1.1]
    exact iso_scalar_initial_risk F S hIso Δ0
  · intro τ hτ
    refine ⟨he.2 τ hτ, ?_⟩
    have hder := iso_scalar_risk_deriv (B : ℝ) S.μ S.lam e
      (fun t => odeRHS p.h (B : ℝ) S.μ S.lam c.d c.v (e t)) (Icc 0 T) τ (he.1.2 τ hτ)
    have hR : odeRisk S.μ S.lam (B : ℝ) (e τ) =
        (1 / 2) * (∑ i, ∑ j, e τ i j) / (B : ℝ) ^ 2 := by
      simp only [odeRisk, hμ, hlam, one_mul]
      have hdiv : (∑ i, ∑ j, e τ i j / (B : ℝ) ^ 2) =
          (∑ i, ∑ j, e τ i j) / (B : ℝ) ^ 2 := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_div]
      rw [hdiv]
      ring
    have hsum : (∑ i, ∑ j, e τ i j) =
        2 * (B : ℝ) ^ 2 * odeRisk S.μ S.lam (B : ℝ) (e τ) := by
      rw [hR]
      field_simp
    apply hder.congr_deriv
    simp only [odeRHS, hμ, hlam, one_mul, hd, hv]
    simp_rw [add_div]
    simp_rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hdrift :
        (∑ i, ∑ j, -(2 * p.h * dIso p.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) p.ϱ) /
            Real.sqrt (odeRisk S.μ S.lam (B : ℝ) (e τ)) * e τ i j / (B : ℝ) ^ 2) =
          (-(2 * p.h * dIso p.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) p.ϱ) /
            Real.sqrt (odeRisk S.μ S.lam (B : ℝ) (e τ)) / (B : ℝ) ^ 2) *
            (∑ i, ∑ j, e τ i j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hdrift, hsum]
    have hsqrt : Real.sqrt (odeRisk S.μ S.lam (B : ℝ) (e τ)) ≠ 0 :=
      (Real.sqrt_pos.2 (he.2 τ hτ)).ne'
    field_simp
    linear_combination
      (4 * p.h * (B : ℝ) * dIso p.β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) p.ϱ) *
        (Real.sq_sqrt (he.2 τ hτ).le)

private lemma iso_scalar_rhs_lipschitz (a b δ : ℝ) (hδ : 0 < δ) :
    ∃ K : NNReal, LipschitzOnWith K (fun x : ℝ => -a * Real.sqrt x + b) (Ici δ) := by
  let K : NNReal := ⟨|a| / (2 * Real.sqrt δ), div_nonneg (abs_nonneg a) (by positivity)⟩
  refine ⟨K, (convex_Ici δ : Convex ℝ (Ici δ)).lipschitzOnWith_of_nnnorm_deriv_le ?_ ?_⟩
  · intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (hδ.trans_le hx)
    exact (((Real.hasDerivAt_sqrt hx0).const_mul (-a)).add_const b).differentiableAt
  · intro x hx
    have hxpos : 0 < x := hδ.trans_le hx
    have hd := ((Real.hasDerivAt_sqrt hxpos.ne').const_mul (-a)).add_const b
    rw [hd.deriv]
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    dsimp [K]
    change |-a * (1 / (2 * Real.sqrt x))| ≤ |a| / (2 * Real.sqrt δ)
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ 1 / (2 * Real.sqrt x))]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    rw [one_div]
    apply (inv_le_inv₀ (by positivity) (by positivity)).2
    gcongr
    exact hx

/-- `prop:app-iso-scalar`(i), uniqueness part, snapshot `cr-2026-10-23`. The scalar equation `eqn:app-iso-scalar` has at
most one solution with `𝓡 > 0` on any interval `[0, T]`. Source as in `prop_app_iso_scalar_i`. -/
theorem prop_app_iso_scalar_i_unique (h B d v R0 T : ℝ) (R1 R2 : ℝ → ℝ)
    (h1 : IsIsoScalarOde h B d v R0 T R1) (h2 : IsIsoScalarOde h B d v R0 T R2) :
    EqOn R1 R2 (Icc (0 : ℝ) T) := by
  by_cases hT : 0 ≤ T
  · rcases h1 with ⟨h10, h1⟩
    rcases h2 with ⟨h20, h2⟩
    have hc1 : ContinuousOn R1 (Icc (0 : ℝ) T) := fun t ht => (h1 t ht).2.continuousWithinAt
    have hc2 : ContinuousOn R2 (Icc (0 : ℝ) T) := fun t ht => (h2 t ht).2.continuousWithinAt
    obtain ⟨t1, ht1, hmin1⟩ :=
      isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hc1
    obtain ⟨t2, ht2, hmin2⟩ :=
      isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT) hc2
    let δ := min (R1 t1) (R2 t2)
    have hδ : 0 < δ := lt_min (h1 t1 ht1).1 (h2 t2 ht2).1
    obtain ⟨K, hLip⟩ := iso_scalar_rhs_lipschitz (2 * h * d) (h ^ 2 / (2 * B) * v) δ hδ
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _ x => -(2 * h * d) * Real.sqrt x + h ^ 2 / (2 * B) * v)
      (s := fun _ => Ici δ) (K := K)
    · intro t ht
      exact hLip
    · exact hc1
    · intro t ht
      exact (h1 t (mem_Icc_of_Ico ht)).2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · intro t ht
      exact (min_le_left (R1 t1) (R2 t2)).trans (hmin1 (mem_Icc_of_Ico ht))
    · exact hc2
    · intro t ht
      exact (h2 t (mem_Icc_of_Ico ht)).2.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)
    · intro t ht
      exact (min_le_right (R1 t1) (R2 t2)).trans (hmin2 (mem_Icc_of_Ico ht))
    · exact h10.trans h20.symm
  · intro t ht
    exfalso
    exact hT (ht.1.trans ht.2)

private lemma iso_scalar_opNorm_one (d : ℕ) : Muon.opNorm (1 : Mat d d) ≤ 1 := by
  unfold Muon.opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp [Matrix.toEuclideanLin]

private lemma iso_scalar_size_one (R : Muon.Setup.SetupRegime) (k : ℕ)
    (hIso : (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1) :
    Muon.Volatility.SizeFin (R.F k).C (R.B k) R.γstar 1 := by
  refine ⟨R.dims k, ?_, ?_⟩
  · rw [hIso.2]
    exact iso_scalar_opNorm_one _
  · rw [hIso.1]
    exact iso_scalar_opNorm_one _

open scoped MatrixOrder in
private lemma iso_scalar_EG_trace {m n B : ℕ} (F : FrozenParams m n B) (D E : Mat m n)
    (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1) (hD : F.A = Ahat F.C D)
    (hR : 0 < riskSigma F.C D) :
    Real.sqrt (2 * riskSigma F.C D) * (Muon.Drift.EG F * Eᵀ).trace = (D * Eᵀ).trace := by
  have hc : Real.sqrt (2 * riskSigma F.C D) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have h1 : rOut F.C * rOut F.C = F.C.Sout :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr F.C.psdOut)
  have h2 : rIn F.C * rIn F.C = F.C.Sin :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr F.C.psdIn)
  have heq : Real.sqrt (2 * riskSigma F.C D) • Muon.Drift.EG F = F.C.Sout * D * F.C.Sin := by
    unfold Muon.Drift.EG
    rw [hD]
    unfold Ahat Arot
    rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
    calc rOut F.C * (rOut F.C * D * rIn F.C) * rIn F.C =
        (rOut F.C * rOut F.C) * D * (rIn F.C * rIn F.C) := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, h2]
  calc
    Real.sqrt (2 * riskSigma F.C D) * (Muon.Drift.EG F * Eᵀ).trace =
        (Real.sqrt (2 * riskSigma F.C D) • (Muon.Drift.EG F * Eᵀ)).trace := by
          rw [Matrix.trace_smul]
          simp only [smul_eq_mul]
    _ = ((Real.sqrt (2 * riskSigma F.C D) • Muon.Drift.EG F) * Eᵀ).trace := by
      rw [Matrix.smul_mul]
    _ = ((F.C.Sout * D * F.C.Sin) * Eᵀ).trace := by rw [heq]
    _ = (D * Eᵀ).trace := by rw [hIso.1, hIso.2]; simp

private lemma iso_scalar_zbar_eq_psi {m n B : ℕ} (F : FrozenParams m n B)
    (S : SpectralData F.C) (hIso : F.C.Sin = 1 ∧ F.C.Sout = 1)
    {β ϱ : ℝ} (hβ : 0 ≤ β ∧ β < 1) (hFβ : F.β = β) (hϱ : 0 < ϱ) :
    Muon.Volatility.zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) S.μ ϱ =
      psiIso β ((n : ℝ) / (B : ℝ)) ((m : ℝ) / (B : ℝ)) ϱ := by
  obtain ⟨hm, hn⟩ := iso_scalar_dims_pos F
  obtain ⟨hμ, hlam⟩ := iso_scalar_eigenvalues F S hIso
  obtain ⟨hout, hin⟩ := iso_scalar_spec_measures F hIso
  have hgm : 0 < (m : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hm) (by exact_mod_cast F.hB)
  have hgn : 0 < (n : ℝ) / (B : ℝ) := div_pos (by exact_mod_cast hn) (by exact_mod_cast F.hB)
  let x := Muon.DetEquiv.branchSol (Muon.DetEquiv.Fw (Muon.emaW β))
    (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ
  have hx : Muon.DetEquiv.IsBranchSol (Muon.DetEquiv.Fw (Muon.emaW β))
      (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ x :=
    iso_scalar_branch F hIso hβ hϱ
  have hcl := prop_app_iso_closure_i hβ.1 hβ.2 hgn hgm hϱ hout hin hx
  have hq := lem_app_iso_comparison_iii hβ.1 hβ.2 hgn hgm hϱ hout hin hx
  subst β
  unfold Muon.Volatility.zbarRaw Muon.Volatility.volraw
  simp_rw [hμ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold psiIso qIso
  rw [hq]
  change (B : ℝ)⁻¹ * ((m : ℝ) * (1 * (x.2.2.1 / (ϱ + x.2.2.1)))) = isoPsi F.β ϱ x
  rw [← hcl.2.2.1]
  rw [hcl.1]
  field_simp

/-- `prop:app-iso-scalar`(ii), snapshot `cr-2026-10-23`. Under `assum:app-setup-regime` (`SetupRegime`), with
`Σ_in = Σ_out = Id` and `ϱ ∈ [ϱ₋, ϱ₊]`, one step of size `lr ≥ 0` from the frozen state, `Δ⁺ = Δ_t − lr Q_ϱ(M_t)`,
satisfies, for every `k`, `𝔼 𝓡(Δ⁺) − 𝓡(Δ_t) = −2 lr 𝔡_iso √𝓡(Δ_t) + lr² B/2 ψ(ϱ) + r_t` with
`|r_t| ≤ lr √(2 𝓡(Δ_t)) ε_B + lr² B/2 γ⋆ ϱ₊ e_B`. Here `ε_B` is `Muon.Drift.epsB` and `e_B` is any upper bound of the
supremum of `thm:app-vol-half-same` (quantified as in `thm_app_iso_volatility`(i)). The integrability of `𝓡(Δ⁺)` and of the
quadratic form is a conclusion conjunct. Source as in `prop_app_iso_scalar_i`.
-/
theorem prop_app_iso_scalar_ii (cert : Muon.External.GaussianOpNorm)
    (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, Muon.Setup.FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (SD : ∀ k, Muon.Setup.SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hIso : ∀ k, (R.F k).C.Sin = 1 ∧ (R.F k).C.Sout = 1)
    (hDt : ∀ k, (R.F k).A = Muon.Setup.Ahat (R.F k).C (Dt k))
    (hRt : ∀ k, 0 < Muon.Setup.riskSigma (R.F k).C (Dt k))
    (lr : ℝ) (hlr : 0 ≤ lr) :
    ∀ eB : ℕ → ℝ,
      (∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi, Muon.opNorm (Muon.DetEquiv.expRes (Muon.emaW R.β) (R.F k) (S k) t s -
          Muon.DetEquiv.Rbar (Muon.DetEquiv.Fw (Muon.emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (R.F k).C s) ≤ eB k) →
      ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
        Integrable (fun ω => Muon.Setup.riskSigma (R.F k).C
          (Dt k - lr • Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω))) (P k) ∧
        Integrable (fun ω => Muon.Setup.pairSigma (R.F k).C
          (Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω))
          (Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω))) (P k) ∧
        |(∫ ω, Muon.Setup.riskSigma (R.F k).C
            (Dt k - lr • Muon.Q ϱ (Muon.DetEquiv.WeightedBuf (Muon.emaW R.β) (R.F k) (S k) t ω)) ∂(P k))
          - Muon.Setup.riskSigma (R.F k).C (Dt k)
          - (-(2 * lr * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) *
              Real.sqrt (Muon.Setup.riskSigma (R.F k).C (Dt k))
            + lr ^ 2 * (R.B k : ℝ) / 2 * psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ)|
          ≤ lr * Real.sqrt (2 * Muon.Setup.riskSigma (R.F k).C (Dt k)) *
              Muon.Drift.epsB (Muon.emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
                (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi +
            lr ^ 2 * (R.B k : ℝ) / 2 * R.γstar * R.ϱhi * eB k := by
  intro eB heB k ϱ hϱ
  let lr' : ℕ → ℝ := fun _ => lr
  have hlr' : ∀ j, 0 ≤ lr' j := fun _ => hlr
  obtain ⟨hintRisk, hintQuad, hstep⟩ :=
    (Muon.Drift.prop_app_drift_onestep R P S t SD Dt hDt hRt lr' hlr').1 k ϱ hϱ
  refine ⟨hintRisk, hintQuad, ?_⟩
  obtain ⟨-, -, -, -, -, -, hdrift⟩ := thm_app_iso_drift R P S t hIso SD Dt hDt hRt
  have hdecomp := (hdrift k ϱ hϱ).2.1
  have hlin := (hdrift k ϱ hϱ).2.2
  have hlin' :
      |(Dt k * (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace -
        2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
          Real.sqrt (riskSigma (R.F k).C (Dt k))| ≤
        Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) *
          Muon.Drift.epsB (emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi := by
    rw [hdecomp]
    convert hlin using 1 <;> ring
  have htrace := iso_scalar_EG_trace (R.F k) (Dt k)
    (Muon.Drift.EQ (Muon.emaW R.β) (R.F k) (S k) t ϱ) (hIso k) (hDt k) (hRt k)
  have hsize := iso_scalar_size_one R k (hIso k)
  obtain ⟨r, hquad, hr⟩ := Muon.Volatility.half_onestep (R.F k) (S k) t (SD k)
    lr R.γstar 1 R.ϱlo R.ϱhi (eB k) hsize (hIso k).1 R.hϱ.1
      (by simpa [R.hβ k] using heB k) ϱ hϱ
  have hquad' :
      lr ^ 2 / 2 * (∫ ω, pairSigma (R.F k).C
        (Q ϱ (Muon.DetEquiv.WeightedBuf (emaW R.β) (R.F k) (S k) t ω))
        (Q ϱ (Muon.DetEquiv.WeightedBuf (emaW R.β) (R.F k) (S k) t ω)) ∂(P k)) =
        lr ^ 2 * (R.B k : ℝ) / 2 *
          (Muon.Volatility.zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (SD k).μ ϱ + r) := by
    simpa [Muon.Setup.frozenUpd, Muon.Setup.frozenBuf, Muon.DetEquiv.WeightedBuf, R.hβ k]
      using hquad
  have hzbar := iso_scalar_zbar_eq_psi (R.F k) (SD k) (hIso k)
    (by rw [← R.hβ k]; exact (R.F k).hβ) (R.hβ k)
    (R.hϱ.1.trans_le hϱ.1)
  have hlinprod :
      lr * Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) *
          (Muon.Drift.EG (R.F k) *
            (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace =
        lr * (Dt k * (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace := by
    rw [mul_assoc, htrace]
  have hres :
      (∫ ω, riskSigma (R.F k).C
          (Dt k - lr • Q ϱ (Muon.DetEquiv.WeightedBuf (emaW R.β) (R.F k) (S k) t ω)) ∂(P k)) -
          riskSigma (R.F k).C (Dt k) -
        (-(2 * lr * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) *
            Real.sqrt (riskSigma (R.F k).C (Dt k)) +
          lr ^ 2 * (R.B k : ℝ) / 2 *
            psiIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ) =
      -lr * ((Dt k * (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace -
        2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
          Real.sqrt (riskSigma (R.F k).C (Dt k))) +
        (lr ^ 2 * (R.B k : ℝ) / 2) * r := by
    dsimp [lr'] at hstep
    rw [hstep, hlinprod, hquad', hzbar]
    ring
  rw [hres]
  calc
    |(-lr) * ((Dt k * (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace -
          2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
            Real.sqrt (riskSigma (R.F k).C (Dt k))) +
        (lr ^ 2 * (R.B k : ℝ) / 2) * r|
        ≤ |(-lr) * ((Dt k * (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace -
            2 * dIso R.β ((R.n k : ℝ) / (R.B k : ℝ)) ((R.m k : ℝ) / (R.B k : ℝ)) ϱ *
              Real.sqrt (riskSigma (R.F k).C (Dt k)))| +
          |(lr ^ 2 * (R.B k : ℝ) / 2) * r| := abs_add_le _ _
    _ ≤ lr * Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) *
          Muon.Drift.epsB (emaW R.β) (R.F k) (S k) t (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi +
        lr ^ 2 * (R.B k : ℝ) / 2 * R.γstar * R.ϱhi * eB k := by
      rw [abs_mul, abs_neg, abs_of_nonneg hlr, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ lr ^ 2 * (R.B k : ℝ) / 2)]
      have hcoef : 0 ≤ lr ^ 2 * (R.B k : ℝ) / 2 := by positivity
      have hr' : (lr ^ 2 * (R.B k : ℝ) / 2) * |r| ≤
          (lr ^ 2 * (R.B k : ℝ) / 2) * (R.γstar * R.ϱhi * eB k) :=
        mul_le_mul_of_nonneg_left (by simpa using hr) hcoef
      exact add_le_add (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hlin' hlr)
        (by simpa only [mul_assoc] using hr')

/-! ## `cor:app-iso-dynamics` -/

private lemma iso_dynamics_prob_of_dynHyp {p : DynParams} {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}
    (hyp : DynHyp p P m n B C) : IsProbabilityMeasure P := by
  have hev : ∀ᶠ k in atTop, 1 ≤ B k := hyp.regime.B_top.eventually (eventually_ge_atTop 1)
  obtain ⟨k, hk⟩ := hev.exists
  let a : Fin (B k) := ⟨0, hk⟩
  refine IsProbabilityMeasure.mk ?_
  have hlaw := (hyp.iid k 0).law a
  have hm := Measure.map_apply_of_aemeasurable ((hyp.iid k 0).meas a) MeasurableSet.univ
  rw [hlaw] at hm
  haveI : IsProbabilityMeasure (dataTarget (C k)) := by unfold dataTarget; infer_instance
  simpa only [Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hm.symm

/-- The preamble of `cor:app-iso-dynamics`, snapshot `cr-2026-10-23`: under the hypotheses of the corollary, at each
dimension `k` the scalar equation `eqn:app-iso-scalar` (with `B = B_k`, initial value `riskSigma (dev0)`, interval
`[0, T⋆]`, `T⋆ = Tstar p`) has a unique solution. Its proof uses `prop_app_dyn_ode_i` and `prop_app_iso_scalar_i`.
Source as in `cor_app_iso_dynamics_i`. -/
theorem cor_app_iso_dynamics_scalar (cert : Muon.External.GaussianOpNorm)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (hCS : p.CSig = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n B : ℕ → ℕ}
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSig : ∀ k : ℕ, (F k).C.Sin = 1 ∧ (F k).C.Sout = 1)
    (hdev : Tendsto (fun k : ℕ => Muon.opNorm (dev0 hyp k) / Muon.fro (dev0 hyp k)) atTop (𝓝 0))
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    ∀ k : ℕ, ∃ R : ℝ → ℝ,
      IsIsoScalarOde p.h (B k : ℝ) (dIso p.β ((n k : ℝ) / (B k : ℝ)) ((m k : ℝ) / (B k : ℝ)) p.ϱ)
        (isoVol cert p.γstar p.CSig p.β (m k) (n k) (B k) p.ϱ) (riskSigma (F k).C (dev0 hyp k)) (Tstar p) R ∧
      ∀ R' : ℝ → ℝ,
        IsIsoScalarOde p.h (B k : ℝ) (dIso p.β ((n k : ℝ) / (B k : ℝ)) ((m k : ℝ) / (B k : ℝ)) p.ϱ)
          (isoVol cert p.γstar p.CSig p.β (m k) (n k) (B k) p.ϱ) (riskSigma (F k).C (dev0 hyp k)) (Tstar p) R' →
        EqOn R' R (Icc (0 : ℝ) (Tstar p)) := by
  intro k
  have hSout : opNorm (F k).C.Sout ≤ p.CSig := by
    rw [(hSig k).2, hCS]
    exact iso_scalar_opNorm_one _
  have hSin : opNorm (F k).C.Sin ≤ p.CSig := by
    rw [(hSig k).1, hCS]
    exact iso_scalar_opNorm_one _
  obtain ⟨e, he⟩ := (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
    hSout hSin (hyp.dims k) (by simpa [dev0] using hyp.W0_norm k)
    (by simpa [dev0] using (hyp.W0_risk k).1)
    (by simpa [dev0] using (hyp.W0_risk k).2)).1
  let R : ℝ → ℝ := fun τ => odeRisk (S k).μ (S k).lam (B k : ℝ) (e τ)
  have hR : IsIsoScalarOde p.h (B k : ℝ)
      (dIso p.β ((n k : ℝ) / (B k : ℝ)) ((m k : ℝ) / (B k : ℝ)) p.ϱ)
      (isoVol cert p.γstar p.CSig p.β (m k) (n k) (B k) p.ϱ)
      (riskSigma (F k).C (dev0 hyp k)) (Tstar p) R :=
    prop_app_iso_scalar_i cert p (F k) (hSig k) (S k) (c k) (hc k)
      (dev0 hyp k) (Tstar p) e he
  refine ⟨R, hR, ?_⟩
  intro R' hR'
  exact prop_app_iso_scalar_i_unique _ _ _ _ _ _ R' R hR' hR

/-- `cor:app-iso-dynamics`(i), snapshot `cr-2026-10-23`. Under the hypotheses of the corollary (`hCS` is the source's
`C_Σ = 1` in `𝒯⋆`), with probability tending to one, `t_stop > BT⋆` and `inf_{t≤BT⋆} 𝓡(Δ_t) ≥ r₀/2` (`isoEvent`).
Routes through `thm_app_dyn_main`(i) and hence takes its four certificates and `hc`.
Source, `section.tex` ll. 608–630, verbatim:
```latex
\begin{corollary}[Isotropic dynamics]\label{cor:app-iso-dynamics}
Let $\Sigmain=\Id_{\Nin}$ and $\Sigmaout=\Id_{\Nout}$, fix
$\macrostep>0$, $\ridge>0$, $\bmom\in[0,1)$, $\gamma_\star<\infty$, $E_\star<\infty$,
$c_M<\infty$ and $0<r_0\le r_1<\infty$, and along a sequence of dimensions
with $B\to\infty$ assume:
\begin{enumerate}[label=(\alph*)]
\item \cref{assum:proportional-regime} holds and $\max(\Nin,\Nout)\le\gamma_\star B$;
\item the algorithm of \cref{def:app-setup-algorithm} is run with momentum
$\bmom$, normalized ridge $\ridge$ and step $\lr_t=\macrostep/B$;
\item $W_0$ is deterministic, $\norm{\Delta_0}_\F^2\le E_\star$,
$r_0\le\cR(0)\le r_1$ and $\norm{\Delta_0}/\norm{\Delta_0}_\F\to0$;
\item the initial buffer $M^\circ_{-1}$ is independent of all batches and
$\EE\norm{M^\circ_{-1}}_\F^2\le c_MB$.
\end{enumerate}
Let $T_\star$ be given by \cref{eqn:app-dyn-Tstar} at $C_\Sigma=1$. Then
\cref{eqn:app-iso-scalar} has a unique solution $\fRisk$ on $[0,T_\star]$, and
\begin{enumerate}[label=(\roman*)]
\item with probability tending to one, $t_{\rm stop}>BT_\star$ and
$\inf_{t\le BT_\star}\cR(t)\ge r_0/2$;
\item $\sup_{\macrotime\le T_\star}\abs{\cR(\lfloor B\macrotime\rfloor)-\fRisk(\macrotime)}\to0$ in probability;
\item on the event of (i), $\sup_{t\le BT_\star}\norm{\Dt}/\norm{\Dt}_\F\to0$ in probability.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_iso_dynamics_i (cert : Muon.External.GaussianOpNorm)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (hCS : p.CSig = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n B : ℕ → ℕ}
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSig : ∀ k : ℕ, (F k).C.Sin = 1 ∧ (F k).C.Sout = 1)
    (hdev : Tendsto (fun k : ℕ => Muon.opNorm (dev0 hyp k) / Muon.fro (dev0 hyp k)) atTop (𝓝 0))
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    Tendsto (fun k : ℕ => P (isoEvent hyp k)) atTop (𝓝 1) := by
  letI : IsProbabilityMeasure P := iso_dynamics_prob_of_dynHyp hyp
  have hmain := thm_app_dyn_main_i cert certOp certP certQ hB F hyp S c hc
  have hsub : ∀ k, mainEvent hyp k ⊆ isoEvent hyp k := by
    intro k ω hω
    intro t ht
    exact ⟨(hω t ht).1, (hω t ht).2.1⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain tendsto_const_nhds
  · exact Filter.Eventually.of_forall fun k => measure_mono (hsub k)
  · exact Filter.Eventually.of_forall fun k => prob_le_one

/-- `cor:app-iso-dynamics`(ii), snapshot `cr-2026-10-23`. Let `𝓡_k` be the solution of `eqn:app-iso-scalar` at dimension `k`
(`cor_app_iso_dynamics_scalar`; the family `Rf` is indexed by the dimension, card §6 item 5). Then
`sup_{τ≤T⋆} |𝓡(⌊B τ⌋) − 𝓡_k(τ)| → 0` in probability. Source as in `cor_app_iso_dynamics_i`. -/
theorem cor_app_iso_dynamics_ii (cert : Muon.External.GaussianOpNorm)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (hCS : p.CSig = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n B : ℕ → ℕ}
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSig : ∀ k : ℕ, (F k).C.Sin = 1 ∧ (F k).C.Sout = 1)
    (hdev : Tendsto (fun k : ℕ => Muon.opNorm (dev0 hyp k) / Muon.fro (dev0 hyp k)) atTop (𝓝 0))
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    ∀ Rf : ∀ k : ℕ, ℝ → ℝ,
      (∀ k : ℕ, IsIsoScalarOde p.h (B k : ℝ)
        (dIso p.β ((n k : ℝ) / (B k : ℝ)) ((m k : ℝ) / (B k : ℝ)) p.ϱ)
        (isoVol cert p.γstar p.CSig p.β (m k) (n k) (B k) p.ϱ) (riskSigma (F k).C (dev0 hyp k)) (Tstar p) (Rf k)) →
      ∀ ε : ℝ, 0 < ε →
        Tendsto (fun k : ℕ => P {ω | ENNReal.ofReal ε <
          ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
            |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) - Rf k τ|})
          atTop (𝓝 0) := by
  intro Rf hRf ε hε
  have hSout : ∀ k, opNorm (F k).C.Sout ≤ p.CSig := by
    intro k
    rw [(hSig k).2, hCS]
    exact iso_scalar_opNorm_one _
  have hSin : ∀ k, opNorm (F k).C.Sin ≤ p.CSig := by
    intro k
    rw [(hSig k).1, hCS]
    exact iso_scalar_opNorm_one _
  choose e he using fun k => (prop_app_dyn_ode_i p (S k) (c k) (dev0 hyp k)
    (hSout k) (hSin k) (hyp.dims k) (by simpa [dev0] using hyp.W0_norm k)
    (by simpa [dev0] using (hyp.W0_risk k).1)
    (by simpa [dev0] using (hyp.W0_risk k).2)).1
  have hmain := (thm_app_dyn_main_iii cert certOp certP certQ hB F hyp S c hc e he).2.2 ε hε
  have heq : ∀ k, EqOn (Rf k)
      (fun τ => odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ)) (Icc (0 : ℝ) (Tstar p)) := by
    intro k
    apply prop_app_iso_scalar_i_unique _ _ _ _ _ _
    · exact hRf k
    · exact prop_app_iso_scalar_i cert p (F k) (hSig k) (S k) (c k) (hc k)
        (dev0 hyp k) (Tstar p) (e k) (he k)
  have hfun : (fun k : ℕ => P {ω | ENNReal.ofReal ε <
      ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) - Rf k τ|}) =
      (fun k : ℕ => P {ω | ENNReal.ofReal ε <
        ⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
          |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) -
            odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ)|}) := by
    funext k
    apply congrArg P
    ext ω
    simp only [Set.mem_setOf_eq]
    rw [show (⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
        |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) - Rf k τ|) =
        (⨆ τ ∈ Icc (0 : ℝ) (Tstar p), ENNReal.ofReal
          |riskSigma (F k).C (errPath hyp k ⌊(B k : ℝ) * τ⌋₊ ω) -
            odeRisk (S k).μ (S k).lam (B k : ℝ) (e k τ)|) by
      apply iSup_congr
      intro τ
      apply iSup_congr
      intro hτ
      rw [heq k hτ]]
  rw [hfun]
  exact hmain

open scoped Matrix.Norms.L2Operator in
private lemma iso_normState_opNorm_eq {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hIso : C.Sin = 1 ∧ C.Sout = 1) :
    opNorm (normState C D) = opNorm D / fro D := by
  have hrot : Arot C D = D := by
    simp [Arot, rOut, rIn, hIso.1, hIso.2]
  have hrisk : riskSigma C D = fro D ^ 2 / 2 := by
    rw [eqn_app_setup_whitened_risk, hrot]
  have hf : 0 ≤ fro D := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt (2 * riskSigma C D) = fro D := by
    rw [hrisk, show 2 * (fro D ^ 2 / 2) = fro D ^ 2 by ring, Real.sqrt_sq hf]
  change opNorm (Ahat C D) = opNorm D / fro D
  rw [Ahat, hrot, hsqrt, opNorm_eq_norm, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg hf, ← opNorm_eq_norm]
  ring

private lemma iso_risk_nonneg {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    0 ≤ riskSigma C D := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma iso_risk_cont {m n : ℕ} (C : Covariances m n) :
    Continuous (fun D : Mat m n => riskSigma C D) := by
  unfold riskSigma pairSigma
  fun_prop

private lemma iso_mat_meas {X : Type} {σ : MeasurableSpace X} {m n : ℕ} {f : X → Mat m n}
    (hf : ∀ i j, Measurable[σ] fun x => f x i j) : Measurable[σ] f :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => hf i j

private lemma iso_entry_meas {X : Type} {σ : MeasurableSpace X} {m n : ℕ} {f : X → Mat m n}
    (hf : Measurable[σ] f) (i : Fin m) (j : Fin n) : Measurable[σ] fun x => f x i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)

private lemma iso_grad_meas {X : Type} {σ : MeasurableSpace X} {B m n : ℕ}
    {Δ : X → Mat m n} {b : X → Batch m n B} (hΔ : Measurable[σ] Δ) (hb : Measurable[σ] b) :
    Measurable[σ] (fun x => grad (Δ x) (b x)) := by
  have hc : Continuous (fun q : Mat m n × Batch m n B => grad q.1 q.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun q : Mat m n × Batch m n B => grad q.1 q.2)
    (f := fun x => (Δ x, b x)) hc.measurable (hΔ.prodMk hb)

private lemma iso_stepUpdate_meas {X : Type} {σ : MeasurableSpace X} {B m n : ℕ}
    (C : Covariances m n) (q : AlgParams m n) (s : X → AlgState m n) (b : X → Batch m n B)
    (hW : Measurable[σ] (fun x => (s x).W)) (hM : Measurable[σ] (fun x => (s x).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun x => stepUpdate C q (s x) (b x)) ∧
      Measurable[σ] (fun x => stepBuffer q (s x) (b x)) := by
  have hWc : Continuous (fun A : Mat m n => A - q.Wstar) := continuous_id.sub continuous_const
  have hD : Measurable[σ] (fun x => errorOf q (s x)) := hWc.measurable.comp hW
  have hR : Measurable[σ] (fun x => riskSigma C (errorOf q (s x))) :=
    (iso_risk_cont C).measurable.comp hD
  have hset : MeasurableSet[σ] {x | riskSigma C (errorOf q (s x)) = 0} :=
    hR (measurableSet_singleton 0)
  have hF : Measurable[σ] (fun x => grad (errorOf q (s x)) (b x)) := iso_grad_meas hD hb
  have hbuf : Measurable[σ] (fun x => stepBuffer q (s x) (b x)) := by
    apply iso_mat_meas
    intro i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact ((iso_entry_meas hM i j).const_mul _).add ((iso_entry_meas hF i j).const_mul _)
  refine ⟨?_, hbuf⟩
  refine Measurable.ite hset measurable_const ?_
  have hnn : ∀ x, (0 : ℝ) ≤ 2 * riskSigma C (errorOf q (s x)) * q.ϱ :=
    fun x => mul_nonneg (mul_nonneg (by norm_num) (iso_risk_nonneg C _)) q.hϱ.le
  have hφ : Measurable[σ]
      (fun x => (⟨2 * riskSigma C (errorOf q (s x)) * q.ϱ, hnn x⟩ : Set.Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const q.ϱ).subtype_mk
  exact measurable_Q.comp (hφ.prodMk hbuf)

private lemma iso_step_meas {X : Type} {σ : MeasurableSpace X} {B m n : ℕ}
    (C : Covariances m n) (q : AlgParams m n) (k : ℕ) (s : X → AlgState m n) (b : X → Batch m n B)
    (hW : Measurable[σ] (fun x => (s x).W)) (hM : Measurable[σ] (fun x => (s x).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun x => (step C q k (s x) (b x)).W) ∧
      Measurable[σ] (fun x => (step C q k (s x) (b x)).Mprev) := by
  obtain ⟨hU, hbuf⟩ := iso_stepUpdate_meas C q s b hW hM hb
  refine ⟨?_, hbuf⟩
  apply iso_mat_meas
  intro i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact (iso_entry_meas hW i j).sub ((iso_entry_meas hU i j).const_mul _)

private lemma iso_run_aem {X : Type} [mX : MeasurableSpace X] {P : Measure X} {m n B : ℕ}
    (C : Covariances m n) (q : AlgParams m n) (W0 : Mat m n) (M : X → Mat m n)
    (hM : AEMeasurable M P) (x : ℕ → X → Batch m n B)
    (hx : ∀ u a, AEMeasurable (fun ω => x u ω a) P) (t : ℕ) :
    AEMeasurable (fun ω => (run C q (initState W0 (M ω)) (fun u => x u ω) t).W) P ∧
      AEMeasurable (fun ω => (run C q (initState W0 (M ω)) (fun u => x u ω) t).Mprev) P := by
  classical
  let xm : ℕ → X → Batch m n B := fun u ω a => (hx u a).mk _ ω
  let Mm : X → Mat m n := hM.mk M
  have hxm : ∀ u, Measurable (xm u) := fun u =>
    measurable_pi_iff.mpr fun a => (hx u a).measurable_mk
  have hMm : Measurable Mm := hM.measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ u, x u ω = xm u ω := by
    have h : ∀ u a, ∀ᵐ ω ∂P, x u ω a = xm u ω a := fun u a => (hx u a).ae_eq_mk
    refine ae_all_iff.2 fun u => ?_
    filter_upwards [ae_all_iff.2 (h u)] with ω hω
    funext a
    exact hω a
  have haeM : ∀ᵐ ω ∂P, M ω = Mm ω := hM.ae_eq_mk
  have hmeas : Measurable (fun ω => (run C q (initState W0 (Mm ω)) (fun u => xm u ω) t).W) ∧
      Measurable (fun ω => (run C q (initState W0 (Mm ω)) (fun u => xm u ω) t).Mprev) := by
    induction t with
    | zero => exact ⟨measurable_const, hMm⟩
    | succ k ih =>
      simpa only [run] using iso_step_meas C q k
        (fun ω => run C q (initState W0 (Mm ω)) (fun u => xm u ω) k) (xm k) ih.1 ih.2 (hxm k)
  have hrun : ∀ᵐ ω ∂P, run C q (initState W0 (M ω)) (fun u => x u ω) t =
      run C q (initState W0 (Mm ω)) (fun u => xm u ω) t := by
    filter_upwards [hae, haeM] with ω hx' hM'
    rw [show (fun u => x u ω) = (fun u => xm u ω) from funext hx', hM']
  have e1 : (fun ω => (run C q (initState W0 (M ω)) (fun u => x u ω) t).W) =ᵐ[P]
      (fun ω => (run C q (initState W0 (Mm ω)) (fun u => xm u ω) t).W) :=
    hrun.mono (fun ω h => by simp only [h])
  have e2 : (fun ω => (run C q (initState W0 (M ω)) (fun u => x u ω) t).Mprev) =ᵐ[P]
      (fun ω => (run C q (initState W0 (Mm ω)) (fun u => xm u ω) t).Mprev) :=
    hrun.mono (fun ω h => by simp only [h])
  exact ⟨hmeas.1.aemeasurable.congr e1.symm, hmeas.2.aemeasurable.congr e2.symm⟩

private lemma iso_errPath_aem {p : DynParams} {X : Type} [MeasurableSpace X] {P : Measure X}
    {m n B : ℕ → ℕ} {C : ∀ k, Covariances (m k) (n k)}
    (hyp : DynHyp p P m n B C) (k t : ℕ) : AEMeasurable (errPath hyp k t) P := by
  have h := (iso_run_aem (C k) (hyp.alg k) (hyp.W0 k) (hyp.Mm1 k) (hyp.Mm1_meas k)
    (hyp.x k) (fun u a => (hyp.iid k u).meas a) t).1
  exact (continuous_id.sub continuous_const).measurable.comp_aemeasurable h

/-- `cor:app-iso-dynamics`(iii), snapshot `cr-2026-10-23`. On the event of (i) (`isoEvent`), the normalized states tend
to zero in probability: `sup_{t≤BT⋆} ‖Δ_t‖/‖Δ_t‖_F → 0` in probability, written as `P (isoEvent ∩ {ε < sup}) → 0`
(the ratio `opNorm Δ_t / fro Δ_t` is `‖Â_t‖` for `Σ_in = Σ_out = Id`). Source as in `cor_app_iso_dynamics_i`. -/
theorem cor_app_iso_dynamics_iii (cert : Muon.External.GaussianOpNorm)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (certQ : Muon.External.GaussianQuadFormLp)
    (p : DynParams) (hCS : p.CSig = 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {m n B : ℕ → ℕ}
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (hSig : ∀ k : ℕ, (F k).C.Sin = 1 ∧ (F k).C.Sout = 1)
    (hdev : Tendsto (fun k : ℕ => Muon.opNorm (dev0 hyp k) / Muon.fro (dev0 hyp k)) atTop (𝓝 0))
    (hB : Tendsto (fun k : ℕ => B k) atTop atTop)
    (S : ∀ k : ℕ, SpectralData (F k).C) (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun k : ℕ => P (isoEvent hyp k ∩ {ω | ENNReal.ofReal ε <
        ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
          ENNReal.ofReal (Muon.opNorm (errPath hyp k t ω) / Muon.fro (errPath hyp k t ω))}))
        atTop (𝓝 0) := by
  intro ε hε
  letI : IsProbabilityMeasure P := iso_dynamics_prob_of_dynHyp hyp
  let G : ℕ → Set Ω := fun k => {ω | ∀ t : ℕ, (t : ℝ) ≤ (B k : ℝ) * Tstar p →
    fro (errPath hyp k t ω) ^ 2 ≤ p.Estar + 1}
  have hGnull : ∀ k, NullMeasurableSet (G k) P := by
    intro k
    rw [show G k = ⋂ t : ℕ, {ω | (t : ℝ) ≤ (B k : ℝ) * Tstar p →
        fro (errPath hyp k t ω) ^ 2 ≤ p.Estar + 1} by
      ext ω
      simp only [G, Set.mem_setOf_eq, Set.mem_iInter]]
    apply NullMeasurableSet.iInter
    intro t
    by_cases ht : (t : ℝ) ≤ (B k : ℝ) * Tstar p
    · simp only [ht, true_implies]
      have hc : Continuous (fun D : Mat (m k) (n k) => fro D ^ 2) := by
        unfold fro
        fun_prop
      have hf : AEMeasurable (fun ω => fro (errPath hyp k t ω) ^ 2) P :=
        hc.measurable.comp_aemeasurable (iso_errPath_aem hyp k t)
      exact nullMeasurableSet_le hf aemeasurable_const
    · simp [ht]
  have hmainprob := thm_app_dyn_main_i cert certOp certP certQ hB F hyp S c hc
  have hGprob : Tendsto (fun k => P (G k)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmainprob tendsto_const_nhds
    · exact Filter.Eventually.of_forall fun k => measure_mono (by
        intro ω hω t ht
        exact (hω t ht).2.2)
    · exact Filter.Eventually.of_forall fun k => prob_le_one
  have hGcomp : Tendsto (fun k => P (G k)ᶜ) atTop (𝓝 0) := by
    rw [show (fun k => P (G k)ᶜ) = (fun k => 1 - P (G k)) by
      funext k
      exact prob_compl_eq_one_sub₀ (hGnull k)]
    exact (ENNReal.tendsto_const_sub_nhds_zero_iff (by norm_num) (fun k => prob_le_one)).2 hGprob
  let A : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal ε <
    ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
      ENNReal.ofReal (opNorm (errPath hyp k t ω) / fro (errPath hyp k t ω))}
  let AhatEvent : ℕ → Set Ω := fun k => {ω | ENNReal.ofReal ε <
    ⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
      ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω)))}
  have hA : ∀ k, A k = AhatEvent k := by
    intro k
    ext ω
    simp only [A, AhatEvent, Set.mem_setOf_eq]
    rw [show (⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
        ENNReal.ofReal (opNorm (errPath hyp k t ω) / fro (errPath hyp k t ω))) =
        (⨆ (t : ℕ) (_ : (t : ℝ) ≤ (B k : ℝ) * Tstar p),
          ENNReal.ofReal (opNorm (normState (F k).C (errPath hyp k t ω)))) by
      apply iSup_congr
      intro t
      apply iSup_congr
      intro ht
      rw [iso_normState_opNorm_eq (F k).C _ (hSig k)]]
  have hdiff := thm_app_dyn_main_iv cert certOp certP certQ hB F hyp S c hc ε hε
  have hdiff' : Tendsto (fun k => P (mainEvent hyp k ∩ AhatEvent k)) atTop (𝓝 0) := by
    simpa only [AhatEvent] using hdiff
  have hsub : ∀ k, isoEvent hyp k ∩ A k ⊆
      (mainEvent hyp k ∩ AhatEvent k) ∪ (G k)ᶜ := by
    intro k ω hω
    by_cases hg : ω ∈ G k
    · left
      refine ⟨?_, ?_⟩
      · intro t ht
        exact ⟨(hω.1 t ht).1, (hω.1 t ht).2, hg t ht⟩
      · simpa only [hA k] using hω.2
    · exact Or.inr hg
  have hle : ∀ k, P (isoEvent hyp k ∩ A k) ≤
      P (mainEvent hyp k ∩ AhatEvent k) + P (G k)ᶜ := fun k =>
    (measure_mono (hsub k)).trans (measure_union_le _ _)
  have hsum : Tendsto (fun k => P (mainEvent hyp k ∩ AhatEvent k) + P (G k)ᶜ)
      atTop (𝓝 0) := by
    simpa only [add_zero] using hdiff'.add hGcomp
  have htarget : Tendsto (fun k => P (isoEvent hyp k ∩ A k)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hle)
  simpa only [A] using htarget

end Muon.Isotropic

end
