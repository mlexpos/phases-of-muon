import Muon.PowerLaw.Participation
import Muon.PowerLaw.Weights
import Muon.Volatility.Closed.Kernel

/-!
# Appendix G, work package L-G.10: the two-time row response (interface draft)

Work package L-G.10 (interface draft). Snapshot `cr-2026-10-23`. Source: `sections/06-power-law/section.tex`,
the paragraph "The two-time row response" (l.444–472: `eqn:app-pl-UV`, `eqn:app-pl-divided`,
`prop:app-pl-response`) and the row lag kernel `eqn:app-pl-rowkernel` (l.79–81). Card:
`sections/06-power-law/CARD.md` §2, §3 (row of `prop:app-pl-response`), §5 (row L-G.10), §6 #5, #16.

Reused, not redefined: `gammaOf` (Participation, `γ = N/B`); `bLag`, `eLag` (Weights: the EMA-only
`b_ℓ`, `e_ℓ` of `eqn:app-pl-UV`, shared with L-G.1); `Muon.DetEquiv.branchSol`, `Fw`, `Muon.emaW`
(branch of `def:app-de-branch`); `Muon.Volatility.lagResp`, `Muon.Volatility.iotaF` (D's lag kernel
`𝔨_ℓ`, `eqn:app-vol-lag-kernel`); `Muon.External.GaussianOpNorm` (certificate).
The proof route is D's `Muon.Volatility.prop_app_vol_closed_reductions_ii` (`eqn:app-vol-closed-half`
at `Σ_in = Id`), imported here for the proofs.

Encoding decisions:
* Spectrum: `μ : Fin N → ℝ` with `0 < μ i` for all `i` (source: "every finite positive spectrum"; no
  ordering is assumed). `Σ_in = Id_N` is encoded by the input eigenvalues `fun _ => 1` and the
  input test `fun _ => 1`; `u_i ⊗ u_i` by the output test `Pi.single i 1`.
* Row kernel `𝔨_{i,ℓ}(s,s') = B 𝔨_ℓ[u_i⊗u_i, Id](s,s')` (`eqn:app-pl-rowkernel`) is `(B:ℝ) * lagResp …`
  with `iotaF s`, `iotaF s'` (D's `eqn:app-vol-kernel` convention).
* Branch: `ν, ν'` are arguments with the defining equalities `ν = B⁻¹ ∑ δ_{μ_i}`, `ν' = γ δ_1`, as in
  `Muon.PowerLaw.prop_app_pl_branch_ii`. Admissibility `(ν,ν') ∈ classK C_Σ γ⋆` follows from `hγ`,
  `hμC`, `hC1`, so `branchSol` is the solution of `def:app-de-branch` (B's `thm_app_de_branch_i`).
* Size constants: the source's objects use the size conditions only through `γ⋆ ≥ γ` and
  `C_Σ ≥ max(μ_i, 1)`; the statements quantify over all such constants (`hγ`, `hμC`, `hC1`). `1 ≤ C_Σ`
  is D's hypothesis for `lagResp`. The statements do not depend on the constants (source remark, l.470 ff.).
* `U`, `V`, `Δ_ℓ` are `eqn:app-pl-UV` written on the branch coordinates (`respU`, `respV`, `respDelta`);
  they are finite sums, so no integrability side condition. `b_ℓ, e_ℓ` are `bLag, eLag` at
  `q = q(-s) = s σ σ̃` (`respQ`), `q' = q(-s')`.
* Momentum: `0 ≤ β < 1` (card §2 parametrization and L-G.1's precedent; the source's standing
  `β ∈ (0,1)` is a special case, and D's closed form covers `β = 0`). See open question 2.
* `hN : 0 < N` is implicit in the source's `μ_1 ≥ … ≥ μ_N` indexing; stated explicitly.
* Summability/integrability of the two series of `eqn:app-pl-UV` is not a source claim; it is a separate
  declaration `prop_app_pl_response_summable` because `bLag`, `eLag` are `tsum`s.
* Parts: (i) `Δ_ℓ > 0`; (ii) the identity `𝔨_{i,ℓ} = formula`; (iii) the nonnegativity of the common value,
  stated for both the formula and the kernel.
-/

set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon.DetEquiv

noncomputable section

namespace Muon.PowerLaw

/-! ## Objects of `eqn:app-pl-UV` on the branch

The branch coordinates at `s` are `(σ, σ̃, s̃₁, s₁) = (.1, .2.1, .2.2.1, .2.2.2)` of `branchSol`, as in
`Muon.PowerLaw.prop_app_pl_branch_ii`. -/

/-- `q(-s) = s σ(-s) σ̃(-s)` of `eqn:app-pl-branch` (first display), the argument of `b_ℓ, e_ℓ` in
`eqn:app-pl-UV`. Helper. -/
def respQ (β : ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) : ℝ :=
  s * (branchSol (Fw (emaW β)) ν ν' s).1 * (branchSol (Fw (emaW β)) ν ν' s).2.1

/-- `𝖴` of `eqn:app-pl-UV`, `𝖴 = (1/B) ∑_{j=1}^N μ_j² / ((s + s̃₁ μ_j)(s' + s̃₁' μ_j))`, with `s̃₁` the
third branch coordinate at `s` and `s̃₁'` at `s'`. Helper; `Fin N` indexes `j = 1..N`.

LaTeX, verbatim from `section.tex` (`eqn:app-pl-UV`):
```latex
\begin{equation}\label{eqn:app-pl-UV}
\begin{gathered}
\mathsf U\defeq\frac1B\sum_{j=1}^N\frac{\mu_j^2}{(s+\tilde s_1\mu_j)(s'+\tilde s_1'\mu_j)},\qquad
\mathsf V\defeq\frac{\gamma}{(s+s_1)(s'+s_1')},\\
b_\ell\defeq\sum_{j\ge0}\EE\frac{\bmom^\ell\emaw j^2g^2}{(1+q\emaw j^2g^2)(1+\bmom^{2\ell}q'\emaw j^2g^2)},\qquad
e_\ell\defeq\sum_{j\ge0}\EE\frac{\bmom^{2\ell}\emaw j^4g^4}{(1+q\emaw j^2g^2)(1+\bmom^{2\ell}q'\emaw j^2g^2)},\\
\Delta_\ell\defeq\big(1-ss'\,\mathsf U\tilde\sigma\tilde\sigma'e_\ell\big)\big(1-ss'\,\mathsf V\sigma\sigma'e_\ell\big)-ss'\,\mathsf U\mathsf V\,b_\ell^2 .
\end{gathered}
\end{equation}
```
-/
def respU (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (ν ν' : FiniteMeasure ℝ) (s s' : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * ∑ j : Fin N, μ j ^ 2 /
    ((s + (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ j) *
      (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.1 * μ j))

/-- `𝖵` of `eqn:app-pl-UV`, `𝖵 = γ / ((s + s₁)(s' + s₁'))` with `γ = N/B = gammaOf N B`, `s₁` the
fourth branch coordinate at `s` and `s₁'` at `s'`. Helper. -/
def respV (β : ℝ) (B N : ℕ) (ν ν' : FiniteMeasure ℝ) (s s' : ℝ) : ℝ :=
  gammaOf N B /
    ((s + (branchSol (Fw (emaW β)) ν ν' s).2.2.2) * (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.2))

/-- `Δ_ℓ(s,s')` of `eqn:app-pl-UV`:
`Δ_ℓ = (1 - s s' 𝖴 σ̃ σ̃' e_ℓ)(1 - s s' 𝖵 σ σ' e_ℓ) - s s' 𝖴 𝖵 b_ℓ²`, with `b_ℓ = bLag β q q' ℓ`,
`e_ℓ = eLag β q q' ℓ`, `q = respQ β ν ν' s`, `q' = respQ β ν ν' s'`. Helper.
-/
def respDelta (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (ν ν' : FiniteMeasure ℝ) (ℓ : ℕ) (s s' : ℝ) :
    ℝ :=
  (1 - s * s' * respU β B μ ν ν' s s' * (branchSol (Fw (emaW β)) ν ν' s).2.1 *
        (branchSol (Fw (emaW β)) ν ν' s').2.1 *
        eLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ) *
      (1 - s * s' * respV β B N ν ν' s s' * (branchSol (Fw (emaW β)) ν ν' s).1 *
        (branchSol (Fw (emaW β)) ν ν' s').1 *
        eLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ) -
    s * s' * respU β B μ ν ν' s s' * respV β B N ν ν' s s' *
      bLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ ^ 2

/-- The right-hand side of `eqn:app-pl-response`:
`γ s s' μ_i b_ℓ / ((s + s̃₁ μ_i)(s' + s̃₁' μ_i)(s + s₁)(s' + s₁') Δ_ℓ)`, with `γ = gammaOf N B`.
Helper. -/
def respRHS (β : ℝ) (B : ℕ) {N : ℕ} (μ : Fin N → ℝ) (ν ν' : FiniteMeasure ℝ) (ℓ : ℕ) (i : Fin N)
    (s s' : ℝ) : ℝ :=
  gammaOf N B * s * s' * μ i * bLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ /
    ((s + (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ i) *
      (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.1 * μ i) *
      (s + (branchSol (Fw (emaW β)) ν ν' s).2.2.2) *
      (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.2) * respDelta β B μ ν ν' ℓ s s')

private lemma response_diag_diracs {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
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

private lemma response_nuOut {N B : ℕ} (C : Muon.Covariances N N) (μ : Fin N → ℝ)
    (hB : 0 < B) (hC : C.Sout = Matrix.diagonal μ) :
    Muon.nuOut C B = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i) := by
  unfold Muon.nuOut
  rw [response_diag_diracs C.Sout C.psdOut.isHermitian μ hC]
  congr 1
  simp [ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma response_nuIn {N B : ℕ} (C : Muon.Covariances N N) (hB : 0 < B)
    (hC : C.Sin = 1) :
    Muon.nuIn C B = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ) := by
  unfold Muon.nuIn
  rw [response_diag_diracs C.Sin C.psdIn.isHermitian (fun _ => 1) (by simpa using hC)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ENNReal, smul_smul]
  congr 1
  simp [gammaOf, div_eq_inv_mul,
    ENNReal.ofReal_inv_of_pos (show (0 : ℝ) < B by exact_mod_cast hB)]

private lemma response_diagonal_bound {N : ℕ} (d : Fin N → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hd : ∀ i, |d i| ≤ C) : Muon.opNorm (Matrix.diagonal d) ≤ C := by
  open scoped Matrix.Norms.L2Operator in
  rw [Muon.opNorm_eq_norm, Matrix.l2_opNorm_diagonal]
  exact (pi_norm_le_iff_of_nonneg hC).2 fun i => by
    simpa [Real.norm_eq_abs] using hd i

private lemma response_stdGaussianFamily (A : Type) :
    Muon.Volatility.IsStdGaussianFamily
      (Measure.infinitePi fun _ : A => gaussianReal 0 1) (fun a (x : A → ℝ) => x a) := by
  refine ⟨fun a => measurable_pi_apply a, ?_, fun a => ?_⟩
  · exact iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  · exact ⟨(measurable_pi_apply a).aemeasurable, Measure.infinitePi_map_eval _ a⟩

private lemma response_emaLagB_eq_bLag {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℝ} {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : Muon.Volatility.IsStdGaussianFamily P g) (q q' : ℝ) :
    Muon.Volatility.emaLagB P β ℓ g q q' = bLag β q q' ℓ := by
  unfold Muon.Volatility.emaLagB bLag
  apply tsum_congr
  intro j
  have hw : emaW β (j + ℓ) = β ^ ℓ * emaW β j := by
    unfold emaW
    rw [pow_add]
    ring
  have h := (hg.2.2 (Sum.inl j)).integral_comp
    (f := fun x : ℝ => β ^ ℓ * emaW β j ^ 2 * x ^ 2 /
      ((1 + q * emaW β j ^ 2 * x ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * x ^ 2)))
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [← h]
  congr 1
  funext ω
  rw [hw]
  unfold Muon.Volatility.phiQ
  simp only [Function.comp_apply, div_eq_mul_inv]
  rw [mul_inv]
  ring

private lemma response_emaLagE_eq_eLag {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {β : ℝ} {ℓ : ℕ} {g : ℕ ⊕ Fin ℓ → Ω → ℝ}
    (hg : Muon.Volatility.IsStdGaussianFamily P g) (q q' : ℝ) :
    Muon.Volatility.emaLagE P β ℓ g q q' = eLag β q q' ℓ := by
  unfold Muon.Volatility.emaLagE eLag
  apply tsum_congr
  intro j
  have hw : emaW β (j + ℓ) = β ^ ℓ * emaW β j := by
    unfold emaW
    rw [pow_add]
    ring
  have h := (hg.2.2 (Sum.inl j)).integral_comp
    (f := fun x : ℝ => β ^ (2 * ℓ) * emaW β j ^ 4 * x ^ 4 /
      ((1 + q * emaW β j ^ 2 * x ^ 2) *
        (1 + β ^ (2 * ℓ) * q' * emaW β j ^ 2 * x ^ 2)))
    (Measurable.aestronglyMeasurable (by fun_prop))
  rw [← h]
  congr 1
  funext ω
  rw [hw]
  unfold Muon.Volatility.psiQ
  simp only [Function.comp_apply, div_eq_mul_inv]
  rw [mul_inv]
  ring

private lemma response_tsum_inl {ℓ : ℕ} (f : ℕ ⊕ Fin ℓ → ℝ)
    (h : ∀ i, f (Sum.inr i) = 0) : ∑' a, f a = ∑' j : ℕ, f (Sum.inl j) := by
  refine (Function.Injective.tsum_eq Sum.inl_injective (f := f) ?_).symm
  intro a ha
  rcases a with j | i
  · exact ⟨j, rfl⟩
  · exact absurd (h i) ha

private lemma response_pairedB_eq_emaLagB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    Muon.Volatility.pairedB P (Muon.Volatility.emaXi₁ β ℓ g)
        (Muon.Volatility.emaXi₂ β ℓ g) q q' =
      Muon.Volatility.emaLagB P β ℓ g q q' := by
  unfold Muon.Volatility.pairedB Muon.Volatility.emaLagB
  rw [response_tsum_inl _ (fun i => by simp [Muon.Volatility.emaXi₁])]
  apply tsum_congr
  intro j
  have hw : emaW β (j + ℓ) = β ^ ℓ * emaW β j := by
    unfold emaW
    rw [pow_add]
    ring
  congr 1
  funext ω
  simp only [Muon.Volatility.emaXi₁, Muon.Volatility.emaXi₂]
  unfold Muon.Volatility.phiQ
  rw [hw]
  simp only [div_eq_mul_inv]
  rw [mul_inv]
  ring

private lemma response_pairedE_eq_emaLagE {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (β : ℝ) (ℓ : ℕ) (g : ℕ ⊕ Fin ℓ → Ω → ℝ) (q q' : ℝ) :
    Muon.Volatility.pairedE P (Muon.Volatility.emaXi₁ β ℓ g)
        (Muon.Volatility.emaXi₂ β ℓ g) q q' =
      Muon.Volatility.emaLagE P β ℓ g q q' := by
  unfold Muon.Volatility.pairedE Muon.Volatility.emaLagE
  rw [response_tsum_inl _ (fun i => by simp [Muon.Volatility.emaXi₁])]
  apply tsum_congr
  intro j
  have hw : emaW β (j + ℓ) = β ^ ℓ * emaW β j := by
    unfold emaW
    rw [pow_add]
    ring
  congr 1
  funext ω
  simp only [Muon.Volatility.emaXi₁, Muon.Volatility.emaXi₂]
  unfold Muon.Volatility.psiQ
  rw [hw]
  simp only [div_eq_mul_inv]
  rw [mul_inv]
  ring

private lemma response_trace_two_resolvents {d : ℕ}
    (A U : Matrix (Fin d) (Fin d) ℝ) (v w : Fin d → ℝ)
    (hU : U.transpose * U = 1) (hA : A = U * Matrix.diagonal v * U.transpose)
    (F : Matrix (Fin d) (Fin d) ℝ) (hF : F = U * Matrix.diagonal w * U.transpose)
    (s a u c : ℝ) (hs : ∀ i, s + a * v i ≠ 0) (hu : ∀ i, u + c * v i ≠ 0) :
    (F * A * (s • (1 : Matrix (Fin d) (Fin d) ℝ) + a • A)⁻¹ *
      (u • (1 : Matrix (Fin d) (Fin d) ℝ) + c • A)⁻¹).trace =
        ∑ i, w i * v i / ((s + a * v i) * (u + c * v i)) := by
  classical
  have hUU : U * U.transpose = 1 := mul_eq_one_comm.mp hU
  have hinv : ∀ (t b : ℝ), (∀ i, t + b * v i ≠ 0) →
      (t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A)⁻¹ =
        U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * U.transpose := by
    intro t b hden
    have he : Matrix.diagonal (fun i => t + b * v i) =
        t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • Matrix.diagonal v := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij]
    have hfac : t • (1 : Matrix (Fin d) (Fin d) ℝ) + b • A =
        U * Matrix.diagonal (fun i => t + b * v i) * U.transpose := by
      rw [he, Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hUU, ← hA]
    have hdiag : Matrix.diagonal (fun i => t + b * v i) *
        Matrix.diagonal (fun i => (t + b * v i)⁻¹) = 1 := by
      rw [Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j <;> simp [Matrix.diagonal_apply, Matrix.one_apply, hij, hden]
    apply Matrix.inv_eq_right_inv
    rw [hfac]
    calc U * Matrix.diagonal (fun i => t + b * v i) * U.transpose *
          (U * Matrix.diagonal (fun i => (t + b * v i)⁻¹) * U.transpose) =
        U * (Matrix.diagonal (fun i => t + b * v i) *
          Matrix.diagonal (fun i => (t + b * v i)⁻¹)) * U.transpose := by
            simp only [Matrix.mul_assoc]
            rw [← Matrix.mul_assoc U.transpose U, hU, Matrix.one_mul]
      _ = 1 := by rw [hdiag, Matrix.mul_one, hUU]
  rw [hinv s a hs, hinv u c hu, hA, hF]
  calc
    (U * Matrix.diagonal w * U.transpose * (U * Matrix.diagonal v * U.transpose) *
        (U * Matrix.diagonal (fun i => (s + a * v i)⁻¹) * U.transpose) *
        (U * Matrix.diagonal (fun i => (u + c * v i)⁻¹) * U.transpose)).trace =
      (U * (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)) * U.transpose).trace := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc U.transpose U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc U.transpose U, hU, Matrix.one_mul,
            ← Matrix.mul_assoc U.transpose U, hU, Matrix.one_mul]
    _ = (Matrix.diagonal w * Matrix.diagonal v *
        Matrix.diagonal (fun i => (s + a * v i)⁻¹) *
        Matrix.diagonal (fun i => (u + c * v i)⁻¹)).trace := by
          rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    _ = _ := by
      simp only [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, div_eq_mul_inv]
      apply Finset.sum_congr rfl
      intro i _
      rw [mul_inv]
      ring

private lemma response_summable_emaW_pow {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {p : ℕ} (hp : 1 ≤ p) : Summable (fun j : ℕ => emaW β j ^ p) := by
  have hr : β ^ p < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
  have heq : (fun j : ℕ => emaW β j ^ p) =
      fun j => (1 - β) ^ p * (β ^ p) ^ j := by
    funext j
    unfold emaW
    rw [mul_pow, pow_right_comm β j p]
  rw [heq]
  exact (summable_geometric_of_lt_one (pow_nonneg hβ0 p) hr).mul_left _

private lemma response_dirac_Icc_compl {a C : ℝ} (ha : a ∈ Icc (0 : ℝ) C) :
    Measure.dirac a (Icc 0 C)ᶜ = 0 := by
  rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
  exact Set.indicator_of_notMem (show a ∉ (Icc (0 : ℝ) C)ᶜ from fun h => h ha) _

private lemma response_branch_nonneg
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {γstar C : ℝ}
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ C) (hC1 : 1 ≤ C)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    {s : ℝ} (hs : 0 < s) :
    0 ≤ (branchSol (Fw (emaW β)) ν ν' s).1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' s).2.1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' s).2.2.1 ∧
      0 ≤ (branchSol (Fw (emaW β)) ν ν' s).2.2.2 := by
  have hgam0 : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hgam : 0 < γstar := hgam0.trans_le hγ
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one hC1
  have hclass : (ν, ν') ∈ classK C γstar := by
    have hd : ∀ i, Measure.dirac (μ i) (Icc 0 C) = 1 := fun i =>
      Measure.dirac_apply_of_mem ⟨(hpos i).le, hμC i⟩
    have hdc : ∀ i, Measure.dirac (μ i) (Icc 0 C)ᶜ = 0 := fun i =>
      response_dirac_Icc_compl ⟨(hpos i).le, hμC i⟩
    have h1mem : (1 : ℝ) ∈ Icc (0 : ℝ) C := ⟨zero_le_one, hC1⟩
    simp only [classK, Set.mem_setOf_eq]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hd, smul_eq_mul,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
      calc
        ENNReal.ofReal ((B : ℝ)⁻¹) * N = ENNReal.ofReal (gammaOf N B) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (inv_nonneg.2 (Nat.cast_nonneg B))]
          congr 1
          unfold gammaOf
          ring
        _ ≤ ENNReal.ofReal γstar := ENNReal.ofReal_le_ofReal hγ
    · rw [hν]
      simp only [Measure.smul_apply, Measure.finsetSum_apply, hdc, smul_eq_mul,
        Finset.sum_const_zero, mul_zero]
    · rw [hν']
      simp only [Measure.smul_apply, Measure.dirac_apply_of_mem h1mem, smul_eq_mul, mul_one]
      exact ENNReal.ofReal_le_ofReal hγ
    · rw [hν', Measure.smul_apply, response_dirac_Icc_compl h1mem, smul_zero]
  have hw : WeightSeq (emaW β) :=
    (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have hsol := branchSol_spec (Fw_admissible hw) hC hgam hclass hs
  exact ⟨hsol.1, hsol.2.1, hsol.2.2.1, hsol.2.2.2.1⟩

/-! ## Statements -/

/-- `prop:app-pl-response`, well-definedness of `b_ℓ, e_ℓ` (not a source claim; needed so that the
`tsum`s of `eqn:app-pl-UV` are the source's series). For `s, s' > 0` and `ℓ ≥ 0`, each term of the two
series is integrable in `g ∼ N(0,1)` and the series of the terms is summable. Snapshot `cr-2026-10-23`.
Proof route: `0 ≤` each integrand is `β^ℓ w_j² g²` resp. `β^{2ℓ} w_j⁴ g⁴` up to a factor `≤ 1`, since
`q(-s), q(-s') ≥ 0` (branch nonnegativity); compare with `sPow β 2`, `sPow β 4` and `∫ g² = ∫ g⁴`-moments.
-/
theorem prop_app_pl_response_summable
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    :
    (∀ j : ℕ, Integrable (fun g : ℝ =>
        β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))) (gaussianReal 0 1)) ∧
    Summable (fun j : ℕ => ∫ g : ℝ,
        β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) ∧
    (∀ j : ℕ, Integrable (fun g : ℝ =>
        β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))) (gaussianReal 0 1)) ∧
    Summable (fun j : ℕ => ∫ g : ℝ,
        β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)) ∂(gaussianReal 0 1)) := by
  have hx := response_branch_nonneg hB hN μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' hs
  have hy := response_branch_nonneg hB hN μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' hs'
  have hq : 0 ≤ respQ β ν ν' s := by
    unfold respQ
    exact mul_nonneg (mul_nonneg hs.le hx.1) hx.2.1
  have hq' : 0 ≤ respQ β ν ν' s' := by
    unfold respQ
    exact mul_nonneg (mul_nonneg hs'.le hy.1) hy.2.1
  have hden : ∀ j g, 1 ≤
      (1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
        (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2) := by
    intro j g
    have h1 : 0 ≤ respQ β ν ν' s * emaW β j ^ 2 * g ^ 2 := by positivity
    have h2 : 0 ≤ β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2 := by
      positivity
    nlinarith [mul_nonneg h1 h2]
  have hb0 : ∀ j g, 0 ≤
      β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)) := by
    intro j g
    exact div_nonneg (by positivity) (zero_le_one.trans (hden j g))
  have hb_le : ∀ j g,
      β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))
        ≤ β ^ ℓ * emaW β j ^ 2 * g ^ 2 := by
    intro j g
    exact div_le_self (by positivity) (hden j g)
  have hbint : ∀ j : ℕ, Integrable (fun g : ℝ =>
      β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)))
      (gaussianReal 0 1) := by
    intro j
    refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 2).const_mul
      (β ^ ℓ * emaW β j ^ 2))
      ((Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb0 j g)]
      exact hb_le j g
  have hbsum : Summable (fun j : ℕ => ∫ g : ℝ,
      β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1)) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg (hb0 j)) (fun j => ?_)
      ((response_summable_emaW_pow hβ0 hβ1 (p := 2) (by norm_num)).mul_left (β ^ ℓ))
    calc
      (∫ g : ℝ, β ^ ℓ * emaW β j ^ 2 * g ^ 2 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))
          ∂(gaussianReal 0 1))
          ≤ ∫ g : ℝ, β ^ ℓ * emaW β j ^ 2 * g ^ 2 ∂(gaussianReal 0 1) :=
            integral_mono (hbint j)
              ((Muon.Foundations.gaussian_integrable_pow 2).const_mul _) (hb_le j)
      _ = β ^ ℓ * emaW β j ^ 2 := by
        rw [integral_const_mul, Muon.Foundations.gaussian_moment_two, mul_one]
  have he0 : ∀ j g, 0 ≤
      β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)) := by
    intro j g
    exact div_nonneg (by positivity) (zero_le_one.trans (hden j g))
  have he_le : ∀ j g,
      β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
          ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
            (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))
        ≤ β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 := by
    intro j g
    exact div_le_self (by positivity) (hden j g)
  have heint : ∀ j : ℕ, Integrable (fun g : ℝ =>
      β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2)))
      (gaussianReal 0 1) := by
    intro j
    refine Integrable.mono' ((Muon.Foundations.gaussian_integrable_pow 4).const_mul
      (β ^ (2 * ℓ) * emaW β j ^ 4))
      ((Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun g => by
      rw [Real.norm_eq_abs, abs_of_nonneg (he0 j g)]
      exact he_le j g
  refine ⟨hbint, hbsum, heint, ?_⟩
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg (he0 j)) (fun j => ?_)
    ((response_summable_emaW_pow hβ0 hβ1 (p := 4) (by norm_num)).mul_left
      (3 * β ^ (2 * ℓ)))
  calc
    (∫ g : ℝ, β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 /
        ((1 + respQ β ν ν' s * emaW β j ^ 2 * g ^ 2) *
          (1 + β ^ (2 * ℓ) * respQ β ν ν' s' * emaW β j ^ 2 * g ^ 2))
        ∂(gaussianReal 0 1))
        ≤ ∫ g : ℝ, β ^ (2 * ℓ) * emaW β j ^ 4 * g ^ 4 ∂(gaussianReal 0 1) :=
          integral_mono (heint j)
            ((Muon.Foundations.gaussian_integrable_pow 4).const_mul _) (he_le j)
    _ = 3 * β ^ (2 * ℓ) * emaW β j ^ 4 := by
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_four]
      ring

/-- `prop:app-pl-response`, part (i), snapshot `cr-2026-10-23`. Declaration of record for
`Δ_ℓ > 0`, for every finite positive spectrum, every `ℓ ≥ 0` and all `s, s' > 0`. The branch is
`Muon.DetEquiv.branchSol` at `(ν, ν')` of the power-law spectrum (hypotheses `hν`, `hν'`); the size
constants satisfy `γ⋆ ≥ γ`, `C_Σ ≥ max(μ_i,1)`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{proposition}[Two-time row response]\label{prop:app-pl-response}
For every finite positive spectrum, every $\ell\ge0$ and all $s,s'>0$, one has
$\Delta_\ell>0$ and
\begin{equation}\label{eqn:app-pl-response}
\mathfrak k_{i,\ell}(s,s')=\frac{\gamma\,ss'\,\mu_i\,b_\ell}{(s+\tilde s_1\mu_i)(s'+\tilde s_1'\mu_i)(s+s_1)(s'+s_1')\,\Delta_\ell}\ \ge0 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_pl_response_i
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    :
    0 < respDelta β B μ ν ν' ℓ s s' := by
  classical
  let i0 : Fin N := ⟨0, hN⟩
  let C : Muon.Covariances N N :=
    { Sout := Matrix.diagonal μ
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun j => (hpos j).le)
      psdIn := Matrix.PosSemidef.diagonal (fun _ => zero_le_one) }
  let Fp : Muon.Setup.FrozenParams N N B :=
    { C := C
      A := Pi.single i0 (Pi.single i0 1)
      hA := by simp [Muon.fro, Pi.single_apply, ite_apply]
      β := β
      hβ := ⟨hβ0, hβ1⟩
      hB := hB }
  let S : Muon.Setup.SpectralData Fp.C :=
    { uOut := 1
      vIn := 1
      μ := μ
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro j
        ext k
        by_cases h : k = j <;> simp [Fp, C, Matrix.mulVec, dotProduct,
          Matrix.diagonal, Matrix.one_apply, h]
      eigIn := by intro j; simp [Fp, C] }
  have hsize : Muon.Volatility.SizeFin Fp.C B γstar CSig := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [gammaOf, div_le_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)] using hγ
    · exact response_diagonal_bound μ CSig (by linarith) (fun j => by
        rw [abs_of_pos (hpos j)]
        exact hμC j)
    · exact response_diagonal_bound (fun _ => 1) CSig (by linarith) (fun _ => by
        simpa using hC1)
  have hCout : Fp.C.Sout = Matrix.diagonal μ := rfl
  have hCin : Fp.C.Sin = 1 := by simp [Fp, C]
  have hνC : (ν : Measure ℝ) = Muon.nuOut Fp.C B := by
    rw [response_nuOut Fp.C μ hB hCout]
    exact hν
  have hν'C : (ν' : Measure ℝ) = Muon.nuIn Fp.C B := by
    rw [response_nuIn Fp.C hB hCin]
    exact hν'
  let Aidx := ℕ ⊕ Fin ℓ
  let P : Measure (Aidx → ℝ) := Measure.infinitePi fun _ : Aidx => gaussianReal 0 1
  let g : Aidx → (Aidx → ℝ) → ℝ := fun a x => x a
  have hg : Muon.Volatility.IsStdGaussianFamily P g := by
    simpa [P, g] using response_stdGaussianFamily Aidx
  have hred := Muon.Volatility.prop_app_vol_closed_reductions_ii
    (P := P) cert γstar CSig Fp S hsize hC1 hCin ℓ hg i0 s s' hs hs'
  have hK : (ν, ν') ∈ Muon.DetEquiv.classK CSig γstar :=
    Muon.Volatility.nu_pair_mem_classK Fp.C γstar CSig hsize hB ν ν' hνC hν'C
  have hbr1 := Muon.Volatility.lem_app_vol_closed_branch_ema
    hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hνC hν'C hK hs
  have hbr2 := Muon.Volatility.lem_app_vol_closed_branch_ema_two
    hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hνC hν'C hK hs'
  have hb1 : Muon.Volatility.branchPt (Fw (emaW β)) Fp.C B s =
      branchSol (Fw (emaW β)) ν ν' s := by
    calc
      _ = Muon.Volatility.branchPt
          (Muon.Volatility.profileF P (Muon.Volatility.emaXi₁ β ℓ g)) Fp.C B s := by
            rw [hbr1.1]
      _ = _ := hbr1.2
  have hb2 : Muon.Volatility.branchPt (Fw (emaW β)) Fp.C B s' =
      branchSol (Fw (emaW β)) ν ν' s' := by
    calc
      _ = Muon.Volatility.branchPt
          (Muon.Volatility.profileF P (Muon.Volatility.emaXi₂ β ℓ g)) Fp.C B s' := by
            rw [hbr2.1]
      _ = _ := hbr2.2
  have hCs : 0 < CSig := lt_of_lt_of_le zero_lt_one hC1
  have hgam0 : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hgam : 0 < γstar := hgam0.trans_le hγ
  have hw : WeightSeq (emaW β) :=
    (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have hx := branchSol_spec (Fw_admissible hw) hCs hgam hK hs
  have hy := branchSol_spec (Fw_admissible hw) hCs hgam hK hs'
  have hto : Muon.Volatility.toutT Fp.C B
      (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s' Fp.C.Sout =
      respU β B μ ν ν' s s' := by
    unfold Muon.Volatility.toutT respU
    rw [response_trace_two_resolvents Fp.C.Sout 1 μ μ (by simp)
      (by simp [Fp, C]) Fp.C.Sout (by simp [Fp, C])]
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro j
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs
        (mul_nonneg hx.2.2.1 (hpos j).le))
    · intro j
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs'
        (mul_nonneg hy.2.2.1 (hpos j).le))
  have hti : Muon.Volatility.tinT Fp.C B
      (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s' Fp.C.Sin =
      respV β B N ν ν' s s' := by
    have ht := hred.2
    unfold Muon.Volatility.emaBr1 Muon.Volatility.emaBr2 at ht
    rw [hbr1.2, hbr2.2] at ht
    simpa [respV, gammaOf] using ht
  have hdelta : Muon.Volatility.profileDelta P Fp.C B
      (Muon.Volatility.emaXi₁ β ℓ g) (Muon.Volatility.emaXi₂ β ℓ g) s s' =
      respDelta β B μ ν ν' ℓ s s' := by
    unfold Muon.Volatility.profileDelta
    rw [hbr1.1, hbr2.1, hb1, hb2]
    change Muon.Volatility.closedDelta Fp.C B
        (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s'
        (Muon.Volatility.pairedB P (Muon.Volatility.emaXi₁ β ℓ g)
          (Muon.Volatility.emaXi₂ β ℓ g) (respQ β ν ν' s) (respQ β ν ν' s'))
        (Muon.Volatility.pairedE P (Muon.Volatility.emaXi₁ β ℓ g)
          (Muon.Volatility.emaXi₂ β ℓ g) (respQ β ν ν' s) (respQ β ν ν' s')) = _
    rw [response_pairedB_eq_emaLagB, response_pairedE_eq_emaLagE,
      response_emaLagB_eq_bLag hg, response_emaLagE_eq_eLag hg]
    simp only [Muon.Volatility.closedDelta, respDelta, hto, hti]
  rw [← hdelta]
  exact (Muon.Volatility.thm_app_vol_closed_kernel_i γstar CSig Fp.C hB hsize hβ0 hβ1 ℓ hg s s' hs hs').1

/-- `prop:app-pl-response`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for the identity
`𝔨_{i,ℓ}(s,s') = γ s s' μ_i b_ℓ / ((s+s̃₁μ_i)(s'+s̃₁'μ_i)(s+s₁)(s'+s₁')Δ_ℓ)`, where the left side is
the row kernel `eqn:app-pl-rowkernel`, `B 𝔨_ℓ[u_i ⊗ u_i, Id_N](s,s')`, of D's lag kernel `lagResp`
(`Σ_in = Id`: input eigenvalues `1`, input test `Id`; `u_i ⊗ u_i` = `Pi.single i 1`). Snapshot
`cr-2026-10-23`. LaTeX of the row kernel, verbatim (`eqn:app-pl-rowkernel`):

```latex
\begin{equation}\label{eqn:app-pl-rowkernel}
\mathfrak k_{i,\ell}(s,s')\defeq B\,\mathfrak k_\ell[u_i\tensor u_i,\Id_N](s,s')\qquad(s,s'>0).
\end{equation}
```

and of the proposition, verbatim from `section.tex` (the whole environment):

```latex
\begin{proposition}[Two-time row response]\label{prop:app-pl-response}
For every finite positive spectrum, every $\ell\ge0$ and all $s,s'>0$, one has
$\Delta_\ell>0$ and
\begin{equation}\label{eqn:app-pl-response}
\mathfrak k_{i,\ell}(s,s')=\frac{\gamma\,ss'\,\mu_i\,b_\ell}{(s+\tilde s_1\mu_i)(s'+\tilde s_1'\mu_i)(s+s_1)(s'+s_1')\,\Delta_\ell}\ \ge0 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_pl_response_ii
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (i : Fin N) :
    (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Muon.Volatility.iotaF s) (Muon.Volatility.iotaF s') =
      respRHS β B μ ν ν' ℓ i s s' := by
  classical
  let C : Muon.Covariances N N :=
    { Sout := Matrix.diagonal μ
      Sin := Matrix.diagonal (fun _ => 1)
      psdOut := Matrix.PosSemidef.diagonal (fun j => (hpos j).le)
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
      μ := μ
      lam := fun _ => 1
      huOut := by simp
      hvIn := by simp
      eigOut := by
        intro j
        ext k
        by_cases h : k = j <;> simp [Fp, C, Matrix.mulVec, dotProduct,
          Matrix.diagonal, Matrix.one_apply, h]
      eigIn := by intro j; simp [Fp, C] }
  have hsize : Muon.Volatility.SizeFin Fp.C B γstar CSig := by
    refine ⟨?_, ?_, ?_⟩
    · simpa [gammaOf, div_le_iff₀ (show (0 : ℝ) < B by exact_mod_cast hB)] using hγ
    · exact response_diagonal_bound μ CSig (by linarith) (fun j => by
        rw [abs_of_pos (hpos j)]
        exact hμC j)
    · exact response_diagonal_bound (fun _ => 1) CSig (by linarith) (fun _ => by
        simpa using hC1)
  have hCout : Fp.C.Sout = Matrix.diagonal μ := rfl
  have hCin : Fp.C.Sin = 1 := by simp [Fp, C]
  have hνC : (ν : Measure ℝ) = Muon.nuOut Fp.C B := by
    rw [response_nuOut Fp.C μ hB hCout]
    exact hν
  have hν'C : (ν' : Measure ℝ) = Muon.nuIn Fp.C B := by
    rw [response_nuIn Fp.C hB hCin]
    exact hν'
  let Aidx := ℕ ⊕ Fin ℓ
  let P : Measure (Aidx → ℝ) := Measure.infinitePi fun _ : Aidx => gaussianReal 0 1
  let g : Aidx → (Aidx → ℝ) → ℝ := fun a x => x a
  have hg : Muon.Volatility.IsStdGaussianFamily P g := by
    simpa [P, g] using response_stdGaussianFamily Aidx
  have hred := Muon.Volatility.prop_app_vol_closed_reductions_ii
    (P := P) cert γstar CSig Fp S hsize hC1 hCin ℓ hg i s s' hs hs'
  have hK : (ν, ν') ∈ Muon.DetEquiv.classK CSig γstar :=
    Muon.Volatility.nu_pair_mem_classK Fp.C γstar CSig hsize hB ν ν' hνC hν'C
  have hbr1 := Muon.Volatility.lem_app_vol_closed_branch_ema
    hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hνC hν'C hK hs
  have hbr2 := Muon.Volatility.lem_app_vol_closed_branch_ema_two
    hB hβ0 hβ1 hg Fp.C CSig γstar ν ν' hνC hν'C hK hs'
  have hb1 : Muon.Volatility.branchPt (Fw (emaW β)) Fp.C B s =
      branchSol (Fw (emaW β)) ν ν' s := by
    calc
      _ = Muon.Volatility.branchPt
          (Muon.Volatility.profileF P (Muon.Volatility.emaXi₁ β ℓ g)) Fp.C B s := by
            rw [hbr1.1]
      _ = _ := hbr1.2
  have hb2 : Muon.Volatility.branchPt (Fw (emaW β)) Fp.C B s' =
      branchSol (Fw (emaW β)) ν ν' s' := by
    calc
      _ = Muon.Volatility.branchPt
          (Muon.Volatility.profileF P (Muon.Volatility.emaXi₂ β ℓ g)) Fp.C B s' := by
            rw [hbr2.1]
      _ = _ := hbr2.2
  have hCs : 0 < CSig := lt_of_lt_of_le zero_lt_one hC1
  have hgam0 : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hgam : 0 < γstar := hgam0.trans_le hγ
  have hw : WeightSeq (emaW β) :=
    (Muon.Drift.emaW_weightClass β ⟨hβ0, hβ1⟩).1
  have hx := branchSol_spec (Fw_admissible hw) hCs hgam hK hs
  have hy := branchSol_spec (Fw_admissible hw) hCs hgam hK hs'
  have hto : Muon.Volatility.toutT Fp.C B
      (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s' Fp.C.Sout =
      respU β B μ ν ν' s s' := by
    unfold Muon.Volatility.toutT respU
    rw [response_trace_two_resolvents Fp.C.Sout 1 μ μ (by simp)
      (by simp [Fp, C]) Fp.C.Sout (by simp [Fp, C])]
    · congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    · intro j
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs
        (mul_nonneg hx.2.2.1 (hpos j).le))
    · intro j
      exact ne_of_gt (add_pos_of_pos_of_nonneg hs'
        (mul_nonneg hy.2.2.1 (hpos j).le))
  have hti : Muon.Volatility.tinT Fp.C B
      (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s' Fp.C.Sin =
      respV β B N ν ν' s s' := by
    have ht := hred.2
    unfold Muon.Volatility.emaBr1 Muon.Volatility.emaBr2 at ht
    rw [hbr1.2, hbr2.2] at ht
    simpa [respV, gammaOf] using ht
  have hdelta : Muon.Volatility.profileDelta P Fp.C B
      (Muon.Volatility.emaXi₁ β ℓ g) (Muon.Volatility.emaXi₂ β ℓ g) s s' =
      respDelta β B μ ν ν' ℓ s s' := by
    unfold Muon.Volatility.profileDelta
    rw [hbr1.1, hbr2.1, hb1, hb2]
    change Muon.Volatility.closedDelta Fp.C B
        (branchSol (Fw (emaW β)) ν ν' s) (branchSol (Fw (emaW β)) ν ν' s') s s'
        (Muon.Volatility.pairedB P (Muon.Volatility.emaXi₁ β ℓ g)
          (Muon.Volatility.emaXi₂ β ℓ g) (respQ β ν ν' s) (respQ β ν ν' s'))
        (Muon.Volatility.pairedE P (Muon.Volatility.emaXi₁ β ℓ g)
          (Muon.Volatility.emaXi₂ β ℓ g) (respQ β ν ν' s) (respQ β ν ν' s')) = _
    rw [response_pairedB_eq_emaLagB, response_pairedE_eq_emaLagE,
      response_emaLagB_eq_bLag hg, response_emaLagE_eq_eLag hg]
    simp only [Muon.Volatility.closedDelta, respDelta, hto, hti]
  unfold Muon.Volatility.emaBr1 Muon.Volatility.emaBr2 at hred
  rw [hbr1.2, hbr2.2, response_emaLagB_eq_bLag hg, hdelta] at hred
  simpa [Fp, S, C, respRHS, gammaOf, respQ] using hred.1

/-- `prop:app-pl-response`, part (iii), snapshot `cr-2026-10-23`. Declaration of record for the
nonnegativity `≥ 0` of the common value in `eqn:app-pl-response`: both the right-hand side (formula) and
the row kernel `B 𝔨_ℓ[u_i ⊗ u_i, Id_N](s,s')` are nonnegative. Snapshot `cr-2026-10-23`. LaTeX, verbatim
from `section.tex` (the whole environment):

```latex
\begin{proposition}[Two-time row response]\label{prop:app-pl-response}
For every finite positive spectrum, every $\ell\ge0$ and all $s,s'>0$, one has
$\Delta_\ell>0$ and
\begin{equation}\label{eqn:app-pl-response}
\mathfrak k_{i,\ell}(s,s')=\frac{\gamma\,ss'\,\mu_i\,b_\ell}{(s+\tilde s_1\mu_i)(s'+\tilde s_1'\mu_i)(s+s_1)(s'+s_1')\,\Delta_\ell}\ \ge0 .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_pl_response_iii
    (cert : Muon.External.GaussianOpNorm) (γstar CSig : ℝ)
    {N B : ℕ} (hB : 0 < B) (hN : 0 < N) (μ : Fin N → ℝ) (hpos : ∀ i, 0 < μ i)
    {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hγ : gammaOf N B ≤ γstar) (hμC : ∀ i, μ i ≤ CSig) (hC1 : 1 ≤ CSig)
    {ν ν' : FiniteMeasure ℝ}
    (hν : (ν : Measure ℝ) = ENNReal.ofReal ((B : ℝ)⁻¹) • ∑ i, Measure.dirac (μ i))
    (hν' : (ν' : Measure ℝ) = ENNReal.ofReal (gammaOf N B) • Measure.dirac (1 : ℝ))
    (ℓ : ℕ) {s s' : ℝ} (hs : 0 < s) (hs' : 0 < s')
    (i : Fin N) :
    0 ≤ respRHS β B μ ν ν' ℓ i s s' ∧
    0 ≤ (B : ℝ) * Muon.Volatility.lagResp cert γstar CSig β ℓ B μ (fun _ : Fin N => (1 : ℝ))
        (Pi.single i (1 : ℝ)) (fun _ : Fin N => (1 : ℝ))
        (Muon.Volatility.iotaF s) (Muon.Volatility.iotaF s') := by
  have hx := response_branch_nonneg hB hN μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' hs
  have hy := response_branch_nonneg hB hN μ hpos hβ0 hβ1 hγ hμC hC1 hν hν' hs'
  have hq : 0 ≤ respQ β ν ν' s := by
    unfold respQ
    exact mul_nonneg (mul_nonneg hs.le hx.1) hx.2.1
  have hq' : 0 ≤ respQ β ν ν' s' := by
    unfold respQ
    exact mul_nonneg (mul_nonneg hs'.le hy.1) hy.2.1
  have hb : 0 ≤ bLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ := by
    unfold bLag
    apply tsum_nonneg
    intro j
    apply integral_nonneg
    intro g
    positivity
  have hgam : 0 < gammaOf N B := by
    unfold gammaOf
    exact div_pos (by exact_mod_cast hN) (by exact_mod_cast hB)
  have hd1 : 0 < s + (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ i :=
    add_pos_of_pos_of_nonneg hs (mul_nonneg hx.2.2.1 (hpos i).le)
  have hd2 : 0 < s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.1 * μ i :=
    add_pos_of_pos_of_nonneg hs' (mul_nonneg hy.2.2.1 (hpos i).le)
  have hd3 : 0 < s + (branchSol (Fw (emaW β)) ν ν' s).2.2.2 :=
    add_pos_of_pos_of_nonneg hs hx.2.2.2
  have hd4 : 0 < s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.2 :=
    add_pos_of_pos_of_nonneg hs' hy.2.2.2
  have hdelta : 0 < respDelta β B μ ν ν' ℓ s s' :=
    prop_app_pl_response_i cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1
      hν hν' ℓ hs hs'
  have hrhs : 0 ≤ respRHS β B μ ν ν' ℓ i s s' := by
    unfold respRHS
    have hnum : 0 ≤ gammaOf N B * s * s' * μ i *
        bLag β (respQ β ν ν' s) (respQ β ν ν' s') ℓ :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hgam.le hs.le) hs'.le) (hpos i).le) hb
    have hden : 0 ≤
        (s + (branchSol (Fw (emaW β)) ν ν' s).2.2.1 * μ i) *
          (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.1 * μ i) *
          (s + (branchSol (Fw (emaW β)) ν ν' s).2.2.2) *
          (s' + (branchSol (Fw (emaW β)) ν ν' s').2.2.2) *
          respDelta β B μ ν ν' ℓ s s' :=
      (mul_pos (mul_pos (mul_pos (mul_pos hd1 hd2) hd3) hd4) hdelta).le
    exact div_nonneg hnum hden
  refine ⟨hrhs, ?_⟩
  rw [prop_app_pl_response_ii cert γstar CSig hB hN μ hpos hβ0 hβ1 hγ hμC hC1
    hν hν' ℓ hs hs' i]
  exact hrhs

end Muon.PowerLaw

end
