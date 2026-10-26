import Mathlib
import Muon.SignSGD.Isotropic
import Muon.SignSGD.HaarTools
import Muon.Foundations.OrthHaar
import Muon.Foundations.SphereGaussian

/-!
# Appendix I (SignSGD): whitening, deletion and the half-anisotropic drift (task L-I.9)

Interface for work package L-I.9 (card `sections/08-signsgd/CARD.md` §3 rows 18–22, §3b rows 820–825,
§5 row L-I.9). Source of record: snapshot `cr-2026-10-23`, `sections/08-signsgd/section.tex`. Labels:
`lem:app-sgd-whitening` (l. 791–804), `lem:app-sgd-deletion` (l. 827–838),
`prop:app-sgd-coordinate-sum` (l. 850–856), `thm:app-sgd-half-drift` (l. 899–911),
`cor:app-sgd-half-pairings` (l. 950–959), and the unlabeled Haar forms (l. 820–825).
Docstrings carry the LaTeX statements verbatim (copied by script from `section.tex`).

Choices:
* Haar measure: a probability `ν` on `O(n)` with `Muon.Foundations.IsOrthHaar ν` (coordinator Q1).
  Expectations over `U` are integrals against `ν`; joint expectations over `(U, batch)` use
  `ν.prod (batchLaw …)`.
* Whitened batch (coordinator Q2): `Xout = U Λ^{1/2} z`, `Xin = w`, with `(z, w)` i.i.d. standard
  Gaussian (`gaussBatch`); the batch law is `Measure.pi` of `gaussBatch` (`batchLaw`). The state is
  `Σout = U Λ Uᵀ`, `Σin = Id`, `Δ = U D` (`Muon.SignSGD.haarSigmaOut`, `haarDelta`).
* Standing hypotheses `0 < c ≤ L`, `0 < f₋ ≤ f₊`, `C_col > 0`, `K ≥ 1` are the fields of
  `HaarParams`; `2 ≤ k` and the bounds of `def:app-sgd-state-law` are `def_app_sgd_state_law`.
* Admissible constants: `∀ P : HaarParams, ∃ C, 0 ≤ C, ∀ n m B μ D ν, …`. The constant depends on `P`
  only and is chosen before all dimensions, the state and the Haar measure.
* Squared-norm expectations are `∫⁻` of `ENNReal.ofReal`, so no Bochner junk value can satisfy a bound.
* The "in particular" relative-error bound of `thm:app-sgd-half-drift` is stated in squared form,
  `E‖X‖² ≤ (C/(b₋B))‖L_BΛD‖²_F`, which is equivalent to `‖X‖_{L²}/‖L_BΛD‖_F ≤ √(C/(b₋B))`.
* `Muon.pairSigma` needs a `Covariances` value. Its `Σin = Id` specialisation `Tr(Σ V Wᵀ)` is written
  as `pairIdIn`; `riskTwo Σ Δ = pairIdIn Σ Δ Δ` is `2ℛ = ‖Δ‖²_Σ`.
* The Haar coordinate `𝒬_i(Δ)` of the row drift is written as `Σ_j D_{ij}²`, which the Haar forms
  identify with `‖Δᵀu_i‖²` (l. 620–621; conjunct 6 of `haar_forms_app_sgd`).
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder
open Muon.Foundations

namespace Muon.SignSGD

/-! ## Shared objects of a state `(Σ, Δ)` -/

/-- The Σ-pairing `Tr(Σ V Wᵀ)`: `Muon.pairSigma` (`eqn:app-setup-pairing`) at `Σin = Id`. -/
noncomputable def pairIdIn {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ)
    (V W : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  (Sg * V * Wᵀ).trace

/-- `2ℛ = ‖Δ‖²_Σ = Tr(Σ Δ Δᵀ)` (`eqn:app-setup-risk-trace` at `Σin = Id`). -/
noncomputable def riskTwo {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  pairIdIn Sg Δ Δ

/-- `μ_pj = (ΣΔ)_pj / √Σ_pp` (`eqn:app-sgd-whitened-entries`, l. 788). -/
noncomputable def whMu {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (p : Fin n) (j : Fin m) : ℝ :=
  (Sg * Δ) p j / Real.sqrt (Sg p p)

/-- `R_p = ‖(ΣΔ)_{p·}‖² / Σ_pp` (`eqn:app-sgd-whitened-entries`, l. 788). -/
noncomputable def whR {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (p : Fin n) : ℝ :=
  (∑ j, (Sg * Δ) p j ^ 2) / Sg p p

/-- `C_j = Δ_{·j}ᵀ Σ Δ_{·j}` (`eqn:app-sgd-whitened-entries`, l. 788). -/
noncomputable def whC {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (j : Fin m) : ℝ :=
  ∑ k, ∑ l, Δ k j * Sg k l * Δ l j

/-- The whitened state `A = Qᵀ Σ^{1/2} Δ` of `lem:app-sgd-whitening` (l. 791–795). -/
noncomputable def whitenedState {n m : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  Qᵀ * CFC.sqrt Sg * Δ

/-! ## Batches and the Haar model -/

/-- The batch with `Xin = w` and `Xout = M z`, from a whitened batch `β = (z_a, w_a)_a`. -/
noncomputable def linBatch {n m B : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) : Batch n m B :=
  { xin := fun a => (β a).2
    xout := fun a => Matrix.mulVec M (β a).1 }

/-- The Haar-model batch `Xout = U Λ^{1/2} z`, `Xin = w` (`def:app-sgd-state-law`, l. 626–628;
coordinator ruling Q2). -/
noncomputable def haarBatch {n m B : ℕ} (μ : Fin n → ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) : Batch n m B :=
  linBatch ((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (fun k => Real.sqrt (μ k))) β

/-- The law of `B` i.i.d. whitened pairs `(z_a, w_a)`, each with law `gaussBatch n m`. -/
noncomputable def batchLaw (n m B : ℕ) : Measure (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :=
  Measure.pi fun _ : Fin B => gaussBatch n m

/-- The one-step sign matrix `S = sign(G°)` of `def:app-sgd-update` in the Haar model. -/
noncomputable def haarSign {n m B : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (β : Fin B → (Fin n → ℝ) × (Fin m → ℝ)) :
    Matrix (Fin n) (Fin m) ℝ :=
  (physGrad (haarDelta U D) (haarBatch μ U β)).map Real.sign

/-- `M(U) = E[S | U]`, the batch mean given the eigenbasis (l. 640), as an integral over the batch. -/
noncomputable def haarMean {n m : ℕ} (B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  fun p j => ∫ β, haarSign μ D U β p j ∂(batchLaw n m B)

/-- `μ_pj` in the Haar model (`whMu` at `Σout = UΛUᵀ`, `Δ = UD`). -/
noncomputable def haarMu {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) (j : Fin m) : ℝ :=
  whMu (haarSigmaOut U μ) (haarDelta U D) p j

/-- `R_p` in the Haar model (`whR` at `Σout = UΛUᵀ`, `Δ = UD`). -/
noncomputable def haarR {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) : ℝ :=
  whR (haarSigmaOut U μ) (haarDelta U D) p

/-- `C_j` in the Haar model (`whC` at `Σout = UΛUᵀ`, `Δ = UD`). -/
noncomputable def haarC {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (j : Fin m) : ℝ :=
  whC (haarSigmaOut U μ) (haarDelta U D) j

/-- The eigenvector `u_i = U e_i` as a vector (`l. 620`). -/
noncomputable def haarCol {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) :
    Fin n → ℝ :=
  fun k => (U : Matrix (Fin n) (Fin n) ℝ) k i

/-- The coordinate error `E = M(U) − √(2/π) 𝒩_B (2ℛ)^{-1/2} D_v^{-1/2} U Λ D` of
`prop:app-sgd-coordinate-sum` (l. 853). -/
noncomputable def haarErr {n m : ℕ} (B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  haarMean B μ D U - (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
    (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹) *
      (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)

/-- The drift error `U^T M(U) − L_B Λ D` of `thm:app-sgd-half-drift` (l. 904). -/
noncomputable def haarDriftErr {n m : ℕ} (B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin m) ℝ :=
  (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarMean B μ D U - LB B μ D • (Matrix.diagonal μ * D)

/-! ## Constants of the Haar model -/

/-- `k_* = max{4, ⌈4 A₂ / P₋⌉}` (l. 827–833). -/
noncomputable def haarKStar (P : HaarParams) : ℕ :=
  max 4 ⌈4 * haarA2 P / haarPminus P⌉₊

/-- `Q₀ = 105 (4 A₀ / P₋)⁴` (l. 829). -/
noncomputable def haarQ0 (P : HaarParams) : ℝ :=
  105 * (4 * haarA0 P / haarPminus P) ^ 4

/-- `b₋ = 8 c² f₋² / (π³ L² f₊²)` (`eqn:app-sgd-half-leading`, l. 905). -/
noncomputable def haarBminus (P : HaarParams) : ℝ :=
  8 * P.c ^ 2 * P.fMin ^ 2 / (Real.pi ^ 3 * P.L ^ 2 * P.fMax ^ 2)

/-- `b₊ = 2 L² f₊² / (π c² f₋²)` (`eqn:app-sgd-half-leading`, l. 905). -/
noncomputable def haarBplus (P : HaarParams) : ℝ :=
  2 * P.L ^ 2 * P.fMax ^ 2 / (Real.pi * P.c ^ 2 * P.fMin ^ 2)

/-- `d₋ = 2 √(2/π) c² f₋² / (π L f₊)` (`cor:app-sgd-half-pairings`, l. 957). -/
noncomputable def haarDminus (P : HaarParams) : ℝ :=
  2 * Real.sqrt (2 / Real.pi) * P.c ^ 2 * P.fMin ^ 2 / (Real.pi * P.L * P.fMax)

/-! ## Haar forms (unlabeled, §3b rows 820–825)

Source `section.tex` l. 820–825 (verbatim):
```latex
In the Haar model, $\Sigma\Delta=U\Lambda D$. Write $\omega_p\defeq U^\T e_p$
for the $p$th row of $U$, a uniform unit vector, so that
\[
v_p=\omega_p^\T\Lambda\omega_p\in[c,L],\qquad \mu_{pj}=\frac{\omega_p^\T\Lambda D_{\cdot j}}{\sqrt{v_p}},\qquad R_p=\frac{\omega_p^\T T_D\omega_p}{v_p},\qquad C_j=D_{\cdot j}^\T\Lambda D_{\cdot j}\le\frac{A_2}k .
\]
The last quantity is deterministic.
``` -/

/-- Haar forms of `v_p`, `μ_pj`, `R_p`, `C_j` and `𝒬_i`, with `C_j ≤ A₂/k` (unlabeled, l. 820–825;
card §3b row 820–825, WP L-I.9). Proof route: algebra over `ω_p = Uᵀ e_p` (row `p` of `U`). -/
theorem haar_forms_app_sgd {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) (j : Fin m) (i : Fin n) :
    riskTwo (haarSigmaOut U μ) (haarDelta U D) = twoR μ D ∧
    haarSigmaOut U μ p p = ∑ k, μ k * (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 ∧
    (P.c ≤ haarSigmaOut U μ p p ∧ haarSigmaOut U μ p p ≤ P.L) ∧
    haarMu μ D U p j
      = (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k j)
        / Real.sqrt (haarSigmaOut U μ p p) ∧
    haarR μ D U p
      = (∑ l, (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k l) ^ 2)
        / haarSigmaOut U μ p p ∧
    haarC μ D U j = ∑ k, μ k * D k j ^ 2 ∧
    haarC μ D U j ≤ haarA2 P / ((kOf n m B : ℕ) : ℝ) ∧
    ∑ k, (Matrix.mulVec (haarDelta U D)ᵀ (haarCol U i)) k ^ 2 = ∑ l, D i l ^ 2 := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hUU : (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 U.2
  have hst := hstate
  unfold def_app_sgd_state_law at hst
  obtain ⟨-, -, -, -, -, hmu, -, -, hcol⟩ := hst
  have hcol' : ∀ j, ∑ i, D i j ^ 2 ≤ P.Ccol / ((kOf n m B : ℕ) : ℝ) := hcol
  have hSD : haarSigmaOut U μ * haarDelta U D = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D := by
    unfold haarSigmaOut haarDelta
    have h : (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * ((U : Matrix (Fin n) (Fin n) ℝ) * D)
        = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ)) * D := by
      simp only [Matrix.mul_assoc]
    rw [h, hUt, Matrix.mul_one]
  have hSpp : haarSigmaOut U μ p p = ∑ k, μ k * (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 := by
    unfold haarSigmaOut
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal, Matrix.transpose_apply]
    ring
  have hEnt : ∀ l, ((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p l = ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k l := by
    intro l
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_diagonal]
  have hrow : ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 = 1 := by
    have h := congrFun (congrFun hUU p) p
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
    simpa [sq] using h
  have hlo : P.c ≤ haarSigmaOut U μ p p := by
    rw [hSpp]
    calc P.c = ∑ k, P.c * (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 := by
          rw [← Finset.mul_sum, hrow, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hmu k).1 (sq_nonneg _)
  have hup : haarSigmaOut U μ p p ≤ P.L := by
    rw [hSpp]
    calc _ ≤ ∑ k, P.L * (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hmu k).2 (sq_nonneg _)
      _ = P.L := by rw [← Finset.mul_sum, hrow, mul_one]
  have hmuEq : haarMu μ D U p j = (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k j)
      / Real.sqrt (haarSigmaOut U μ p p) := by
    unfold haarMu whMu
    rw [hSD, hEnt j]
  have hRq : haarR μ D U p = (∑ l, (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k l) ^ 2)
      / haarSigmaOut U μ p p := by
    unfold haarR whR
    rw [hSD]
    simp only [hEnt]
  have hMat : (haarDelta U D)ᵀ * haarSigmaOut U μ * haarDelta U D
      = Dᵀ * Matrix.diagonal μ * D := by
    have e : (haarDelta U D)ᵀ * haarSigmaOut U μ * haarDelta U D
        = (haarDelta U D)ᵀ * (haarSigmaOut U μ * haarDelta U D) := Matrix.mul_assoc _ _ _
    rw [e, hSD]
    unfold haarDelta
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  have hC' : ∀ j, whC (haarSigmaOut U μ) (haarDelta U D) j
      = ((haarDelta U D)ᵀ * haarSigmaOut U μ * haarDelta U D) j j := by
    intro j
    simp only [whC, Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hC : haarC μ D U j = ∑ k, μ k * D k j ^ 2 := by
    unfold haarC
    rw [hC' j, hMat, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hC7 : haarC μ D U j ≤ haarA2 P / ((kOf n m B : ℕ) : ℝ) := by
    rw [hC]
    calc ∑ k, μ k * D k j ^ 2 ≤ ∑ k, P.L * D k j ^ 2 :=
          Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hmu k).2 (sq_nonneg _)
      _ = P.L * ∑ k, D k j ^ 2 := by rw [Finset.mul_sum]
      _ ≤ P.L * (P.Ccol / ((kOf n m B : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left (hcol' j) (le_trans P.c_pos.le P.c_le_L)
      _ = haarA2 P / ((kOf n m B : ℕ) : ℝ) := by unfold haarA2; ring
  have hDA : (haarDelta U D)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = Dᵀ := by
    unfold haarDelta
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hUt, Matrix.mul_one]
  have hv : Matrix.mulVec (haarDelta U D)ᵀ (haarCol U i) = fun k => D i k := by
    funext k
    have h := congrFun (congrFun hDA k) i
    rw [Matrix.mul_apply] at h
    simpa [Matrix.mulVec, dotProduct, haarCol, Matrix.transpose_apply] using h
  have h1 : riskTwo (haarSigmaOut U μ) (haarDelta U D) = twoR μ D := by
    unfold riskTwo pairIdIn twoR
    rw [hSD]
    unfold haarDelta
    rw [Matrix.transpose_mul]
    have hT : (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D * (Dᵀ * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ)
        = (U : Matrix (Fin n) (Fin n) ℝ) * (Matrix.diagonal μ * (D * Dᵀ)) * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
      simp only [Matrix.mul_assoc]
    rw [hT, Matrix.trace_mul_comm, ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  refine ⟨h1, hSpp, ⟨hlo, hup⟩, hmuEq, hRq, hC, hC7, ?_⟩
  rw [hv]

/-! ## `lem:app-sgd-whitening` -/

/-! ### Private helpers for `lem:app-sgd-whitening` -/

private lemma aux_S_symm {n : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) :
    (CFC.sqrt Sg)ᵀ = CFC.sqrt Sg := by
  have h : (CFC.sqrt Sg)ᴴ = CFC.sqrt Sg :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Sg)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma aux_S_mul_self {n : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) (hSg : Sg.PosSemidef) :
    CFC.sqrt Sg * CFC.sqrt Sg = Sg :=
  CFC.sqrt_mul_sqrt_self Sg (Matrix.nonneg_iff_posSemidef.mpr hSg)

private lemma aux_Q_comm {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1) :
    Q * Qᵀ = 1 :=
  mul_eq_one_comm.mp hQ

private lemma aux_sum_sq_eq_trace {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) :
    ∑ i, ∑ l, X i l ^ 2 = (X * Xᵀ).trace := by
  simp [Matrix.trace, Matrix.mul_apply, sq]

private lemma aux_trace_conj {n : ℕ} (Q X : Matrix (Fin n) (Fin n) ℝ) (hQQ : Q * Qᵀ = 1) :
    (Qᵀ * X * Q).trace = X.trace := by
  rw [Matrix.trace_mul_comm (Qᵀ * X) Q, ← Matrix.mul_assoc, hQQ, Matrix.one_mul]

private lemma aux_deleted_sum {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) (j : Fin m) :
    ∑ k, ∑ l, sgdDeletedBlock X i j k l ^ 2
      = ∑ k, ∑ l, X k l ^ 2 - ∑ l, X i l ^ 2 - ∑ k, X k j ^ 2 + X i j ^ 2 := by
  have hpt : ∀ k l, sgdDeletedBlock X i j k l ^ 2 = X k l ^ 2 - (if k = i then X k l ^ 2 else 0)
      - (if l = j then X k l ^ 2 else 0)
      + (if k = i then (if l = j then X k l ^ 2 else 0) else 0) := by
    intro k l
    unfold sgdDeletedBlock
    by_cases hk : k = i <;> by_cases hl : l = j <;> simp [hk, hl]
  simp only [hpt, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp [Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.sum_ite_eq]

private lemma aux_sign_pos_mul (c x : ℝ) (hc : 0 < c) : Real.sign (c * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with h | h | h
  · rw [Real.sign_of_neg h, Real.sign_of_neg (mul_neg_of_pos_of_neg hc h)]
  · simp [h]
  · rw [Real.sign_of_pos h, Real.sign_of_pos (mul_pos hc h)]

private lemma aux_orth_dot {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQQ : Q * Qᵀ = 1)
    (z u : Fin n → ℝ) : (Qᵀ *ᵥ z) ⬝ᵥ (Qᵀ *ᵥ u) = z ⬝ᵥ u := by
  have h : (Qᵀ)ᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]
    exact hQQ
  rw [← Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h,
    Matrix.vecMul_one]

private lemma aux_dot_sym {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : Sᵀ = S)
    (z v : Fin n → ℝ) : z ⬝ᵥ (S *ᵥ v) = (S *ᵥ z) ⬝ᵥ v := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS]

private lemma aux_sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

/-- Part (i) of `lem:app-sgd-whitening`: the law of `sign(G°_pj)` equals the law of
`sign(G^A_{1j})` (`CFC.sqrt` is `Σ^{1/2}`; index `1` is `⟨0, hN⟩`). cr-2026-10-23. Source `section.tex` l. 791-804. LaTeX statement (verbatim):
```latex
\begin{lemma}[Whitening a coordinate]\label{lem:app-sgd-whitening}
Let $Q$ be orthogonal with first column $\Sigma^{1/2}e_p/\sqrt{v_p}$ and put
$A\defeq Q^\T\Sigma^{1/2}\Delta$. Then $\norm A_\F^2=2\cR$, the entry
$A_{1j}$ equals $\mu_{pj}$, row $1$ of $A$ has squared norm $R_p$, column $j$
of $A$ has squared norm $C_j$, and $\sign(G^\circ_{pj})$ has the law of
$\sign(G^A_{1j})$, where $G^A$ is the isotropic gradient of the state $A$.
In particular \cref{prop:app-sgd-coordinate} applies to $(p,j)$ with $F^2=2\cR$,
$\Delta_{ij}$ replaced by $\mu_{pj}$, and
$\norm{\bar A}_\F^2=2\cR-R_p-C_j+\mu_{pj}^2$, whenever this is at least
$\cR/2$ and $B\ge4$; its comparison term is
\[
\sqrt{\frac2\pi}\,\mathcal N_B\frac{\mu_{pj}}{\sqrt{2\cR}}=\frac{\mathcal N_B\,(\Sigma\Delta)_{pj}}{\sqrt{\pi\cR\,v_p}} .
\]
\end{lemma}
``` -/
theorem lem_app_sgd_whitening_i {n m B : ℕ} (hN : 0 < n) (Sg : Matrix (Fin n) (Fin n) ℝ)
    (hSg : Sg.PosSemidef) (Δ : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (hp : 0 < Sg p p)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hQc : ∀ k, Q k ⟨0, hN⟩ = CFC.sqrt Sg k p / Real.sqrt (Sg p p)) (j : Fin m) :
    (batchLaw n m B).map (fun β => Real.sign (physGrad Δ (linBatch (CFC.sqrt Sg) β) p j))
      = (batchLaw n m B).map (fun β =>
          Real.sign (physGrad (whitenedState Sg Δ Q)
            (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) β) ⟨0, hN⟩ j)) := by
  have hSym := aux_S_symm Sg
  have hSS := aux_S_mul_self Sg hSg
  have hQQ := aux_Q_comm Q hQ
  have hpos : 0 < Real.sqrt (Sg p p) := Real.sqrt_pos.mpr hp
  -- `(Σ^{1/2} z)_p = √Σ_pp · (Qᵀ z)_0`, from the first column of `Q`
  have hcol : ∀ z : Fin n → ℝ,
      (CFC.sqrt Sg *ᵥ z) p = Real.sqrt (Sg p p) * (Qᵀ *ᵥ z) ⟨0, hN⟩ := by
    intro z
    have hSk : ∀ k l, CFC.sqrt Sg k l = CFC.sqrt Sg l k := fun k l => by
      have h := congrFun (congrFun hSym l) k
      simpa [Matrix.transpose_apply] using h
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    rw [hQc k, hSk k p]
    field_simp
  have hAw : ∀ w : Fin m → ℝ,
      whitenedState Sg Δ Q *ᵥ w = Qᵀ *ᵥ (CFC.sqrt Sg *ᵥ (Δ *ᵥ w)) := by
    intro w
    simp only [whitenedState, ← Matrix.mulVec_mulVec]
  have hres : ∀ (z : Fin n → ℝ) (w : Fin m → ℝ),
      (CFC.sqrt Sg *ᵥ z) ⬝ᵥ (Δ *ᵥ w) = (Qᵀ *ᵥ z) ⬝ᵥ (whitenedState Sg Δ Q *ᵥ w) := by
    intro z w
    rw [hAw, aux_orth_dot Q hQQ, aux_dot_sym _ hSym]
  -- pointwise identity: the physical gradients differ by the positive factor `√Σ_pp`
  have hphys : ∀ β : Fin B → (Fin n → ℝ) × (Fin m → ℝ),
      physGrad Δ (linBatch (CFC.sqrt Sg) β) p j
        = Real.sqrt (Sg p p) * physGrad (whitenedState Sg Δ Q)
            (linBatch (1 : Matrix (Fin n) (Fin n) ℝ)
              (fun a => (Qᵀ *ᵥ (β a).1, (β a).2))) ⟨0, hN⟩ j := by
    intro β
    unfold physGrad
    simp only [residual, linBatch, Matrix.one_mulVec]
    rw [mul_left_comm]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [hres (β a).1 (β a).2, hcol (β a).1]
    ring
  -- the map `β ↦ (Qᵀ z_a, w_a)_a` preserves the batch law
  have hTmeas : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) => (Qᵀ *ᵥ x.1, x.2)) := by
    fun_prop
  have hTB : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      fun a => (Qᵀ *ᵥ (β a).1, (β a).2)) := by
    refine measurable_pi_iff.mpr (fun a => ?_)
    exact hTmeas.comp (measurable_pi_apply a)
  have hgauss : (gaussBatch n m).map (fun x : (Fin n → ℝ) × (Fin m → ℝ) => (Qᵀ *ᵥ x.1, x.2))
      = gaussBatch n m := by
    have hmemQ : (Qᵀ)ᵀ * Qᵀ = 1 := by
      rw [Matrix.transpose_transpose]
      exact hQQ
    have hO : Qᵀ ∈ Matrix.orthogonalGroup (Fin n) ℝ :=
      (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).2 hmemQ
    have h1 : (Muon.Foundations.stdGaussianPi n).map (fun z : Fin n → ℝ => Qᵀ *ᵥ z)
        = Muon.Foundations.stdGaussianPi n :=
      Muon.Foundations.stdGaussianPi_map_orthogonal n ⟨Qᵀ, hO⟩
    have h2 := Measure.map_prod_map (Muon.Foundations.stdGaussianPi n)
      (Muon.Foundations.stdGaussianPi m) (f := fun z : Fin n → ℝ => Qᵀ *ᵥ z) (g := id)
      (by fun_prop) measurable_id
    rw [Measure.map_id, h1] at h2
    unfold gaussBatch
    exact h2.symm
  have hT : (batchLaw n m B).map
      (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => fun a => (Qᵀ *ᵥ (β a).1, (β a).2))
      = batchLaw n m B := by
    haveI : IsProbabilityMeasure (gaussBatch n m) := by
      unfold gaussBatch
      infer_instance
    unfold batchLaw
    have h := Measure.pi_map_pi (μ := fun _ : Fin B => gaussBatch n m)
      (f := fun _ : Fin B => fun x : (Fin n → ℝ) × (Fin m → ℝ) => (Qᵀ *ᵥ x.1, x.2))
      (fun _ => hTmeas.aemeasurable)
    refine h.trans ?_
    congr 1
    funext i
    exact hgauss
  have hF : Measurable (fun γ : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      physGrad (whitenedState Sg Δ Q) (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) γ) ⟨0, hN⟩ j) := by
    unfold physGrad residual linBatch
    fun_prop
  calc (batchLaw n m B).map (fun β => Real.sign (physGrad Δ (linBatch (CFC.sqrt Sg) β) p j))
      = (batchLaw n m B).map ((fun γ => Real.sign (physGrad (whitenedState Sg Δ Q)
            (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) γ) ⟨0, hN⟩ j))
          ∘ (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
              fun a => (Qᵀ *ᵥ (β a).1, (β a).2))) := by
        congr 1
        funext β
        simp only [Function.comp, hphys β, aux_sign_pos_mul _ _ hpos]
    _ = (((batchLaw n m B).map
          (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => fun a => (Qᵀ *ᵥ (β a).1, (β a).2))).map
          (fun γ => Real.sign (physGrad (whitenedState Sg Δ Q)
            (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) γ) ⟨0, hN⟩ j))) :=
        (Measure.map_map (aux_sign_measurable.comp hF) hTB).symm
    _ = (batchLaw n m B).map (fun β => Real.sign (physGrad (whitenedState Sg Δ Q)
            (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) β) ⟨0, hN⟩ j)) := by
        rw [hT]

/-- Part (ii) of `lem:app-sgd-whitening`: the Frobenius, row, column and entry identities of the
whitened state `A` (`‖A‖²_F = 2ℛ`, `A_{1j} = μ_pj`, row `1` has squared norm `R_p`, column `j` has
squared norm `C_j`). cr-2026-10-23. Source `section.tex` l. 791-804. LaTeX statement (verbatim):
```latex
\begin{lemma}[Whitening a coordinate]\label{lem:app-sgd-whitening}
Let $Q$ be orthogonal with first column $\Sigma^{1/2}e_p/\sqrt{v_p}$ and put
$A\defeq Q^\T\Sigma^{1/2}\Delta$. Then $\norm A_\F^2=2\cR$, the entry
$A_{1j}$ equals $\mu_{pj}$, row $1$ of $A$ has squared norm $R_p$, column $j$
of $A$ has squared norm $C_j$, and $\sign(G^\circ_{pj})$ has the law of
$\sign(G^A_{1j})$, where $G^A$ is the isotropic gradient of the state $A$.
In particular \cref{prop:app-sgd-coordinate} applies to $(p,j)$ with $F^2=2\cR$,
$\Delta_{ij}$ replaced by $\mu_{pj}$, and
$\norm{\bar A}_\F^2=2\cR-R_p-C_j+\mu_{pj}^2$, whenever this is at least
$\cR/2$ and $B\ge4$; its comparison term is
\[
\sqrt{\frac2\pi}\,\mathcal N_B\frac{\mu_{pj}}{\sqrt{2\cR}}=\frac{\mathcal N_B\,(\Sigma\Delta)_{pj}}{\sqrt{\pi\cR\,v_p}} .
\]
\end{lemma}
``` -/
theorem lem_app_sgd_whitening_ii {n m : ℕ} (hN : 0 < n) (Sg : Matrix (Fin n) (Fin n) ℝ)
    (hSg : Sg.PosSemidef) (Δ : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (hp : 0 < Sg p p)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hQc : ∀ k, Q k ⟨0, hN⟩ = CFC.sqrt Sg k p / Real.sqrt (Sg p p)) (j : Fin m) :
    (∑ i, ∑ l, whitenedState Sg Δ Q i l ^ 2 = riskTwo Sg Δ) ∧
    whitenedState Sg Δ Q ⟨0, hN⟩ j = whMu Sg Δ p j ∧
    (∑ l, whitenedState Sg Δ Q ⟨0, hN⟩ l ^ 2 = whR Sg Δ p) ∧
    (∑ i, whitenedState Sg Δ Q i j ^ 2 = whC Sg Δ j) := by
  have hSym := aux_S_symm Sg
  have hSS := aux_S_mul_self Sg hSg
  have hQQ := aux_Q_comm Q hQ
  have hSk : ∀ k l, CFC.sqrt Sg k l = CFC.sqrt Sg l k := fun k l => by
    have h := congrFun (congrFun hSym l) k
    simpa [Matrix.transpose_apply] using h
  have hsumS : ∀ l, ∑ k, CFC.sqrt Sg p k * (CFC.sqrt Sg * Δ) k l = (Sg * Δ) p l := by
    intro l
    conv_rhs => rw [← hSS]
    rw [Matrix.mul_assoc, Matrix.mul_apply]
  have hrow : ∀ l, whitenedState Sg Δ Q ⟨0, hN⟩ l = (Sg * Δ) p l / Real.sqrt (Sg p p) := by
    intro l
    unfold whitenedState
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    have e : ∑ k, (Qᵀ) ⟨0, hN⟩ k * (CFC.sqrt Sg * Δ) k l
        = ∑ k, CFC.sqrt Sg p k * (CFC.sqrt Sg * Δ) k l / Real.sqrt (Sg p p) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.transpose_apply, hQc k, hSk k p]
      ring
    rw [e, ← Finset.sum_div, hsumS l]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hA : whitenedState Sg Δ Q * (whitenedState Sg Δ Q)ᵀ
        = Qᵀ * (CFC.sqrt Sg * Δ * Δᵀ * CFC.sqrt Sg) * Q := by
      simp only [whitenedState, Matrix.transpose_mul, Matrix.transpose_transpose, hSym,
        Matrix.mul_assoc]
    rw [aux_sum_sq_eq_trace, hA, aux_trace_conj Q _ hQQ]
    unfold riskTwo pairIdIn
    conv_rhs => rw [← hSS]
    rw [Matrix.trace_mul_comm (CFC.sqrt Sg * Δ * Δᵀ) (CFC.sqrt Sg)]
    simp only [Matrix.mul_assoc]
  · unfold whMu
    exact hrow j
  · unfold whR
    simp only [hrow]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro l _
    rw [div_pow, Real.sq_sqrt hp.le]
  · have hAtA : (whitenedState Sg Δ Q)ᵀ * whitenedState Sg Δ Q = Δᵀ * Sg * Δ := by
      have h2 : Q * (Qᵀ * (CFC.sqrt Sg * Δ)) = CFC.sqrt Sg * Δ := by
        rw [← Matrix.mul_assoc, hQQ, Matrix.one_mul]
      have h3 : CFC.sqrt Sg * (CFC.sqrt Sg * Δ) = Sg * Δ := by
        rw [← Matrix.mul_assoc, hSS]
      simp only [whitenedState, Matrix.transpose_mul, Matrix.transpose_transpose, hSym,
        Matrix.mul_assoc]
      rw [h2, h3]
    rw [show ∑ i, whitenedState Sg Δ Q i j ^ 2
        = ((whitenedState Sg Δ Q)ᵀ * whitenedState Sg Δ Q) j j by
      simp [Matrix.mul_apply, sq]]
    rw [hAtA]
    unfold whC
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    rw [Finset.sum_comm]

/-- Part (iii) of `lem:app-sgd-whitening`: the "in particular" clause. The deleted block
`Ā = sgdDeletedBlock A ⟨0, hN⟩ j` (row index `1` of the source is `⟨0, hN⟩`) has `‖Ā‖²_F = 2ℛ − R_p − C_j + μ_pj²`; the comparison term equals
`𝒩_B (ΣΔ)_pj / √(π ℛ Σ_pp)`; the hypotheses `4 ≤ B` and `‖Ā‖²_F ≥ ℛ/2` give `‖A‖_F/2 ≤ ‖Ā‖_F`, i.e.
the isotropic coordinate proposition `prop:app-sgd-coordinate` (`Muon.SignSGD.prop_app_sgd_coordinate`)
applies to `(A, ⟨0, hN⟩, j)` with `F = ‖A‖_F = √(2ℛ)` and `Δ_ij = μ_pj`. cr-2026-10-23. Source `section.tex` l. 791-804. LaTeX statement (verbatim):
```latex
\begin{lemma}[Whitening a coordinate]\label{lem:app-sgd-whitening}
Let $Q$ be orthogonal with first column $\Sigma^{1/2}e_p/\sqrt{v_p}$ and put
$A\defeq Q^\T\Sigma^{1/2}\Delta$. Then $\norm A_\F^2=2\cR$, the entry
$A_{1j}$ equals $\mu_{pj}$, row $1$ of $A$ has squared norm $R_p$, column $j$
of $A$ has squared norm $C_j$, and $\sign(G^\circ_{pj})$ has the law of
$\sign(G^A_{1j})$, where $G^A$ is the isotropic gradient of the state $A$.
In particular \cref{prop:app-sgd-coordinate} applies to $(p,j)$ with $F^2=2\cR$,
$\Delta_{ij}$ replaced by $\mu_{pj}$, and
$\norm{\bar A}_\F^2=2\cR-R_p-C_j+\mu_{pj}^2$, whenever this is at least
$\cR/2$ and $B\ge4$; its comparison term is
\[
\sqrt{\frac2\pi}\,\mathcal N_B\frac{\mu_{pj}}{\sqrt{2\cR}}=\frac{\mathcal N_B\,(\Sigma\Delta)_{pj}}{\sqrt{\pi\cR\,v_p}} .
\]
\end{lemma}
``` -/
theorem lem_app_sgd_whitening_iii {n m B : ℕ} (hN : 0 < n) (Sg : Matrix (Fin n) (Fin n) ℝ)
    (hSg : Sg.PosSemidef) (Δ : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (hp : 0 < Sg p p)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hQc : ∀ k, Q k ⟨0, hN⟩ = CFC.sqrt Sg k p / Real.sqrt (Sg p p)) (j : Fin m) :
    frobNorm (whitenedState Sg Δ Q) = Real.sqrt (riskTwo Sg Δ) ∧
    (∑ k, ∑ l, sgdDeletedBlock (whitenedState Sg Δ Q) ⟨0, hN⟩ j k l ^ 2
        = riskTwo Sg Δ - whR Sg Δ p - whC Sg Δ j + whMu Sg Δ p j ^ 2) ∧
    (Real.sqrt (2 / Real.pi) * batchConst B * whMu Sg Δ p j / Real.sqrt (riskTwo Sg Δ)
        = batchConst B * (Sg * Δ) p j / Real.sqrt (Real.pi * (riskTwo Sg Δ / 2) * Sg p p)) ∧
    (4 ≤ B → riskTwo Sg Δ / 4 ≤ ∑ k, ∑ l, sgdDeletedBlock (whitenedState Sg Δ Q) ⟨0, hN⟩ j k l ^ 2 →
        frobNorm (whitenedState Sg Δ Q) / 2
          ≤ frobNorm (sgdDeletedBlock (whitenedState Sg Δ Q) ⟨0, hN⟩ j)) := by
  obtain ⟨h1, h2, h3, h4⟩ := lem_app_sgd_whitening_ii hN Sg hSg Δ p hp Q hQ hQc j
  have hR0 : 0 ≤ riskTwo Sg Δ := by
    rw [← h1]
    exact Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun l _ => sq_nonneg _))
  have hsq4 : Real.sqrt 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [frobNorm, h1]
  · rw [aux_deleted_sum, ← h1, ← h3, ← h4, ← h2]
  · have key : Real.sqrt (2 / Real.pi) / Real.sqrt (riskTwo Sg Δ)
        = 1 / Real.sqrt (Real.pi * (riskTwo Sg Δ / 2)) := by
      rcases hR0.eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      · have hne : riskTwo Sg Δ ≠ 0 := hpos.ne'
        rw [← Real.sqrt_div (by positivity : (0:ℝ) ≤ 2 / Real.pi) (riskTwo Sg Δ), one_div,
          ← Real.sqrt_inv]
        congr 1
        field_simp
    have hxnn : 0 ≤ Real.pi * (riskTwo Sg Δ / 2) := mul_nonneg Real.pi_pos.le (by linarith)
    unfold whMu
    have e1 : Real.sqrt (2 / Real.pi) * batchConst B * ((Sg * Δ) p j / Real.sqrt (Sg p p))
        / Real.sqrt (riskTwo Sg Δ)
        = (Real.sqrt (2 / Real.pi) / Real.sqrt (riskTwo Sg Δ))
          * (batchConst B * (Sg * Δ) p j / Real.sqrt (Sg p p)) := by
      ring
    have e2 : batchConst B * (Sg * Δ) p j / Real.sqrt (Real.pi * (riskTwo Sg Δ / 2) * Sg p p)
        = batchConst B * (Sg * Δ) p j
          / (Real.sqrt (Real.pi * (riskTwo Sg Δ / 2)) * Real.sqrt (Sg p p)) := by
      rw [Real.sqrt_mul hxnn (Sg p p)]
    rw [e1, key, e2]
    ring
  · intro _ hineq
    unfold frobNorm
    rw [h1]
    calc Real.sqrt (riskTwo Sg Δ) / 2 = Real.sqrt (riskTwo Sg Δ / 4) := by
          rw [Real.sqrt_div hR0, hsq4]
      _ ≤ _ := Real.sqrt_le_sqrt hineq

/-! ## `lem:app-sgd-deletion` -/

/-- Part (i) of `lem:app-sgd-deletion`: on `𝒜_p = {R_p ≤ P₋/4}` the deleted block of the whitened
state has squared norm at least `ℛ` (for `k ≥ k_*`, any orthogonal `Q` with the first column of
`lem:app-sgd-whitening`). cr-2026-10-23. Source `section.tex` l. 827-838. LaTeX statement (verbatim):
```latex
\begin{lemma}[Deletion estimates]\label{lem:app-sgd-deletion}
In the Haar model put
\[
Q_0\defeq105\Big(\frac{4A_0}{P_-}\Big)^4,\qquad k_*\defeq\max\{4,\lceil4A_2/P_-\rceil\},
\]
and let $k\ge k_*$. On the event $\mathcal A_p\defeq\{R_p\le P_- /4\}$, the
deleted block of \cref{lem:app-sgd-whitening} has squared norm at least
$\cR$. For $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-deletion}
\EE R_p^q\le\frac{(2q-1)!!\,A_0^q}{\Nout^q},\qquad \EE\abs{\mu_{pj}}^{2q}\le\frac{(2q-1)!!\,A_1^q}{\Nout^qk^q},\qquad \PP(\mathcal A_p^c)\le\frac{Q_0}{\Nout^4}.
\end{equation}
\end{lemma}
``` -/
theorem lem_app_sgd_deletion_i {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (hk : haarKStar P ≤ kOf n m B) (hN : 0 < n) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (p : Fin n) (j : Fin m) (hU : haarR μ D U p ≤ haarPminus P / 4)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hQc : ∀ k, Q k ⟨0, hN⟩
      = CFC.sqrt (haarSigmaOut U μ) k p / Real.sqrt (haarSigmaOut U μ p p)) :
    twoR μ D / 2 ≤ ∑ k, ∑ l, sgdDeletedBlock
      (whitenedState (haarSigmaOut U μ) (haarDelta U D) Q) ⟨0, hN⟩ j k l ^ 2 := by
  have hbd := haar_bounds P n m B μ D hstate
  have hlo : haarPminus P ≤ twoR μ D := hbd.1
  obtain ⟨h1, -, ⟨hc, -⟩, -, -, -, h7, -⟩ := haar_forms_app_sgd P μ D hstate U p j p
  have hmu : ∀ i, P.c ≤ μ i ∧ μ i ≤ P.L := by
    unfold def_app_sgd_state_law at hstate
    obtain ⟨-, -, -, -, -, hmu', -⟩ := hstate
    exact hmu'
  have hPm : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hk4 : (4 : ℝ) ≤ (kOf n m B : ℝ) := by
    have : 4 ≤ kOf n m B := le_trans (le_max_left _ _) hk
    exact_mod_cast this
  have hceil : 4 * haarA2 P / haarPminus P ≤ (kOf n m B : ℝ) := by
    have h' : ⌈4 * haarA2 P / haarPminus P⌉₊ ≤ kOf n m B := le_trans (le_max_right _ _) hk
    exact le_trans (Nat.le_ceil _) (by exact_mod_cast h')
  have hk0 : (0 : ℝ) < (kOf n m B : ℝ) := by linarith
  have hA : 4 * haarA2 P ≤ (kOf n m B : ℝ) * haarPminus P := (div_le_iff₀ hPm).mp hceil
  have hCk : haarA2 P / (kOf n m B : ℝ) ≤ haarPminus P / 4 := by
    rw [div_le_iff₀ hk0]
    nlinarith
  have hSg : (haarSigmaOut U μ).PosSemidef := by
    unfold haarSigmaOut
    have hdiag : (Matrix.diagonal μ).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun i => le_trans P.c_pos.le (hmu i).1)
    have h := hdiag.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℝ)
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hpos : 0 < haarSigmaOut U μ p p := lt_of_lt_of_le P.c_pos hc
  have hid := (lem_app_sgd_whitening_iii (B := B) hN (haarSigmaOut U μ) hSg (haarDelta U D) p
    hpos Q hQ hQc j).2.1
  have hR : whR (haarSigmaOut U μ) (haarDelta U D) p ≤ haarPminus P / 4 := hU
  have hC : whC (haarSigmaOut U μ) (haarDelta U D) j ≤ haarPminus P / 4 :=
    le_trans (le_trans h7 hCk) le_rfl
  rw [hid, h1]
  nlinarith [sq_nonneg (whMu (haarSigmaOut U μ) (haarDelta U D) p j)]

private noncomputable def trO {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Matrix.orthogonalGroup (Fin n) ℝ :=
  ⟨(U : Matrix (Fin n) (Fin n) ℝ)ᵀ, by
    rw [Matrix.mem_orthogonalGroup_iff]
    simpa using (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2⟩

private lemma trO_coe {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    ((trO U : Matrix.orthogonalGroup (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ)
      = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := rfl

private lemma trO_cont {n : ℕ} : Continuous (trO (n := n)) := by
  unfold trO
  exact Continuous.subtype_mk (continuous_subtype_val.matrix_transpose) _

private lemma trO_trO {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ) : trO (trO U) = U := by
  apply Subtype.ext
  simp [trO_coe]

private lemma trO_mul {n : ℕ} (a b : Matrix.orthogonalGroup (Fin n) ℝ) :
    trO (a * b) = trO b * trO a := by
  apply Subtype.ext
  simp [trO_coe, Matrix.transpose_mul]

private lemma isOrthHaar_trO {n : ℕ} {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) : IsOrthHaar (ν.map trO) := by
  obtain ⟨hP, hL, hR⟩ := hν
  have hm : Measurable (trO (n := n)) := trO_cont.measurable
  refine ⟨?_, ?_, ?_⟩
  · have : IsProbabilityMeasure ν := hP
    exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ]; simp⟩
  · intro g
    have hg1 : Measurable (fun h : Matrix.orthogonalGroup (Fin n) ℝ => g * h) :=
      (continuous_const.mul continuous_id).measurable
    rw [Measure.map_map hg1 hm]
    have : (fun h => g * h) ∘ trO = trO ∘ (fun h => h * trO g) := by
      funext h; simp [Function.comp, trO_mul, trO_trO]
    have hg2 : Measurable (fun h : Matrix.orthogonalGroup (Fin n) ℝ => h * trO g) :=
      (continuous_id.mul continuous_const).measurable
    rw [this, ← Measure.map_map hm hg2, hR]
  · intro g
    have hg1 : Measurable (fun h : Matrix.orthogonalGroup (Fin n) ℝ => h * g) :=
      (continuous_id.mul continuous_const).measurable
    rw [Measure.map_map hg1 hm]
    have : (fun h => h * g) ∘ trO = trO ∘ (fun h => trO g * h) := by
      funext h; simp [Function.comp, trO_mul, trO_trO]
    have hg2 : Measurable (fun h : Matrix.orthogonalGroup (Fin n) ℝ => trO g * h) :=
      (continuous_const.mul continuous_id).measurable
    rw [this, ← Measure.map_map hm hg2, hL]

private lemma row_law {n : ℕ} {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (p : Fin n) :
    ν.map (fun U : Matrix.orthogonalGroup (Fin n) ℝ => fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)
      = sphereGauss n := by
  have hm : Measurable (trO (n := n)) := trO_cont.measurable
  have h1 := orthHaar_map_mulVec_eq_sphereGauss n (isOrthHaar_trO hν) (Pi.single p 1) (by
    simp [euclidNorm, Pi.single_apply])
  have hm2 : Measurable (fun V : Matrix.orthogonalGroup (Fin n) ℝ =>
      (V : Matrix (Fin n) (Fin n) ℝ) *ᵥ (Pi.single p (1:ℝ) : Fin n → ℝ)) := by
    apply Continuous.measurable
    exact continuous_subtype_val.matrix_mulVec continuous_const
  rw [Measure.map_map hm2 hm] at h1
  rw [← h1]
  congr 1
  funext U k
  simp [trO_coe, Matrix.mulVec, dotProduct, Pi.single_apply]

private lemma sphere_ae_le_one (n : ℕ) : ∀ᵐ v ∂(sphereGauss n), ∑ i, v i ^ 2 ≤ 1 := by
  unfold sphereGauss
  have hm : Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) := by
    unfold euclidNorm; fun_prop
  have hs : MeasurableSet {v : Fin n → ℝ | ∑ i, v i ^ 2 ≤ 1} :=
    measurableSet_le (by fun_prop) measurable_const
  refine (ae_map_iff hm.aemeasurable hs).2 (Filter.Eventually.of_forall fun z => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  show ∑ i, ((euclidNorm n z)⁻¹ * z i) ^ 2 ≤ 1
  by_cases hz : ∑ i, z i ^ 2 = 0
  · have : euclidNorm n z = 0 := by simp [euclidNorm, hz]
    simp [this]
  · have hpos : 0 < ∑ i, z i ^ 2 := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hz)
    have : ∑ i, ((euclidNorm n z)⁻¹ * z i) ^ 2 = 1 := by
      simp_rw [mul_pow]
      rw [← Finset.mul_sum, inv_pow]
      unfold euclidNorm
      rw [Real.sq_sqrt hpos.le]
      field_simp
    exact this.le

private lemma sphere_integrable {n : ℕ} (g : (Fin n → ℝ) → ℝ) (hg : Continuous g) :
    Integrable g (sphereGauss n) := by
  have : IsProbabilityMeasure (sphereGauss n) := by
    unfold sphereGauss
    have hm : Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) := by
      unfold euclidNorm; fun_prop
    exact ⟨by rw [Measure.map_apply hm MeasurableSet.univ]; simp⟩
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [sphere_ae_le_one n] with v hv
  apply hC
  intro i _
  have : v i ^ 2 ≤ 1 := le_trans (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)) hv
  constructor <;> nlinarith [sq_nonneg (v i + 1), sq_nonneg (v i - 1)]

private lemma lintegral_row_le {n : ℕ} {ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (p : Fin n) (g : (Fin n → ℝ) → ℝ) (hg : Continuous g)
    (hg0 : ∀ ω, 0 ≤ g ω) (b : ℝ) (hb : ∫ ω, g ω ∂(sphereGauss n) ≤ b) :
    ∫⁻ U, ENNReal.ofReal (g (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)) ∂ν
      ≤ ENNReal.ofReal b := by
  have hrow : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k) := by
    apply Continuous.measurable
    exact continuous_pi fun k => continuous_subtype_val.matrix_elem p k
  have h1 : ∫⁻ U, ENNReal.ofReal (g (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)) ∂ν
      = ∫⁻ ω, ENNReal.ofReal (g ω) ∂(sphereGauss n) := by
    rw [← row_law hν p]
    exact (lintegral_map (ENNReal.measurable_ofReal.comp hg.measurable) hrow).symm
  rw [h1, ← ofReal_integral_eq_lintegral_ofReal (sphere_integrable g hg)
    (Filter.Eventually.of_forall hg0)]
  exact ENNReal.ofReal_le_ofReal hb


private lemma dq_ge_pow (n q : ℕ) : (n : ℝ) ^ q ≤ dq n q := by
  unfold dq
  have h : (n : ℝ) ^ q = ∏ r ∈ Finset.range q, (n : ℝ) := by simp
  rw [h]
  have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  gcongr with r hr
  have : (0:ℝ) ≤ r := Nat.cast_nonneg r
  linarith

private lemma TD_psd {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) :
    (TD μ D).PosSemidef := by
  have h := Matrix.posSemidef_self_mul_conjTranspose (Matrix.diagonal μ * D)
  have e : TD μ D = (Matrix.diagonal μ * D) * (Matrix.diagonal μ * D)ᴴ := by
    unfold TD
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [e]; exact h

private lemma quad_TD {n m : ℕ} (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ) (ω : Fin n → ℝ) :
    dotProduct ω ((TD μ D).mulVec ω) = ∑ l, (∑ k, ω k * μ k * D k l) ^ 2 := by
  have e : TD μ D = (Matrix.diagonal μ * D) * (Matrix.diagonal μ * D)ᵀ := by
    unfold TD
    rw [Matrix.transpose_mul, Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [e, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  unfold dotProduct
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [sq]
  have : (ω ᵥ* (Matrix.diagonal μ * D)) l = ∑ k, ω k * μ k * D k l := by
    simp only [Matrix.vecMul, dotProduct, Matrix.diagonal_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]


/-- Part (ii) of `lem:app-sgd-deletion`: the moment bounds
`E R_p^q ≤ (2q−1)!! A₀^q / N^q` and `E|μ_pj|^{2q} ≤ (2q−1)!! A₁^q / (N^q k^q)` for `1 ≤ q ≤ 4`
under the Haar measure `ν`, for `k ≥ k_*`. cr-2026-10-23. Source `section.tex` l. 827-838. LaTeX statement (verbatim):
```latex
\begin{lemma}[Deletion estimates]\label{lem:app-sgd-deletion}
In the Haar model put
\[
Q_0\defeq105\Big(\frac{4A_0}{P_-}\Big)^4,\qquad k_*\defeq\max\{4,\lceil4A_2/P_-\rceil\},
\]
and let $k\ge k_*$. On the event $\mathcal A_p\defeq\{R_p\le P_- /4\}$, the
deleted block of \cref{lem:app-sgd-whitening} has squared norm at least
$\cR$. For $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-deletion}
\EE R_p^q\le\frac{(2q-1)!!\,A_0^q}{\Nout^q},\qquad \EE\abs{\mu_{pj}}^{2q}\le\frac{(2q-1)!!\,A_1^q}{\Nout^qk^q},\qquad \PP(\mathcal A_p^c)\le\frac{Q_0}{\Nout^4}.
\end{equation}
\end{lemma}
``` -/
theorem lem_app_sgd_deletion_ii {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (hk : haarKStar P ≤ kOf n m B) (hN : 0 < n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (p : Fin n) (j : Fin m) (q : ℕ) (hq : 1 ≤ q ∧ q ≤ 4) :
    (∫⁻ U, ENNReal.ofReal (haarR μ D U p ^ q) ∂ν
        ≤ ENNReal.ofReal (((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarA0 P ^ q
            / (n : ℝ) ^ q)) ∧
    (∫⁻ U, ENNReal.ofReal (haarMu μ D U p j ^ (2 * q)) ∂ν
        ≤ ENNReal.ofReal (((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarA1 P ^ q
            / ((n : ℝ) ^ q * ((kOf n m B : ℕ) : ℝ) ^ q))) := by
  have hbd := haar_bounds P n m B μ D hstate
  have hstate' := hstate
  unfold def_app_sgd_state_law at hstate'
  obtain ⟨-, hk2, -, -, -, hmu, -, -, hcol⟩ := hstate'
  have hcol' : ∀ j, ∑ i, D i j ^ 2 ≤ P.Ccol / ((kOf n m B : ℕ) : ℝ) := hcol
  have hkn : kOf n m B ≤ n := by unfold kOf; exact min_le_left _ _
  have hn2 : 2 ≤ n := le_trans hk2 hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hN
  have hk0 : (0 : ℝ) < ((kOf n m B : ℕ) : ℝ) := by
    have : 0 < kOf n m B := by omega
    exact_mod_cast this
  have hc := P.c_pos
  have hLpos : 0 < P.L := lt_of_lt_of_le hc P.c_le_L
  have hdf : (0 : ℝ) ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdq := dq_ge_pow n q
  have hnq : (0 : ℝ) < (n : ℝ) ^ q := pow_pos hn0 q
  have hcq : (0 : ℝ) < P.c ^ q := pow_pos hc q
  have hrowforms := fun (U : Matrix.orthogonalGroup (Fin n) ℝ) =>
    haar_forms_app_sgd P μ D hstate U p j p
  constructor
  · -- part 1
    set T := TD μ D with hT
    let g : (Fin n → ℝ) → ℝ := fun ω => (dotProduct ω (T.mulVec ω)) ^ q / P.c ^ q
    have hgc : Continuous g := by
      simp only [g]
      apply Continuous.div_const
      apply Continuous.pow
      unfold dotProduct Matrix.mulVec
      fun_prop
    have hg0 : ∀ ω, 0 ≤ g ω := by
      intro ω
      simp only [g]
      rw [hT, quad_TD]
      positivity
    have htr : 0 ≤ T.trace ∧ T.trace ≤ haarH0 P := by
      refine ⟨(TD_psd μ D).trace_nonneg, hbd.2.2.1⟩
    have hH0 : 0 ≤ haarH0 P := by unfold haarH0; positivity
    have hint : ∫ ω, g ω ∂(sphereGauss n) ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarA0 P ^ q
            / (n : ℝ) ^ q := by
      simp only [g]
      rw [integral_div]
      have h3 := lem_app_sgd_sphere_iii n q hn2 hq T (TD_psd μ D)
      have hdqpos : 0 < dq n q := lt_of_lt_of_le hnq hdq
      have h4 : ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * T.trace ^ q / dq n q
          ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarH0 P ^ q / (n : ℝ) ^ q := by
        calc _ ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarH0 P ^ q / dq n q := by
              apply div_le_div_of_nonneg_right _ hdqpos.le
              exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ htr.1 htr.2 q) hdf
          _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg hdf (pow_nonneg hH0 q)) hnq hdq
      calc (∫ ω, (dotProduct ω (T.mulVec ω)) ^ q ∂(sphereGauss n)) / P.c ^ q
          ≤ (((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarH0 P ^ q / (n : ℝ) ^ q) / P.c ^ q :=
            div_le_div_of_nonneg_right (le_trans h3 h4) hcq.le
        _ = _ := by
            unfold haarA0
            field_simp
            rw [← mul_pow, mul_div_cancel₀ _ hc.ne']
    refine le_trans (lintegral_mono fun U => ?_) (lintegral_row_le hν p g hgc hg0 _ hint)
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨-, hSpp, ⟨hlo, -⟩, -, hR, -⟩ := hrowforms U
    rw [hR]
    simp only [g]
    rw [hT, quad_TD, ← div_pow]
    have hN0 : 0 ≤ ∑ l, (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k l) ^ 2 :=
      Finset.sum_nonneg fun l _ => sq_nonneg _
    exact pow_le_pow_left₀ (div_nonneg hN0 (by linarith)) (div_le_div_of_nonneg_left hN0 hc hlo) q
  · set a : Fin n → ℝ := fun k => μ k * D k j with ha
    let g : (Fin n → ℝ) → ℝ := fun ω => |dotProduct ω a| ^ (2 * q) / P.c ^ q
    have hgc : Continuous g := by
      simp only [g]
      apply Continuous.div_const
      apply Continuous.pow
      apply continuous_abs.comp
      unfold dotProduct
      fun_prop
    have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by simp only [g]; positivity
    have hS : euclidNorm n a ^ (2 * q) ≤ (P.L ^ 2 * P.Ccol / ((kOf n m B : ℕ) : ℝ)) ^ q := by
      have h1 : euclidNorm n a ^ (2 * q) = (∑ k, a k ^ 2) ^ q := by
        unfold euclidNorm
        rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      rw [h1]
      apply pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => sq_nonneg _)
      calc ∑ k, a k ^ 2 ≤ ∑ k, P.L ^ 2 * D k j ^ 2 := by
            apply Finset.sum_le_sum
            intro k _
            simp only [ha]
            rw [mul_pow]
            apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
            exact pow_le_pow_left₀ (le_trans hc.le (hmu k).1) (hmu k).2 2
        _ = P.L ^ 2 * ∑ k, D k j ^ 2 := by rw [Finset.mul_sum]
        _ ≤ P.L ^ 2 * (P.Ccol / ((kOf n m B : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (hcol' j) (sq_nonneg _)
        _ = _ := by ring
    have hint : ∫ ω, g ω ∂(sphereGauss n) ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * haarA1 P ^ q
            / ((n : ℝ) ^ q * ((kOf n m B : ℕ) : ℝ) ^ q) := by
      simp only [g]
      rw [integral_div]
      have h3 := lem_app_sgd_sphere_ii n q hn2 hq a
      have hdqpos : 0 < dq n q := lt_of_lt_of_le hnq hdq
      rw [h3]
      have h4 : ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * euclidNorm n a ^ (2 * q) / dq n q
          ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * (P.L ^ 2 * P.Ccol / ((kOf n m B : ℕ) : ℝ)) ^ q
              / (n : ℝ) ^ q := by
        calc _ ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * (P.L ^ 2 * P.Ccol / ((kOf n m B : ℕ) : ℝ)) ^ q
              / dq n q := by
              apply div_le_div_of_nonneg_right _ hdqpos.le
              exact mul_le_mul_of_nonneg_left hS hdf
          _ ≤ _ := div_le_div_of_nonneg_left
              (mul_nonneg hdf (pow_nonneg (by have := P.Ccol_pos; positivity) q)) hnq hdq
      calc _ ≤ (((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * (P.L ^ 2 * P.Ccol / ((kOf n m B : ℕ) : ℝ)) ^ q
              / (n : ℝ) ^ q) / P.c ^ q := div_le_div_of_nonneg_right h4 hcq.le
        _ = _ := by
            unfold haarA1
            field_simp
            rw [← mul_pow, ← mul_pow]
            congr 1
            field_simp
    refine le_trans (lintegral_mono fun U => ?_) (lintegral_row_le hν p g hgc hg0 _ hint)
    apply ENNReal.ofReal_le_ofReal
    obtain ⟨-, hSpp, ⟨hlo, -⟩, hMu, -⟩ := hrowforms U
    rw [hMu]
    simp only [g]
    have hx : (∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k * μ k * D k j)
        = dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k) a := by
      unfold dotProduct
      exact Finset.sum_congr rfl fun k _ => by simp only [ha]; ring
    rw [hx]
    set x := dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k) a
    have hv0 : 0 ≤ haarSigmaOut U μ p p := by linarith
    have e1 : (x / Real.sqrt (haarSigmaOut U μ p p)) ^ (2 * q) = (x ^ 2 / haarSigmaOut U μ p p) ^ q := by
      rw [pow_mul, div_pow, Real.sq_sqrt hv0]
    have e2 : |x| ^ (2 * q) / P.c ^ q = (x ^ 2 / P.c) ^ q := by
      rw [pow_mul, sq_abs, div_pow]
    rw [e1, e2]
    exact pow_le_pow_left₀ (div_nonneg (sq_nonneg _) hv0)
      (div_le_div_of_nonneg_left (sq_nonneg _) hc hlo) q

/-- Part (iii) of `lem:app-sgd-deletion`: the event bound `P(𝒜_p^c) ≤ Q₀ / N⁴` under the Haar
measure `ν`, for `k ≥ k_*`. cr-2026-10-23. Source `section.tex` l. 827-838. LaTeX statement (verbatim):
```latex
\begin{lemma}[Deletion estimates]\label{lem:app-sgd-deletion}
In the Haar model put
\[
Q_0\defeq105\Big(\frac{4A_0}{P_-}\Big)^4,\qquad k_*\defeq\max\{4,\lceil4A_2/P_-\rceil\},
\]
and let $k\ge k_*$. On the event $\mathcal A_p\defeq\{R_p\le P_- /4\}$, the
deleted block of \cref{lem:app-sgd-whitening} has squared norm at least
$\cR$. For $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-deletion}
\EE R_p^q\le\frac{(2q-1)!!\,A_0^q}{\Nout^q},\qquad \EE\abs{\mu_{pj}}^{2q}\le\frac{(2q-1)!!\,A_1^q}{\Nout^qk^q},\qquad \PP(\mathcal A_p^c)\le\frac{Q_0}{\Nout^4}.
\end{equation}
\end{lemma}
``` -/
theorem lem_app_sgd_deletion_iii {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (hk : haarKStar P ≤ kOf n m B) (hN : 0 < n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν) (p : Fin n) :
    ν {U : Matrix.orthogonalGroup (Fin n) ℝ | haarPminus P / 4 < haarR μ D U p}
      ≤ ENNReal.ofReal (haarQ0 P / (n : ℝ) ^ 4) := by
  have hm : 0 < m := by
    unfold def_app_sgd_state_law at hstate
    exact hstate.1.2.1
  have hPm : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hmom := (lem_app_sgd_deletion_ii P μ D hstate hk hN ν hν p ⟨0, hm⟩ 4
    ⟨by norm_num, by norm_num⟩).1
  have hcont : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val
  have hSig : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarSigmaOut U μ) := by
    unfold haarSigmaOut
    exact (hcont.matrix_mul continuous_const).matrix_mul hcont.matrix_transpose
  have hDel : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarDelta U D) := by
    unfold haarDelta
    exact hcont.matrix_mul continuous_const
  have hW : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      haarSigmaOut U μ * haarDelta U D) := hSig.matrix_mul hDel
  have hnum : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ j, (haarSigmaOut U μ * haarDelta U D) p j ^ 2) :=
    continuous_finset_sum _ (fun j _ => (hW.matrix_elem p j).pow 2)
  have hden : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarSigmaOut U μ p p) :=
    hSig.matrix_elem p p
  have hmeas : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarR μ D U p) := by
    unfold haarR whR
    exact hnum.measurable.div hden.measurable
  have hf : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal (haarR μ D U p ^ 4)) :=
    ENNReal.measurable_ofReal.comp (hmeas.pow_const 4)
  have hc0 : ENNReal.ofReal ((haarPminus P / 4) ^ 4) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (by linarith) 4
  have hcinf : ENNReal.ofReal ((haarPminus P / 4) ^ 4) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hsub : {U : Matrix.orthogonalGroup (Fin n) ℝ | haarPminus P / 4 < haarR μ D U p} ⊆
      {U | ENNReal.ofReal ((haarPminus P / 4) ^ 4) ≤ ENNReal.ofReal (haarR μ D U p ^ 4)} := by
    intro U hU'
    simp only [Set.mem_setOf_eq] at hU' ⊢
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_pow_left₀ (by linarith) hU'.le 4
  have hMarkov := mul_meas_ge_le_lintegral₀ (μ := ν) hf.aemeasurable
    (ENNReal.ofReal ((haarPminus P / 4) ^ 4))
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hdf : ((Nat.doubleFactorial (2 * 4 - 1) : ℕ) : ℝ) = 105 := by
    norm_num [Nat.doubleFactorial]
  have heq : ENNReal.ofReal (((Nat.doubleFactorial (2 * 4 - 1) : ℕ) : ℝ) * haarA0 P ^ 4
      / (n : ℝ) ^ 4)
      = ENNReal.ofReal ((haarPminus P / 4) ^ 4) * ENNReal.ofReal (haarQ0 P / (n : ℝ) ^ 4) := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [hdf]
    simp only [haarA0, haarH0, haarQ0, haarPminus]
    have hc : P.c ≠ 0 := P.c_pos.ne'
    have hf1 : P.fMin ≠ 0 := P.fMin_pos.ne'
    field_simp
  have hbound : ENNReal.ofReal ((haarPminus P / 4) ^ 4)
      * ν {U : Matrix.orthogonalGroup (Fin n) ℝ | haarPminus P / 4 < haarR μ D U p}
      ≤ ENNReal.ofReal ((haarPminus P / 4) ^ 4)
        * ENNReal.ofReal (haarQ0 P / (n : ℝ) ^ 4) := by
    calc ENNReal.ofReal ((haarPminus P / 4) ^ 4)
          * ν {U : Matrix.orthogonalGroup (Fin n) ℝ | haarPminus P / 4 < haarR μ D U p}
        ≤ ENNReal.ofReal ((haarPminus P / 4) ^ 4)
          * ν {U | ENNReal.ofReal ((haarPminus P / 4) ^ 4)
              ≤ ENNReal.ofReal (haarR μ D U p ^ 4)} :=
          mul_le_mul_of_nonneg_left (measure_mono hsub) zero_le
      _ ≤ ∫⁻ U, ENNReal.ofReal (haarR μ D U p ^ 4) ∂ν := hMarkov
      _ ≤ ENNReal.ofReal (((Nat.doubleFactorial (2 * 4 - 1) : ℕ) : ℝ) * haarA0 P ^ 4
            / (n : ℝ) ^ 4) := hmom
      _ = _ := heq
  exact (ENNReal.mul_le_mul_iff_right hc0 hcinf).mp hbound

private lemma coord_sum_mean_abs_le_one {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (p : Fin n) (j : Fin m) : |haarMean B μ D U p j| ≤ 1 := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by
    unfold gaussBatch
    infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by
    unfold batchLaw
    infer_instance
  have hsign : ∀ x : ℝ, |Real.sign x| ≤ 1 := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · simp [Real.sign_of_neg hx]
    · simp [hx]
    · simp [Real.sign_of_pos hx]
  have h := norm_integral_le_of_norm_le_const (μ := batchLaw n m B) (C := (1 : ℝ))
    (f := fun β => haarSign μ D U β p j)
    (Filter.Eventually.of_forall fun β => by
      simpa only [Real.norm_eq_abs, haarSign, Matrix.map_apply] using
        hsign (physGrad (haarDelta U D) (haarBatch μ U β) p j))
  simpa only [haarMean, measureReal_def, measure_univ, ENNReal.toReal_one, mul_one, Real.norm_eq_abs] using h

private lemma coord_sum_err_entry {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (p : Fin n) (j : Fin m) :
    haarErr B μ D U p j = haarMean B μ D U p j
      - Real.sqrt (2 / Real.pi) * batchConst B * haarMu μ D U p j
        / Real.sqrt (twoR μ D) := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hSD : haarSigmaOut U μ * haarDelta U D
      = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D := by
    unfold haarSigmaOut haarDelta
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ
      (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  simp only [haarErr, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_assoc, Matrix.diagonal_mul]
  unfold haarMu whMu
  rw [hSD, Matrix.mul_assoc]
  ring

private lemma coord_sum_mu_sq_sum {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (p : Fin n) (hp : 0 ≤ haarSigmaOut U μ p p) :
    ∑ j, haarMu μ D U p j ^ 2 = haarR μ D U p := by
  unfold haarMu whMu haarR whR
  simp only [div_pow, Real.sq_sqrt hp]
  rw [Finset.sum_div]

private lemma coord_sum_mu_sq_le_R {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (p : Fin n) (j : Fin m) (hp : 0 ≤ haarSigmaOut U μ p p) :
    haarMu μ D U p j ^ 2 ≤ haarR μ D U p := by
  rw [← coord_sum_mu_sq_sum μ D U p hp]
  exact Finset.single_le_sum (fun l _ => sq_nonneg (haarMu μ D U p l)) (Finset.mem_univ j)

private lemma coord_sum_err_sq_bound {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hstate : def_app_sgd_state_law P n m B μ D)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) (j : Fin m) :
    haarErr B μ D U p j ^ 2 ≤ 2 + (4 / Real.pi) * (B : ℝ)
      * haarMu μ D U p j ^ 2 / haarPminus P := by
  have hP : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hR := (haar_bounds P n m B μ D hstate).1
  have hRpos : 0 < twoR μ D := lt_of_lt_of_le hP hR
  have hB : 1 ≤ B := by
    have h := hstate.1.2.2
    omega
  have hbatch := prop_app_sgd_batch_coefficient_ii B hB
  have hNpos : 0 ≤ batchConst B :=
    le_trans (by positivity) ((le_max_left _ _).trans hbatch.1)
  have hNsq : batchConst B ^ 2 ≤ (B : ℝ) := by
    have hs := Real.sq_sqrt (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
    nlinarith [Real.sqrt_nonneg (B : ℝ), hbatch.2]
  have hM := coord_sum_mean_abs_le_one (B := B) μ D U p j
  have hMsq : haarMean B μ D U p j ^ 2 ≤ 1 := by
    simpa only [one_pow, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg _) hM 2
  have hratio : batchConst B ^ 2 / twoR μ D ≤ (B : ℝ) / haarPminus P :=
    (div_le_div_of_nonneg_right hNsq hRpos.le).trans
      (div_le_div_of_nonneg_left (Nat.cast_nonneg B) hP hR)
  have hlead : (Real.sqrt (2 / Real.pi) * batchConst B * haarMu μ D U p j
      / Real.sqrt (twoR μ D)) ^ 2
      ≤ (2 / Real.pi) * ((B : ℝ) / haarPminus P) * haarMu μ D U p j ^ 2 := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / Real.pi),
      Real.sq_sqrt hRpos.le]
    calc _ = (2 / Real.pi) * (batchConst B ^ 2 / twoR μ D)
          * haarMu μ D U p j ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (sq_nonneg _)
  rw [coord_sum_err_entry]
  set t := Real.sqrt (2 / Real.pi) * batchConst B * haarMu μ D U p j
    / Real.sqrt (twoR μ D)
  change t ^ 2 ≤ _ at hlead
  have heq : (4 / Real.pi) * (B : ℝ) * haarMu μ D U p j ^ 2 / haarPminus P
      = 2 * ((2 / Real.pi) * ((B : ℝ) / haarPminus P) * haarMu μ D U p j ^ 2) := by
    ring
  rw [heq]
  nlinarith [sq_nonneg (haarMean B μ D U p j + t)]

private lemma coord_sum_bad_entry {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hstate : def_app_sgd_state_law P n m B μ D) (hk : haarKStar P ≤ kOf n m B)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (p : Fin n) (j : Fin m) :
    let c := (2 / Real.pi) * (B : ℝ) / haarPminus P
    ∫⁻ U in {U | haarPminus P / 4 < haarR μ D U p},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν
      ≤ ENNReal.ofReal ((2 + c) * (haarQ0 P / (n : ℝ) ^ 4)
        + c * (3 * haarA1 P ^ 2 / ((n : ℝ) ^ 2 * (kOf n m B : ℝ) ^ 2))) := by
  dsimp only
  let c := (2 / Real.pi) * (B : ℝ) / haarPminus P
  let s := {U : Matrix.orthogonalGroup (Fin n) ℝ | haarPminus P / 4 < haarR μ D U p}
  have hP : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hN : 0 < n := hstate.1.1
  have hprob := lem_app_sgd_deletion_iii P μ D hstate hk hN ν hν p
  have hmom := (lem_app_sgd_deletion_ii P μ D hstate hk hN ν hν p j 2
    ⟨by norm_num, by norm_num⟩).2
  have hdf : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
    norm_num [Nat.doubleFactorial]
  rw [hdf] at hmom
  norm_num only [Nat.reduceMul] at hmom
  have hpoint : ∀ U : Matrix.orthogonalGroup (Fin n) ℝ,
      haarErr B μ D U p j ^ 2 ≤ (2 + c) + c * haarMu μ D U p j ^ 4 := by
    intro U
    have h := coord_sum_err_sq_bound P μ D hstate U p j
    have heq : (4 / Real.pi) * (B : ℝ) * haarMu μ D U p j ^ 2 / haarPminus P
        = 2 * c * haarMu μ D U p j ^ 2 := by dsimp [c]; ring
    rw [heq] at h
    have hy := mul_nonneg hc (sq_nonneg (haarMu μ D U p j ^ 2 - 1))
    nlinarith
  have hrestrict : ∫⁻ U in s, ENNReal.ofReal (haarMu μ D U p j ^ 4) ∂ν
      ≤ ∫⁻ U, ENNReal.ofReal (haarMu μ D U p j ^ 4) ∂ν :=
    lintegral_mono' Measure.restrict_le_self le_rfl
  calc
    ∫⁻ U in s, ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν
      ≤ ∫⁻ U in s, ENNReal.ofReal ((2 + c) + c * haarMu μ D U p j ^ 4) ∂ν :=
        lintegral_mono fun U => ENNReal.ofReal_le_ofReal (hpoint U)
    _ = ENNReal.ofReal (2 + c) * ν s
        + ENNReal.ofReal c * ∫⁻ U in s, ENNReal.ofReal (haarMu μ D U p j ^ 4) ∂ν := by
      have heq : ∀ U : Matrix.orthogonalGroup (Fin n) ℝ,
          ENNReal.ofReal ((2 + c) + c * haarMu μ D U p j ^ 4)
            = ENNReal.ofReal (2 + c) + ENNReal.ofReal c
              * ENNReal.ofReal (haarMu μ D U p j ^ 4) := by
        intro U
        rw [ENNReal.ofReal_add (by linarith) (by positivity), ENNReal.ofReal_mul hc]
      simp_rw [heq]
      rw [lintegral_add_left measurable_const, lintegral_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal (2 + c) * ENNReal.ofReal (haarQ0 P / (n : ℝ) ^ 4)
        + ENNReal.ofReal c * ENNReal.ofReal
          (3 * haarA1 P ^ 2 / ((n : ℝ) ^ 2 * (kOf n m B : ℝ) ^ 2)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hprob zero_le) (mul_le_mul_of_nonneg_left (hrestrict.trans hmom) zero_le)
    _ = _ := by
      have hQ : 0 ≤ haarQ0 P := by unfold haarQ0; positivity
      rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 + c), ← ENNReal.ofReal_mul hc,
        ← ENNReal.ofReal_add (by positivity) (by positivity)]

private lemma coord_sum_bad_algebra (K k n m b a q t : ℝ)
    (hK : 0 ≤ K) (hk : 1 ≤ k) (hn : k ≤ n) (hm0 : 0 ≤ m) (hb0 : 0 ≤ b)
    (hm : m ≤ K * k) (hb : b ≤ K * k) (ha : 0 ≤ a) (hq : 0 ≤ q) (ht : 0 ≤ t) :
    n * m * ((2 + a * b) * (q / n ^ 4) + a * b * (t / (n ^ 2 * k ^ 2)))
      ≤ 2 * K * q + a * K ^ 2 * (q + t) := by
  have hk0 : 0 < k := by linarith
  have hn1 : 1 ≤ n := hk.trans hn
  have hn0 : 0 < n := by linarith
  have hn2 : 1 ≤ n ^ 2 := by nlinarith
  have hkn3 : k ≤ n ^ 3 := by nlinarith [mul_nonneg hn0.le (sub_nonneg.mpr hn2)]
  have hk2n3 : k ^ 2 ≤ n ^ 3 := by
    have hkn2 : k ^ 2 ≤ n ^ 2 := pow_le_pow_left₀ hk0.le hn 2
    nlinarith [mul_nonneg (sq_nonneg n) (sub_nonneg.mpr hn1)]
  have hbm : b * m ≤ K ^ 2 * k ^ 2 := by
    calc _ ≤ (K * k) * (K * k) := mul_le_mul hb hm hm0 (mul_nonneg hK hk0.le)
      _ = _ := by ring
  have h1 : m / n ^ 3 ≤ K := by
    apply (div_le_iff₀ (pow_pos hn0 3)).2
    exact hm.trans (mul_le_mul_of_nonneg_left hkn3 hK)
  have h2 : b * m / n ^ 3 ≤ K ^ 2 := by
    apply (div_le_iff₀ (pow_pos hn0 3)).2
    exact hbm.trans (mul_le_mul_of_nonneg_left hk2n3 (sq_nonneg K))
  have h3 : b * m / (n * k ^ 2) ≤ K ^ 2 := by
    apply (div_le_iff₀ (mul_pos hn0 (pow_pos hk0 2))).2
    calc _ ≤ K ^ 2 * k ^ 2 := hbm
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg (sq_nonneg K) (sq_nonneg k)) (sub_nonneg.mpr hn1)]
  calc
    _ = 2 * q * (m / n ^ 3) + a * q * (b * m / n ^ 3)
        + a * t * (b * m / (n * k ^ 2)) := by
      field_simp
      <;> ring
    _ ≤ 2 * q * K + a * q * K ^ 2 + a * t * K ^ 2 := by
      exact add_le_add
        (add_le_add (mul_le_mul_of_nonneg_left h1 (by positivity))
          (mul_le_mul_of_nonneg_left h2 (mul_nonneg ha hq)))
        (mul_le_mul_of_nonneg_left h3 (mul_nonneg ha ht))
    _ = _ := by ring

private lemma coord_sum_bad_total {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hstate : def_app_sgd_state_law P n m B μ D) (hk : haarKStar P ≤ kOf n m B)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν) :
    ∑ p, ∑ j, (∫⁻ U in {U | haarPminus P / 4 < haarR μ D U p},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν)
      ≤ ENNReal.ofReal (2 * P.K * haarQ0 P + ((2 / Real.pi) / haarPminus P)
        * P.K ^ 2 * (haarQ0 P + 3 * haarA1 P ^ 2)) := by
  let a := (2 / Real.pi) / haarPminus P
  let T := (2 + a * (B : ℝ)) * (haarQ0 P / (n : ℝ) ^ 4)
    + a * (B : ℝ) * (3 * haarA1 P ^ 2 / ((n : ℝ) ^ 2 * (kOf n m B : ℝ) ^ 2))
  have hP : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hQ : 0 ≤ haarQ0 P := by unfold haarQ0; positivity
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hT : ∀ p j, (∫⁻ U in {U | haarPminus P / 4 < haarR μ D U p},
      ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) ≤ ENNReal.ofReal T := by
    intro p j
    convert coord_sum_bad_entry P μ D hstate hk ν hν p j using 1 <;>
      dsimp [T, a] <;> congr 1 <;> ring
  have hst := hstate
  unfold def_app_sgd_state_law at hst
  obtain ⟨-, hk2, hn, hm, hB, -⟩ := hst
  have hkn : (kOf n m B : ℝ) ≤ n := by
    exact_mod_cast (show kOf n m B ≤ n by unfold kOf; omega)
  have hk1 : (1 : ℝ) ≤ kOf n m B := by exact_mod_cast (show 1 ≤ kOf n m B by omega)
  have halg := coord_sum_bad_algebra P.K (kOf n m B : ℝ) n m B a
    (haarQ0 P) (3 * haarA1 P ^ 2) (by linarith [P.one_le_K]) hk1 hkn
    (Nat.cast_nonneg m) (Nat.cast_nonneg B) hm hB ha hQ (by positivity)
  calc
    _ ≤ ∑ _p : Fin n, ∑ _j : Fin m, ENNReal.ofReal T :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun j _ => hT p j
    _ = ENNReal.ofReal ((n : ℝ) * (m : ℝ) * T) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)),
        ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      simp only [ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal halg

private lemma coord_sum_frob_sq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    frobNorm A ^ 2 = ∑ p, ∑ j, A p j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun j _ => sq_nonneg _)

private lemma coord_sum_variance_gap {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : A ≠ 0) (p : Fin n) (j : Fin m) :
    sgdSd A p j ^ 2 - frobNorm A ^ 2
      ≤ 5 * ((∑ l, A p l ^ 2) + ∑ k, A k j ^ 2) := by
  have hrow : A p j ^ 2 ≤ ∑ l, A p l ^ 2 :=
    Finset.single_le_sum (fun l _ => sq_nonneg (A p l)) (Finset.mem_univ j)
  have hcol : 0 ≤ ∑ k, A k j ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hs : sgdSd A p j ^ 2 = variance (sgdCoord A p j) (gaussBatch n m) :=
    Real.sq_sqrt (variance_nonneg _ _)
  rw [hs, lem_app_sgd_moments_ii A hA p j]
  linarith

private lemma coord_sum_third_sq {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : A ≠ 0) (p : Fin n) (j : Fin m) :
    (∫ x, (sgdCoord A p j x - A p j) ^ 3 ∂(gaussBatch n m)) ^ 2
      ≤ 80000 * A p j ^ 2 * (frobNorm A ^ 2) ^ 2
        + 5832 * frobNorm A ^ 2 * (∑ l, A p l ^ 2) * ∑ k, A k j ^ 2 := by
  have hrow : ∑ l, sgdRow A p j l ^ 2 ≤ ∑ l, A p l ^ 2 := by
    apply Finset.sum_le_sum
    intro l _
    by_cases hl : l = j <;> simp [sgdRow, hl, sq_nonneg]
  have hcol : ∑ k, sgdCol A p j k ^ 2 ≤ ∑ k, A k j ^ 2 := by
    apply Finset.sum_le_sum
    intro k _
    by_cases hk : k = p <;> simp [sgdCol, hk, sq_nonneg]
  have hF : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  have hbound : |∫ x, (sgdCoord A p j x - A p j) ^ 3 ∂(gaussBatch n m)|
      ≤ 200 * |A p j| * frobNorm A ^ 2
        + 54 * frobNorm A * Real.sqrt (∑ l, A p l ^ 2)
          * Real.sqrt (∑ k, A k j ^ 2) := by
    refine (lem_app_sgd_moments_v A hA p j).trans ?_
    gcongr
  have hr : Real.sqrt (∑ l, A p l ^ 2) ^ 2 = ∑ l, A p l ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun l _ => sq_nonneg _)
  have hc : Real.sqrt (∑ k, A k j ^ 2) ^ 2 = ∑ k, A k j ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
  calc
    _ = |∫ x, (sgdCoord A p j x - A p j) ^ 3 ∂(gaussBatch n m)| ^ 2 :=
      (sq_abs _).symm
    _ ≤ (200 * |A p j| * frobNorm A ^ 2
        + 54 * frobNorm A * Real.sqrt (∑ l, A p l ^ 2)
          * Real.sqrt (∑ k, A k j ^ 2)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hbound 2
    _ ≤ 2 * (200 * |A p j| * frobNorm A ^ 2) ^ 2
        + 2 * (54 * frobNorm A * Real.sqrt (∑ l, A p l ^ 2)
          * Real.sqrt (∑ k, A k j ^ 2)) ^ 2 := by
      nlinarith [sq_nonneg (200 * |A p j| * frobNorm A ^ 2
        - 54 * frobNorm A * Real.sqrt (∑ l, A p l ^ 2)
          * Real.sqrt (∑ k, A k j ^ 2))]
    _ = _ := by simp only [mul_pow, sq_abs, hr, hc]; ring

private lemma coord_sum_orth_mulVec {n : ℕ} (x v : Fin n → ℝ)
    (hx : x ⬝ᵥ x = 1) (hv : v ⬝ᵥ v = 1) :
    ∃ W : Matrix.orthogonalGroup (Fin n) ℝ,
      (W : Matrix (Fin n) (Fin n) ℝ) *ᵥ v = x := by
  by_cases hxv : x = v
  · exact ⟨1, by simp [hxv]⟩
  set u : Fin n → ℝ := x - v with hu
  set N : ℝ := u ⬝ᵥ u with hN
  have hN0 : N ≠ 0 := fun h => hxv (sub_eq_zero.1 ((dotProduct_self_eq_zero).1 h))
  have hNe : N = 2 - 2 * (x ⬝ᵥ v) := by
    rw [hN, hu, sub_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v x, hx, hv]
    ring
  have huv : u ⬝ᵥ v = -(N / 2) := by
    rw [hu, sub_dotProduct, hv]
    linarith
  set T : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec u u with hT
  have hTT : T * T = N • T := by
    rw [hT, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply, hN]
    ring
  have hTt : Tᵀ = T := by rw [hT, Matrix.transpose_vecMulVec]
  set W : Matrix (Fin n) (Fin n) ℝ := 1 - (2 / N) • T with hW
  have hWt : Wᵀ = W := by
    rw [hW, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hTt]
  have hWW : W * Wᵀ = 1 := by
    rw [hWt, hW, sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, hTT]
    simp only [one_mul, mul_one, smul_smul]
    have h1 : (2 / N) * ((2 / N) * N) = 2 * (2 / N) := by field_simp
    rw [h1, two_mul, add_smul]
    abel
  refine ⟨⟨W, (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).2 hWW⟩, ?_⟩
  show W *ᵥ v = x
  rw [hW, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hT,
    Matrix.vecMulVec_mulVec, huv]
  have hxu : x = v + u := by rw [hu]; abel
  conv_rhs => rw [hxu]
  simp only [op_smul_eq_smul, smul_smul]
  have h3 : (2 / N) * -(N / 2) = -1 := by field_simp
  rw [h3]
  simp

private lemma coord_sum_whitening_exists {n : ℕ} (hN : 0 < n)
    (Sg : Matrix (Fin n) (Fin n) ℝ) (hSg : Sg.PosSemidef) (p : Fin n)
    (hp : 0 < Sg p p) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, Qᵀ * Q = 1 ∧
      ∀ k, Q k ⟨0, hN⟩ = CFC.sqrt Sg k p / Real.sqrt (Sg p p) := by
  let x : Fin n → ℝ := fun k => CFC.sqrt Sg k p / Real.sqrt (Sg p p)
  let v : Fin n → ℝ := Pi.single ⟨0, hN⟩ 1
  have hx : x ⬝ᵥ x = 1 := by
    have hSS := congrFun (congrFun (aux_S_mul_self Sg hSg) p) p
    have hSym := aux_S_symm Sg
    have hsum : ∑ k, CFC.sqrt Sg k p ^ 2 = Sg p p := by
      rw [← hSS, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro k _
      have he := congrFun (congrFun hSym k) p
      simp only [Matrix.transpose_apply] at he
      rw [← he]
      ring
    simp only [x, dotProduct, ← sq, div_pow, Real.sq_sqrt hp.le]
    rw [← Finset.sum_div, hsum, div_self hp.ne']
  have hv : v ⬝ᵥ v = 1 := by simp [v]
  obtain ⟨Q, hQ⟩ := coord_sum_orth_mulVec x v hx hv
  refine ⟨Q, (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 Q.2, ?_⟩
  intro k
  have he := congrFun hQ k
  simpa [v, x] using he

private lemma coord_sum_whitened_mean {n m B : ℕ} (hN : 0 < n)
    (Sg : Matrix (Fin n) (Fin n) ℝ) (hSg : Sg.PosSemidef)
    (D : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (hp : 0 < Sg p p)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Qᵀ * Q = 1)
    (hQc : ∀ k, Q k ⟨0, hN⟩ = CFC.sqrt Sg k p / Real.sqrt (Sg p p)) (j : Fin m) :
    (∫ β, Real.sign (physGrad D (linBatch (CFC.sqrt Sg) β) p j) ∂batchLaw n m B)
      = expSignEntry n m B (whitenedState Sg D Q) ⟨0, hN⟩ j := by
  have hL : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      Real.sign (physGrad D (linBatch (CFC.sqrt Sg) β) p j)) := by
    apply aux_sign_measurable.comp
    unfold physGrad residual linBatch
    fun_prop
  have hR : Measurable (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      Real.sign (physGrad (whitenedState Sg D Q)
        (linBatch (1 : Matrix (Fin n) (Fin n) ℝ) β) ⟨0, hN⟩ j)) := by
    apply aux_sign_measurable.comp
    unfold physGrad residual linBatch
    fun_prop
  have heq := congrArg (fun ρ : Measure ℝ => ∫ x : ℝ, x ∂ρ)
    (lem_app_sgd_whitening_i (B := B) hN Sg hSg D p hp Q hQ hQc j)
  rw [integral_map hL.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) _ from
        measurable_id.aestronglyMeasurable),
    integral_map hR.aemeasurable
      (show AEStronglyMeasurable (fun x : ℝ => x) _ from
        measurable_id.aestronglyMeasurable)] at heq
  simpa only [expSignEntry, batchLaw, physGrad, residual, linBatch,
    Matrix.one_mulVec, sgdCoord, mul_assoc] using heq

private lemma coord_sum_haar_sqrt {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    CFC.sqrt (haarSigmaOut U μ)
      = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (fun k => Real.sqrt (μ k))
        * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hS : (haarSigmaOut U μ).PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal hμ).mul_mul_conjTranspose_same
      (U : Matrix (Fin n) (Fin n) ℝ)
    simpa only [haarSigmaOut, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hT : ((U : Matrix (Fin n) (Fin n) ℝ)
      * Matrix.diagonal (fun k => Real.sqrt (μ k))
      * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ).PosSemidef := by
    have hd : (Matrix.diagonal (fun k => Real.sqrt (μ k))).PosSemidef :=
      Matrix.PosSemidef.diagonal (fun k => Real.sqrt_nonneg (μ k))
    have h := hd.mul_mul_conjTranspose_same (U : Matrix (Fin n) (Fin n) ℝ)
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  apply (CFC.sqrt_eq_iff _ _ (Matrix.nonneg_iff_posSemidef.mpr hS)
    (Matrix.nonneg_iff_posSemidef.mpr hT)).2
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ
    (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul,
    ← Matrix.mul_assoc (Matrix.diagonal (fun k => Real.sqrt (μ k))),
    Matrix.diagonal_mul_diagonal]
  simp only [← sq, Real.sq_sqrt (hμ _)]
  simp only [haarSigmaOut, Matrix.mul_assoc]

private lemma coord_sum_batch_rotate {n m B : ℕ}
    (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (batchLaw n m B).map (fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
      fun a => ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ (β a).1, (β a).2))
      = batchLaw n m B := by
  have hmeas : Measurable (fun x : (Fin n → ℝ) × (Fin m → ℝ) =>
      ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1, x.2)) := by fun_prop
  have hgauss : (gaussBatch n m).map (fun x : (Fin n → ℝ) × (Fin m → ℝ) =>
      ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1, x.2)) = gaussBatch n m := by
    have h := Measure.map_prod_map (stdGaussianPi n) (stdGaussianPi m)
      (f := fun z => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) (g := id)
      (by fun_prop) measurable_id
    rw [Measure.map_id, stdGaussianPi_map_orthogonal] at h
    exact h.symm
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  unfold batchLaw
  have h := Measure.pi_map_pi (μ := fun _ : Fin B => gaussBatch n m)
    (f := fun _ : Fin B => fun x : (Fin n → ℝ) × (Fin m → ℝ) =>
      ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ x.1, x.2))
    (fun _ => hmeas.aemeasurable)
  refine h.trans ?_
  congr 1
  funext a
  exact hgauss

private lemma coord_sum_haar_mean_sqrt {n m B : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ k, 0 ≤ μ k) (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) (j : Fin m) :
    haarMean B μ D U p j = ∫ β, Real.sign
      (physGrad (haarDelta U D) (linBatch (CFC.sqrt (haarSigmaOut U μ)) β) p j)
      ∂batchLaw n m B := by
  let T := fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) =>
    fun a => ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ (β a).1, (β a).2)
  let F := fun β : Fin B → (Fin n → ℝ) × (Fin m → ℝ) => Real.sign
    (physGrad (haarDelta U D) (linBatch (CFC.sqrt (haarSigmaOut U μ)) β) p j)
  have hT : Measurable T := by dsimp [T]; fun_prop
  have hF : Measurable F := by
    dsimp [F]
    apply aux_sign_measurable.comp
    unfold physGrad residual linBatch
    fun_prop
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hmat : CFC.sqrt (haarSigmaOut U μ) * (U : Matrix (Fin n) (Fin n) ℝ)
      = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal (fun k => Real.sqrt (μ k)) := by
    rw [coord_sum_haar_sqrt μ hμ U, Matrix.mul_assoc, hUt, Matrix.mul_one]
  have hbatch : ∀ β, haarBatch μ U β
      = linBatch (CFC.sqrt (haarSigmaOut U μ)) (T β) := by
    intro β
    unfold haarBatch linBatch
    congr 1
    funext a
    simp only [T, Matrix.mulVec_mulVec, hmat]
  calc
    _ = ∫ β, F (T β) ∂batchLaw n m B := by
      unfold haarMean
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun β => by
        simp only [haarSign, Matrix.map_apply, hbatch β, F]
    _ = ∫ β, F β ∂((batchLaw n m B).map T) :=
      (integral_map hT.aemeasurable hF.aestronglyMeasurable).symm
    _ = _ := by rw [coord_sum_batch_rotate U]

private lemma coord_sum_good_state {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hstate : def_app_sgd_state_law P n m B μ D) (hk : haarKStar P ≤ kOf n m B)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p : Fin n) (j : Fin m)
    (hgood : haarR μ D U p ≤ haarPminus P / 4) :
    ∃ A : Matrix (Fin n) (Fin m) ℝ,
      A ≠ 0 ∧ frobNorm A ^ 2 = twoR μ D ∧ A ⟨0, hstate.1.1⟩ j = haarMu μ D U p j ∧
      (∑ l, A ⟨0, hstate.1.1⟩ l ^ 2) = haarR μ D U p ∧
      (∑ k, A k j ^ 2) = haarC μ D U j ∧
      frobNorm A / 2 ≤ frobNorm (sgdDeletedBlock A ⟨0, hstate.1.1⟩ j) ∧
      haarMean B μ D U p j = expSignEntry n m B A ⟨0, hstate.1.1⟩ j := by
  have hN : 0 < n := hstate.1.1
  have hμ : ∀ k, 0 ≤ μ k := by
    intro k
    exact P.c_pos.le.trans (hstate.2.2.2.2.2.1 k).1
  have hSg : (haarSigmaOut U μ).PosSemidef := by
    have h := (Matrix.PosSemidef.diagonal hμ).mul_mul_conjTranspose_same
      (U : Matrix (Fin n) (Fin n) ℝ)
    simpa only [haarSigmaOut, Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hforms := haar_forms_app_sgd P μ D hstate U p j p
  have hp : 0 < haarSigmaOut U μ p p := P.c_pos.trans_le hforms.2.2.1.1
  obtain ⟨Q, hQ, hQc⟩ := coord_sum_whitening_exists hN (haarSigmaOut U μ) hSg p hp
  let A := whitenedState (haarSigmaOut U μ) (haarDelta U D) Q
  have hw := lem_app_sgd_whitening_ii hN (haarSigmaOut U μ) hSg
    (haarDelta U D) p hp Q hQ hQc j
  have hF : frobNorm A ^ 2 = twoR μ D := by
    rw [coord_sum_frob_sq]
    exact hw.1.trans hforms.1
  have hR : 0 < twoR μ D :=
    (mul_pos P.c_pos (pow_pos P.fMin_pos 2)).trans_le (haar_bounds P n m B μ D hstate).1
  have hA : A ≠ 0 := by
    intro heq
    have hz : frobNorm A ^ 2 = 0 := by simp [heq, frobNorm]
    linarith
  have hB : 4 ≤ B := by
    have h4 : 4 ≤ kOf n m B := (le_max_left _ _).trans hk
    have hkB : kOf n m B ≤ B := by unfold kOf; omega
    omega
  have hdel := lem_app_sgd_deletion_i P μ D hstate hk hN U p j hgood Q hQ hQc
  have hwh := lem_app_sgd_whitening_iii (B := B) hN (haarSigmaOut U μ) hSg
    (haarDelta U D) p hp Q hQ hQc j
  refine ⟨A, hA, hF, hw.2.1, hw.2.2.1, hw.2.2.2, ?_, ?_⟩
  · apply hwh.2.2.2 hB
    rw [hforms.1]
    exact le_trans (by linarith : twoR μ D / 4 ≤ twoR μ D / 2) hdel
  · rw [coord_sum_haar_mean_sqrt μ hμ D U p j]
    exact coord_sum_whitened_mean hN (haarSigmaOut U μ) hSg
      (haarDelta U D) p hp Q hQ hQc j

private lemma coord_sum_measurable_mu_R {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (j : Fin m) :
    Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarMu μ D U p j) ∧
    Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarR μ D U p) := by
  have hU : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val
  have hS : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarSigmaOut U μ) :=
    (hU.matrix_mul continuous_const).matrix_mul hU.matrix_transpose
  have hD : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarDelta U D) :=
    hU.matrix_mul continuous_const
  have hW := hS.matrix_mul hD
  have hden := (hS.matrix_elem p p).measurable
  constructor
  · exact (hW.matrix_elem p j).measurable.div (Real.continuous_sqrt.measurable.comp hden)
  · exact (continuous_finset_sum _ (fun l _ => (hW.matrix_elem p l).pow 2)).measurable.div hden

private lemma coord_sum_measurable_err {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (p : Fin n) (j : Fin m) :
    Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarErr B μ D U p j) := by
  have hgrad : Continuous (fun x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      physGrad (haarDelta x.1 D) (haarBatch μ x.1 x.2) p j) := by
    unfold physGrad residual haarBatch linBatch haarDelta Matrix.mulVec dotProduct
    simp only
    fun_prop
  have hsign : Measurable Real.sign := by
    unfold Real.sign
    exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
      (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
        measurable_const)
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hmean : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarMean B μ D U p j) :=
    ((hsign.comp hgrad.measurable).stronglyMeasurable.integral_prod_right').measurable
  simp_rw [coord_sum_err_entry]
  exact hmean.sub ((measurable_const.mul (coord_sum_measurable_mu_R μ D p j).1).div_const _)

private lemma coord_sum_integral_entries {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) :
    (∫⁻ U, ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2) ∂ν) =
      ∑ p, ∑ j, ∫⁻ U, ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν := by
  have hf (p : Fin n) (j : Fin m) : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal (haarErr B μ D U p j ^ 2)) :=
    ENNReal.measurable_ofReal.comp ((coord_sum_measurable_err μ D p j).pow_const 2)
  have heq (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2) =
        ∑ p, ∑ j, ENNReal.ofReal (haarErr B μ D U p j ^ 2) := by
    rw [coord_sum_frob_sq]
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun (p : Fin n) _ => Finset.sum_nonneg fun (j : Fin m) _ =>
        sq_nonneg (haarErr B μ D U p j))]
    exact Finset.sum_congr rfl fun (p : Fin n) _ =>
      ENNReal.ofReal_sum_of_nonneg (fun (j : Fin m) _ => sq_nonneg (haarErr B μ D U p j))
  simp_rw [heq]
  rw [lintegral_finsetSum _ (fun p _ => Finset.measurable_sum _ (fun j _ => hf p j))]
  exact Finset.sum_congr rfl fun p _ => lintegral_finsetSum _ (fun j _ => hf p j)

private lemma coord_sum_split_entry {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (p : Fin n) (j : Fin m) :
    (∫⁻ U, ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) =
      (∫⁻ U in {U | haarR μ D U p ≤ haarPminus P / 4},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) +
      (∫⁻ U in {U | haarPminus P / 4 < haarR μ D U p},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) := by
  have hs : MeasurableSet {U : Matrix.orthogonalGroup (Fin n) ℝ |
      haarR μ D U p ≤ haarPminus P / 4} :=
    measurableSet_le (coord_sum_measurable_mu_R μ D p j).2 measurable_const
  have heq : {U : Matrix.orthogonalGroup (Fin n) ℝ | haarR μ D U p ≤ haarPminus P / 4}ᶜ =
      {U | haarPminus P / 4 < haarR μ D U p} := by
    ext U
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
  rw [← heq]
  exact (lintegral_add_compl _ hs).symm

private lemma coord_sum_five_sq (e a b c d f : ℝ) (h : |e| ≤ a + b + c + d + f) :
    e ^ 2 ≤ 5 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + f ^ 2) := by
  have hs : 0 ≤ a + b + c + d + f := (abs_nonneg e).trans h
  have he := pow_le_pow_left₀ (abs_nonneg e) h 2
  rw [sq_abs] at he
  nlinarith [sq_nonneg (a-b), sq_nonneg (a-c), sq_nonneg (a-d), sq_nonneg (a-f),
    sq_nonneg (b-c), sq_nonneg (b-d), sq_nonneg (b-f), sq_nonneg (c-d),
    sq_nonneg (c-f), sq_nonneg (d-f)]

private lemma coord_sum_good_abs :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (P : HaarParams) (n m B : ℕ) (μ : Fin n → ℝ)
      (D : Matrix (Fin n) (Fin m) ℝ), def_app_sgd_state_law P n m B μ D →
      haarKStar P ≤ kOf n m B → ∀ (U : Matrix.orthogonalGroup (Fin n) ℝ)
      (p : Fin n) (j : Fin m), haarR μ D U p ≤ haarPminus P / 4 →
      let f := Real.sqrt (haarPminus P)
      |haarErr B μ D U p j| ≤
        sgdC1 * Real.sqrt (85832 * haarPplus P ^ 2 * haarR μ D U p)
          / (f ^ 3 * Real.sqrt (B : ℝ)) + C₂ / (B : ℝ)
        + (B : ℝ) ^ (3 / 2 : ℝ) * |haarMu μ D U p j| ^ 3
          / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)
        + Real.sqrt (2 / Real.pi) * (Real.sqrt (B : ℝ) * |haarMu μ D U p j|
          * (5 * (haarR μ D U p + haarC μ D U j))) / f ^ 3
        + Real.sqrt (2 / Real.pi) * (4 * |haarMu μ D U p j|)
          / (f * Real.sqrt (B : ℝ)) := by
  obtain ⟨C₂, hcoord⟩ := prop_app_sgd_coordinate
  refine ⟨max C₂ 0, le_max_right _ _, ?_⟩
  intro P n m B μ D hstate hk U p j hgood
  dsimp only
  obtain ⟨A, hA, hF, hx, hrow, hcol, hdel, hmean⟩ :=
    coord_sum_good_state P μ D hstate hk U p j hgood
  let i : Fin n := ⟨0, hstate.1.1⟩
  change A i j = haarMu μ D U p j at hx
  change (∑ l, A i l ^ 2) = haarR μ D U p at hrow
  have hP : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hf : 0 < Real.sqrt (haarPminus P) := Real.sqrt_pos.2 hP
  have hF0 : 0 ≤ frobNorm A := Real.sqrt_nonneg _
  have hs0 : 0 ≤ sgdSd A i j := Real.sqrt_nonneg _
  have hs2 : sgdSd A i j ^ 2 = variance (sgdCoord A i j) (gaussBatch n m) :=
    Real.sq_sqrt (variance_nonneg _ _)
  have hvar := (lem_app_sgd_moments_iii A hA i j).1
  have hFs : frobNorm A ≤ sgdSd A i j := by rw [← hs2] at hvar; nlinarith
  have hfF : Real.sqrt (haarPminus P) ≤ frobNorm A := by
    have hl := (haar_bounds P n m B μ D hstate).1
    have he := Real.sq_sqrt hP.le
    nlinarith
  have hfden : Real.sqrt (haarPminus P) ^ 3 ≤
      sgdSd A i j * frobNorm A * (sgdSd A i j + frobNorm A) := by
    calc _ = Real.sqrt (haarPminus P) * Real.sqrt (haarPminus P)
          * Real.sqrt (haarPminus P) := by ring
      _ ≤ _ := by gcongr <;> linarith
  have hB : 4 ≤ B := by
    have h4 := (le_max_left 4 ⌈4 * haarA2 P / haarPminus P⌉₊).trans hk
    have hkB : kOf n m B ≤ B := by unfold kOf; omega
    omega
  have hb0 : (0 : ℝ) < B := by exact_mod_cast (show 0 < B by omega)
  have hC : (∑ k, A k j ^ 2) ≤ frobNorm A ^ 2 := by
    rw [coord_sum_frob_sq]
    exact Finset.sum_le_sum fun k _ =>
      Finset.single_le_sum (fun l _ => sq_nonneg (A k l)) (Finset.mem_univ j)
  have hmu : haarMu μ D U p j ^ 2 ≤ haarR μ D U p := by
    rw [← hx, ← hrow]
    exact Finset.single_le_sum (fun l _ => sq_nonneg (A i l)) (Finset.mem_univ j)
  have hr0 : 0 ≤ haarR μ D U p := (sq_nonneg _).trans hmu
  have hc0 : 0 ≤ haarC μ D U j := by
    rw [← hcol]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  have hFup : frobNorm A ^ 2 ≤ haarPplus P := hF.trans_le
    (haar_bounds P n m B μ D hstate).2.1
  have hcUp : haarC μ D U j ≤ haarPplus P := by rw [← hcol]; exact hC.trans hFup
  have hPup0 : 0 ≤ haarPplus P := (sq_nonneg (frobNorm A)).trans hFup
  have hxR : A i j ^ 2 ≤ haarR μ D U p := by simpa only [hx] using hmu
  have hm3 := coord_sum_third_sq A hA i j
  rw [hrow, hcol] at hm3
  have hm3' : (∫ x, (sgdCoord A i j x - A i j) ^ 3 ∂(gaussBatch n m)) ^ 2 ≤
      85832 * haarPplus P ^ 2 * haarR μ D U p := by
    calc _ ≤ 80000 * A i j ^ 2 * (frobNorm A ^ 2) ^ 2
          + 5832 * frobNorm A ^ 2 * haarR μ D U p * haarC μ D U j := hm3
      _ ≤ 80000 * haarR μ D U p * haarPplus P ^ 2
          + 5832 * haarPplus P * haarR μ D U p * haarPplus P := by gcongr
      _ = _ := by ring
  have hmabs : |∫ x, (sgdCoord A i j x - A i j) ^ 3 ∂(gaussBatch n m)| ≤
      Real.sqrt (85832 * haarPplus P ^ 2 * haarR μ D U p) := by
    exact (Real.sqrt_sq_eq_abs _).symm.trans_le (Real.sqrt_le_sqrt hm3')
  have hgap := coord_sum_variance_gap A hA i j
  rw [hrow, hcol] at hgap
  have hgap0 : 0 ≤ sgdSd A i j ^ 2 - frobNorm A ^ 2 := by
    nlinarith [pow_le_pow_left₀ hF0 hFs 2]
  have h := hcoord n m B A i j hB hA hdel
  have hFn : frobNorm A = Real.sqrt (twoR μ D) := by
    rw [← hF, Real.sqrt_sq hF0]
  rw [← hmean, hx, hFn] at h
  rw [coord_sum_err_entry]
  refine h.trans ?_
  rw [← hFn]
  have hC1 : 0 ≤ sgdC1 := by unfold sgdC1; positivity
  have hfs : Real.sqrt (haarPminus P) ≤ sgdSd A i j := hfF.trans hFs
  rw [hx] at hmabs
  gcongr <;> first | positivity | assumption | exact le_max_left C₂ 0

private lemma coord_sum_square_majorant (e c₁ c₂ T f b x R C : ℝ)
    (hf : 0 < f) (hb : 0 < b) (hT : 0 ≤ T) (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hx : x ^ 2 ≤ R)
    (h : |e| ≤ c₁ * Real.sqrt (T * R) / (f ^ 3 * Real.sqrt b) + c₂ / b
      + b ^ (3 / 2 : ℝ) * |x| ^ 3 / (3 * Real.sqrt (2 * Real.pi) * f ^ 3)
      + Real.sqrt (2 / Real.pi) * (Real.sqrt b * |x| * (5 * (R + C))) / f ^ 3
      + Real.sqrt (2 / Real.pi) * (4 * |x|) / (f * Real.sqrt b)) :
    e ^ 2 ≤ 5 * (((c₁ ^ 2 * T / f ^ 6) + 32 / (Real.pi * f ^ 2)) * R / b
      + c₂ ^ 2 / b ^ 2 + (1 / (18 * Real.pi * f ^ 6)) * b ^ 3 * x ^ 6
      + (100 / (Real.pi * f ^ 6)) * b * (R ^ 3 + C ^ 2 * R)) := by
  have h1 : (c₁ * Real.sqrt (T * R) / (f ^ 3 * Real.sqrt b)) ^ 2 =
      (c₁ ^ 2 * T / f ^ 6) * R / b := by
    rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt (mul_nonneg hT hR), Real.sq_sqrt hb.le]
    ring
  have hp : (b ^ (3 / 2 : ℝ)) ^ 2 = b ^ 3 := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb.le]
    norm_num
  have h3 : (b ^ (3 / 2 : ℝ) * |x| ^ 3 /
      (3 * Real.sqrt (2 * Real.pi) * f ^ 3)) ^ 2 =
      (1 / (18 * Real.pi * f ^ 6)) * b ^ 3 * x ^ 6 := by
    rw [div_pow, mul_pow, hp, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
    rw [← pow_mul, mul_comm 3 2, pow_mul, sq_abs]
    ring
  have hpoly : x ^ 2 * (R + C) ^ 2 ≤ 2 * (R ^ 3 + C ^ 2 * R) := by
    calc _ ≤ R * (R + C) ^ 2 := mul_le_mul_of_nonneg_right hx (sq_nonneg _)
      _ ≤ _ := by nlinarith [mul_nonneg hR (sq_nonneg (R - C))]
  have h4 : (Real.sqrt (2 / Real.pi) *
      (Real.sqrt b * |x| * (5 * (R + C))) / f ^ 3) ^ 2 ≤
      (100 / (Real.pi * f ^ 6)) * b * (R ^ 3 + C ^ 2 * R) := by
    rw [div_pow, mul_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / Real.pi), Real.sq_sqrt hb.le, sq_abs]
    calc _ = (50 * b / (Real.pi * f ^ 6)) * (x ^ 2 * (R + C) ^ 2) := by ring
      _ ≤ (50 * b / (Real.pi * f ^ 6)) * (2 * (R ^ 3 + C ^ 2 * R)) :=
        mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  have h5 : (Real.sqrt (2 / Real.pi) * (4 * |x|) / (f * Real.sqrt b)) ^ 2 ≤
      (32 / (Real.pi * f ^ 2)) * R / b := by
    rw [div_pow, mul_pow, mul_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 / Real.pi), Real.sq_sqrt hb.le, sq_abs]
    calc _ = (32 / (Real.pi * f ^ 2 * b)) * x ^ 2 := by ring
      _ ≤ (32 / (Real.pi * f ^ 2 * b)) * R :=
        mul_le_mul_of_nonneg_left hx (by positivity)
      _ = _ := by ring
  have he := coord_sum_five_sq _ _ _ _ _ _ h
  rw [h1, div_pow, h3] at he
  calc _ ≤ 5 * ((c₁ ^ 2 * T / f ^ 6) * R / b + c₂ ^ 2 / b ^ 2
      + (1 / (18 * Real.pi * f ^ 6)) * b ^ 3 * x ^ 6
      + (100 / (Real.pi * f ^ 6)) * b * (R ^ 3 + C ^ 2 * R)
      + (32 / (Real.pi * f ^ 2)) * R / b) := by linarith
    _ = _ := by ring

private lemma coord_sum_good_sq :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (P : HaarParams) (n m B : ℕ) (μ : Fin n → ℝ)
      (D : Matrix (Fin n) (Fin m) ℝ), def_app_sgd_state_law P n m B μ D →
      haarKStar P ≤ kOf n m B → ∀ (U : Matrix.orthogonalGroup (Fin n) ℝ)
      (p : Fin n) (j : Fin m), haarR μ D U p ≤ haarPminus P / 4 →
      let f := Real.sqrt (haarPminus P)
      haarErr B μ D U p j ^ 2 ≤ 5 *
        (((sgdC1 ^ 2 * (85832 * haarPplus P ^ 2) / f ^ 6)
          + 32 / (Real.pi * f ^ 2)) * haarR μ D U p / (B : ℝ)
        + C₂ ^ 2 / (B : ℝ) ^ 2
        + (1 / (18 * Real.pi * f ^ 6)) * (B : ℝ) ^ 3 * haarMu μ D U p j ^ 6
        + (100 / (Real.pi * f ^ 6)) * (B : ℝ) *
          (haarR μ D U p ^ 3 + (haarA2 P / (kOf n m B : ℝ)) ^ 2 * haarR μ D U p)) := by
  obtain ⟨C₂, hC₂, habs⟩ := coord_sum_good_abs
  refine ⟨C₂, hC₂, ?_⟩
  intro P n m B μ D hstate hk U p j hgood
  dsimp only
  have hforms := haar_forms_app_sgd P μ D hstate U p j p
  have hp : 0 ≤ haarSigmaOut U μ p p := P.c_pos.le.trans hforms.2.2.1.1
  have hx := coord_sum_mu_sq_le_R μ D U p j hp
  have hr : 0 ≤ haarR μ D U p := (sq_nonneg _).trans hx
  have hc : 0 ≤ haarC μ D U j := by
    rw [hforms.2.2.2.2.2.1]
    exact Finset.sum_nonneg fun k _ =>
      mul_nonneg (P.c_pos.le.trans (hstate.2.2.2.2.2.1 k).1) (sq_nonneg _)
  have hC := hforms.2.2.2.2.2.2.1
  have h := coord_sum_square_majorant _ sgdC1 C₂ (85832 * haarPplus P ^ 2)
    (Real.sqrt (haarPminus P)) B (haarMu μ D U p j) (haarR μ D U p) (haarC μ D U j)
    (Real.sqrt_pos.2 (mul_pos P.c_pos (pow_pos P.fMin_pos 2)))
    (by exact_mod_cast hstate.1.2.2) (by positivity) hr hc hx
    (habs P n m B μ D hstate hk U p j hgood)
  refine h.trans ?_
  gcongr

private lemma coord_sum_integrate_polynomial {n m B : ℕ} (P : HaarParams)
    (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
    (hstate : def_app_sgd_state_law P n m B μ D) (hk : haarKStar P ≤ kOf n m B)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (p : Fin n) (j : Fin m) (a b c d : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (∫⁻ U, ENNReal.ofReal (a * haarR μ D U p + b
      + c * haarMu μ D U p j ^ 6 + d * haarR μ D U p ^ 3) ∂ν) ≤
    ENNReal.ofReal (a * (haarA0 P / (n : ℝ)) + b
      + c * (15 * haarA1 P ^ 3 / ((n : ℝ) ^ 3 * (kOf n m B : ℝ) ^ 3))
      + d * (15 * haarA0 P ^ 3 / (n : ℝ) ^ 3)) := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hR (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ haarR μ D U p := by
    have hh := haar_forms_app_sgd P μ D hstate U p j p
    exact (sq_nonneg _).trans (coord_sum_mu_sq_le_R μ D U p j
      (P.c_pos.le.trans hh.2.2.1.1))
  have hm := coord_sum_measurable_mu_R μ D p j
  have hrm := ENNReal.measurable_ofReal.comp hm.2
  have hmm := ENNReal.measurable_ofReal.comp (hm.1.pow_const 6)
  have hr3m := ENNReal.measurable_ofReal.comp (hm.2.pow_const 3)
  have hma : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal a * ENNReal.ofReal (haarR μ D U p)) := measurable_const.mul hrm
  have hmc : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal c * ENNReal.ofReal (haarMu μ D U p j ^ 6)) := measurable_const.mul hmm
  have hmb : Measurable (fun _U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal b) := measurable_const
  have hL : 0 < P.L := P.c_pos.trans_le P.c_le_L
  have hA0 : 0 ≤ haarA0 P := div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) P.c_pos.le
  have hA1 : 0 ≤ haarA1 P := div_nonneg (mul_nonneg (sq_nonneg _) P.Ccol_pos.le) P.c_pos.le
  have hm1 := (lem_app_sgd_deletion_ii P μ D hstate hk hstate.1.1 ν hν p j 1
    ⟨by norm_num, by norm_num⟩).1
  have hm3 := lem_app_sgd_deletion_ii P μ D hstate hk hstate.1.1 ν hν p j 3
    ⟨by norm_num, by norm_num⟩
  norm_num [Nat.doubleFactorial] at hm1 hm3
  have heq (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      ENNReal.ofReal (a * haarR μ D U p + b + c * haarMu μ D U p j ^ 6
        + d * haarR μ D U p ^ 3) =
      ENNReal.ofReal a * ENNReal.ofReal (haarR μ D U p) + ENNReal.ofReal b
        + ENNReal.ofReal c * ENNReal.ofReal (haarMu μ D U p j ^ 6)
        + ENNReal.ofReal d * ENNReal.ofReal (haarR μ D U p ^ 3) := by
    have hr := hR U
    rw [ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_add (by positivity) hb,
      ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hc, ENNReal.ofReal_mul hd]
  have hsumab : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal a * ENNReal.ofReal (haarR μ D U p) + ENNReal.ofReal b) := hma.add hmb
  have hsumabc : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal a * ENNReal.ofReal (haarR μ D U p) + ENNReal.ofReal b
      + ENNReal.ofReal c * ENNReal.ofReal (haarMu μ D U p j ^ 6)) := hsumab.add hmc
  simp_rw [heq]
  rw [lintegral_add_left hsumabc,
    lintegral_add_left hsumab,
    lintegral_add_left hma, lintegral_const,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, measure_univ, mul_one]
  refine (add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hm1 zero_le) le_rfl)
    (mul_le_mul_of_nonneg_left hm3.2 zero_le))
    (mul_le_mul_of_nonneg_left hm3.1 zero_le)).trans_eq ?_
  rw [← ENNReal.ofReal_mul ha, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_mul hd,
    ← ENNReal.ofReal_add (by positivity) hb,
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

private lemma coord_sum_good_algebra (K k n m B a b c d t u v w : ℝ)
    (hK : 0 ≤ K) (hk : 1 ≤ k) (hn : k ≤ n) (hB : k ≤ B)
    (hn' : n ≤ K * k) (hm : m ≤ K * k) (hB' : B ≤ K * k)
    (hm0 : 0 ≤ m) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (ht : 0 ≤ t) (hu : 0 ≤ u) (hw : 0 ≤ w) :
    n * m * ((a / B + d * B * (v / k) ^ 2) * (t / n) + b / B ^ 2
      + c * B ^ 3 * (u / (n ^ 3 * k ^ 3)) + d * B * (w / n ^ 3)) ≤
      K * a * t + K ^ 2 * b + K ^ 4 * c * u + K ^ 2 * d * (v ^ 2 * t + w) := by
  have hk0 : 0 < k := by linarith
  have hn0 : 0 < n := hk0.trans_le hn
  have hB0 : 0 < B := hk0.trans_le hB
  have hmb : m / B ≤ K := (div_le_iff₀ hB0).2
    (hm.trans (mul_le_mul_of_nonneg_left hB hK))
  have hnm : n * m / B ^ 2 ≤ K ^ 2 := by
    apply (div_le_iff₀ (pow_pos hB0 2)).2
    calc _ ≤ (K * k) * (K * k) := mul_le_mul hn' hm hm0 (by positivity)
      _ ≤ _ := by nlinarith [pow_le_pow_left₀ hk0.le hB 2,
        mul_nonneg (sq_nonneg K) (sub_nonneg.mpr (pow_le_pow_left₀ hk0.le hB 2))]
  have hmbk : m * B / k ^ 2 ≤ K ^ 2 := by
    apply (div_le_iff₀ (pow_pos hk0 2)).2
    calc _ ≤ (K * k) * (K * k) := mul_le_mul hm hB' hB0.le (by positivity)
      _ = _ := by ring
  have hmbn : m * B / n ^ 2 ≤ K ^ 2 := by
    apply (div_le_iff₀ (pow_pos hn0 2)).2
    calc _ ≤ K ^ 2 * k ^ 2 := (div_le_iff₀ (pow_pos hk0 2)).1 hmbk
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hk0.le hn 2) (sq_nonneg K)
  have hkN : k ≤ n ^ 2 := by nlinarith
  have hcube : m * B ^ 3 / (n ^ 2 * k ^ 3) ≤ K ^ 4 := by
    apply (div_le_iff₀ (by positivity : 0 < n ^ 2 * k ^ 3)).2
    calc _ ≤ (K * k) * (K * k) ^ 3 := by gcongr
      _ = K ^ 4 * k ^ 4 := by ring
      _ ≤ K ^ 4 * (n ^ 2 * k ^ 3) := by
        have h := mul_le_mul_of_nonneg_right hkN (pow_nonneg hk0.le 3)
        nlinarith [mul_le_mul_of_nonneg_left h (pow_nonneg hK 4)]
  calc
    _ = a * t * (m / B) + b * (n * m / B ^ 2)
        + c * u * (m * B ^ 3 / (n ^ 2 * k ^ 3))
        + d * v ^ 2 * t * (m * B / k ^ 2) + d * w * (m * B / n ^ 2) := by
      field_simp
      <;> ring
    _ ≤ a * t * K + b * K ^ 2 + c * u * K ^ 4
        + d * v ^ 2 * t * K ^ 2 + d * w * K ^ 2 := by gcongr
    _ = _ := by ring

private lemma coord_sum_good_total (P : HaarParams) :
    ∃ CG : ℝ, 0 ≤ CG ∧ ∀ (n m B : ℕ) (μ : Fin n → ℝ)
      (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)),
      IsOrthHaar ν → def_app_sgd_state_law P n m B μ D → haarKStar P ≤ kOf n m B →
      ∑ p, ∑ j, (∫⁻ U in {U | haarR μ D U p ≤ haarPminus P / 4},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) ≤ ENNReal.ofReal CG := by
  obtain ⟨C₂, hC₂, hsq⟩ := coord_sum_good_sq
  let f := Real.sqrt (haarPminus P)
  let a := sgdC1 ^ 2 * (85832 * haarPplus P ^ 2) / f ^ 6 + 32 / (Real.pi * f ^ 2)
  let c := 1 / (18 * Real.pi * f ^ 6)
  let d := 100 / (Real.pi * f ^ 6)
  let H := P.K * a * haarA0 P + P.K ^ 2 * C₂ ^ 2
    + P.K ^ 4 * c * (15 * haarA1 P ^ 3)
    + P.K ^ 2 * d * (haarA2 P ^ 2 * haarA0 P + 15 * haarA0 P ^ 3)
  have hL : 0 < P.L := P.c_pos.trans_le P.c_le_L
  have hK : 0 ≤ P.K := by linarith [P.one_le_K]
  have hf : 0 < f := Real.sqrt_pos.2 (mul_pos P.c_pos (pow_pos P.fMin_pos 2))
  have hA0 : 0 ≤ haarA0 P := div_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _)) P.c_pos.le
  have hA1 : 0 ≤ haarA1 P := div_nonneg (mul_nonneg (sq_nonneg _) P.Ccol_pos.le) P.c_pos.le
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  refine ⟨5 * H, by positivity, ?_⟩
  intro n m B μ D ν hν hstate hk
  let k : ℝ := kOf n m B
  let T := (a / (B : ℝ) + d * (B : ℝ) * (haarA2 P / k) ^ 2) * (haarA0 P / (n : ℝ))
    + C₂ ^ 2 / (B : ℝ) ^ 2
    + c * (B : ℝ) ^ 3 * (15 * haarA1 P ^ 3 / ((n : ℝ) ^ 3 * k ^ 3))
    + d * (B : ℝ) * (15 * haarA0 P ^ 3 / (n : ℝ) ^ 3)
  have hb : (0 : ℝ) < B := by exact_mod_cast hstate.1.2.2
  have hentry (p : Fin n) (j : Fin m) :
      (∫⁻ U in {U | haarR μ D U p ≤ haarPminus P / 4},
        ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) ≤ ENNReal.ofReal (5 * T) := by
    let g := fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (a / (B : ℝ) + d * (B : ℝ) * (haarA2 P / k) ^ 2) * haarR μ D U p
        + C₂ ^ 2 / (B : ℝ) ^ 2 + (c * (B : ℝ) ^ 3) * haarMu μ D U p j ^ 6
        + (d * (B : ℝ)) * haarR μ D U p ^ 3
    have hs : MeasurableSet {U : Matrix.orthogonalGroup (Fin n) ℝ |
        haarR μ D U p ≤ haarPminus P / 4} :=
      measurableSet_le (coord_sum_measurable_mu_R μ D p j).2 measurable_const
    have hpoint (U : Matrix.orthogonalGroup (Fin n) ℝ)
        (hU : haarR μ D U p ≤ haarPminus P / 4) : haarErr B μ D U p j ^ 2 ≤ 5 * g U := by
      have h := hsq P n m B μ D hstate hk U p j hU
      change haarErr B μ D U p j ^ 2 ≤ 5 *
        (a * haarR μ D U p / (B : ℝ) + C₂ ^ 2 / (B : ℝ) ^ 2
          + c * (B : ℝ) ^ 3 * haarMu μ D U p j ^ 6
          + d * (B : ℝ) * (haarR μ D U p ^ 3 + (haarA2 P / k) ^ 2 * haarR μ D U p)) at h
      convert h using 1 <;> dsimp [g] <;> ring
    have hi := coord_sum_integrate_polynomial P μ D hstate hk ν hν p j
      (a / (B : ℝ) + d * (B : ℝ) * (haarA2 P / k) ^ 2)
      (C₂ ^ 2 / (B : ℝ) ^ 2) (c * (B : ℝ) ^ 3) (d * (B : ℝ))
      (by positivity) (by positivity) (by positivity) (by positivity)
    change (∫⁻ U, ENNReal.ofReal (g U) ∂ν) ≤ ENNReal.ofReal T at hi
    calc
      _ ≤ ∫⁻ U in {U | haarR μ D U p ≤ haarPminus P / 4}, ENNReal.ofReal (5 * g U) ∂ν :=
        setLIntegral_mono' hs fun U hU => ENNReal.ofReal_le_ofReal (hpoint U hU)
      _ ≤ ∫⁻ U, ENNReal.ofReal (5 * g U) ∂ν := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal 5 * ∫⁻ U, ENNReal.ofReal (g U) ∂ν := by
        simp_rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal 5 * ENNReal.ofReal T := mul_le_mul_of_nonneg_left hi zero_le
      _ = _ := (ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)).symm
  have hst := hstate
  unfold def_app_sgd_state_law at hst
  obtain ⟨-, hk2, hn, hm, hB, -⟩ := hst
  have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ kOf n m B by omega)
  have hkn : k ≤ n := by dsimp [k]; exact_mod_cast (show kOf n m B ≤ n by unfold kOf; omega)
  have hkb : k ≤ B := by dsimp [k]; exact_mod_cast (show kOf n m B ≤ B by unfold kOf; omega)
  have halg := coord_sum_good_algebra P.K k n m B a (C₂ ^ 2) c d (haarA0 P)
    (15 * haarA1 P ^ 3) (haarA2 P) (15 * haarA0 P ^ 3) hK hk1 hkn hkb hn hm hB
    (Nat.cast_nonneg m) ha (sq_nonneg _) hc hd hA0 (by positivity) (by positivity)
  change (n : ℝ) * (m : ℝ) * T ≤ H at halg
  calc
    _ ≤ ∑ _p : Fin n, ∑ _j : Fin m, ENNReal.ofReal (5 * T) :=
      Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun j _ => hentry p j
    _ = ENNReal.ofReal ((n : ℝ) * (m : ℝ) * (5 * T)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg m)),
        ENNReal.ofReal_mul (Nat.cast_nonneg n)]
      simp only [ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [halg])

/-! ## `prop:app-sgd-coordinate-sum` -/

/-- `prop:app-sgd-coordinate-sum`: there is an admissible `C_E` (depending on `P` only) with
`E_U‖E‖²_F ≤ C_E` for every Haar state with `k ≥ k_*`. cr-2026-10-23. Source `section.tex` l. 850-856. LaTeX statement (verbatim):
```latex
\begin{proposition}[Coordinate errors in Frobenius norm]\label{prop:app-sgd-coordinate-sum}
In the Haar model with $k\ge k_*$, let $D_v\defeq\diag(v_1,\dots,v_{\Nout})$ and
\[
E\defeq M(U)-\sqrt{\frac2\pi}\,\frac{\mathcal N_B}{\sqrt{2\cR}}\,D_v^{-1/2}U\Lambda D .
\]
There is an admissible constant $C_E$ such that $\EE_U\norm E_\F^2\le C_E$.
\end{proposition}
``` -/
theorem prop_app_sgd_coordinate_sum (P : HaarParams) :
    ∃ CE : ℝ, 0 ≤ CE ∧ ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
      (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)), IsOrthHaar ν →
      def_app_sgd_state_law P n m B μ D → haarKStar P ≤ kOf n m B →
      ∫⁻ U, ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2) ∂ν ≤ ENNReal.ofReal CE := by
  obtain ⟨CG, hCG, hgood⟩ := coord_sum_good_total P
  let CB := 2 * P.K * haarQ0 P + ((2 / Real.pi) / haarPminus P)
    * P.K ^ 2 * (haarQ0 P + 3 * haarA1 P ^ 2)
  have hK : 0 ≤ P.K := by linarith [P.one_le_K]
  have hQ : 0 ≤ haarQ0 P := by unfold haarQ0; positivity
  have hP : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hCB : 0 ≤ CB := by dsimp [CB]; positivity
  refine ⟨CG + CB, add_nonneg hCG hCB, ?_⟩
  intro n m B μ D ν hν hstate hk
  rw [coord_sum_integral_entries]
  calc
    _ = (∑ p, ∑ j, ∫⁻ U in {U | haarR μ D U p ≤ haarPminus P / 4},
          ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν)
        + (∑ p, ∑ j, ∫⁻ U in {U | haarPminus P / 4 < haarR μ D U p},
          ENNReal.ofReal (haarErr B μ D U p j ^ 2) ∂ν) := by
      simp_rw [coord_sum_split_entry P μ D ν, Finset.sum_add_distrib]
    _ ≤ ENNReal.ofReal CG + ENNReal.ofReal CB :=
      add_le_add (hgood n m B μ D ν hν hstate hk)
        (coord_sum_bad_total P μ D hstate hk ν hν)
    _ = _ := (ENNReal.ofReal_add hCG hCB).symm

/-! ## `thm:app-sgd-half-drift` -/

private lemma half_inv_sqrt_sq_bound (c v w : ℝ) (hc : 0 < c) (hv : c ≤ v)
    (hw : c ≤ w) :
    ((Real.sqrt v)⁻¹ - (Real.sqrt w)⁻¹) ^ 2 ≤ (v - w) ^ 2 / (4 * c ^ 3) := by
  have hv0 : 0 < v := hc.trans_le hv
  have hw0 : 0 < w := hc.trans_le hw
  have hsv : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hsw : 0 < Real.sqrt w := Real.sqrt_pos.mpr hw0
  have hcsv : Real.sqrt c ≤ Real.sqrt v := Real.sqrt_le_sqrt hv
  have hcsw : Real.sqrt c ≤ Real.sqrt w := Real.sqrt_le_sqrt hw
  have hc0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hden : 4 * c ^ 3 ≤ v * w * (Real.sqrt v + Real.sqrt w) ^ 2 := by
    have hprod : c * c ≤ v * w := mul_le_mul hv hw hc.le hv0.le
    have hsum : 2 * Real.sqrt c ≤ Real.sqrt v + Real.sqrt w := by
      simpa [two_mul] using add_le_add hcsv hcsw
    have hsum2 : (2 * Real.sqrt c) ^ 2 ≤ (Real.sqrt v + Real.sqrt w) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hsum 2
    have hsqc : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc.le
    nlinarith [mul_nonneg (sub_nonneg.mpr hprod) (sq_nonneg (Real.sqrt v + Real.sqrt w)),
      mul_nonneg (mul_nonneg hc.le hc.le) (sub_nonneg.mpr hsum2)]
  have hid : ((Real.sqrt v)⁻¹ - (Real.sqrt w)⁻¹) ^ 2
      = (v - w) ^ 2 / (v * w * (Real.sqrt v + Real.sqrt w) ^ 2) := by
    have hva : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0.le
    have hwa : Real.sqrt w ^ 2 = w := Real.sq_sqrt hw0.le
    have hdiff : (Real.sqrt w - Real.sqrt v) * (Real.sqrt w + Real.sqrt v) = w - v := by
      nlinarith
    have hcore : (Real.sqrt w - Real.sqrt v) ^ 2 * v * w
          * (Real.sqrt v + Real.sqrt w) ^ 2
        = Real.sqrt w ^ 2 * Real.sqrt v ^ 2 * (v - w) ^ 2 := by
      calc
        _ = v * w * ((Real.sqrt w - Real.sqrt v)
            * (Real.sqrt w + Real.sqrt v)) ^ 2 := by ring
        _ = v * w * (w - v) ^ 2 := by rw [hdiff]
        _ = _ := by rw [hwa, hva]; ring
    rw [inv_sub_inv]
    field_simp [hsv.ne', hsw.ne', hv0.ne', hw0.ne']
    · convert hcore using 1 <;> ring
    · exact hsv.ne'
    · exact hsw.ne'
  rw [hid]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden

private lemma half_fluct_energy_row {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν) (p : Fin n) :
    ∫⁻ U, ENNReal.ofReal ((haarSigmaOut U μ p p - muBar μ) ^ 2
        * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2) ∂ν
      ≤ ENNReal.ofReal ((60 * P.L ^ 4 + 3 * haarH0 P ^ 2) / (2 * (n : ℝ) ^ 2)) := by
  have hst := hstate
  unfold def_app_sgd_state_law at hst
  obtain ⟨-, hn2k, -, -, -, hμ, -, -, -⟩ := hst
  have hkn : kOf n m B ≤ n := by unfold kOf; exact min_le_left _ _
  have hn2 : 2 ≤ n := hn2k.trans hkn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let Λ : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal μ
  let g : (Fin n → ℝ) → ℝ := fun ω =>
    ((dotProduct ω (Λ.mulVec ω) - muBar μ) ^ 4
      + (dotProduct ω ((TD μ D).mulVec ω)) ^ 2) / 2
  have hgc : Continuous g := by
    dsimp [g]
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hg0 : ∀ ω, 0 ≤ g ω := fun ω => by dsimp [g]; positivity
  have hlo : (Λ - P.c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    have heq : Λ - P.c • (1 : Matrix (Fin n) (Fin n) ℝ)
        = Matrix.diagonal (fun i => μ i - P.c) := by
      ext i j
      by_cases hij : i = j <;> simp [Λ, hij, Matrix.one_apply]
    rw [heq]
    exact Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (hμ i).1
  have hhi : (P.L • (1 : Matrix (Fin n) (Fin n) ℝ) - Λ).PosSemidef := by
    have heq : P.L • (1 : Matrix (Fin n) (Fin n) ℝ) - Λ
        = Matrix.diagonal (fun i => P.L - μ i) := by
      ext i j
      by_cases hij : i = j <;> simp [Λ, hij, Matrix.one_apply]
    rw [heq]
    exact Matrix.PosSemidef.diagonal fun i => sub_nonneg.mpr (hμ i).2
  have htrace : Matrix.trace Λ / (n : ℝ) = muBar μ := by
    simp [Λ, Matrix.trace, muBar]
  have hfluct : ∫ ω, (dotProduct ω (Λ.mulVec ω) - muBar μ) ^ 4 ∂(sphereGauss n)
      ≤ 60 * P.L ^ 4 / (n : ℝ) ^ 2 := by
    rw [← htrace]
    exact lem_app_sgd_sphere_v n hn2 P.c P.L P.c_pos.le Λ hlo hhi
  have hT0 : 0 ≤ (TD μ D).trace := (TD_psd μ D).trace_nonneg
  have hTH : (TD μ D).trace ≤ haarH0 P := (haar_bounds P n m B μ D hstate).2.2.1
  have hH0 : 0 ≤ haarH0 P := by unfold haarH0; positivity
  have henergy : ∫ ω, (dotProduct ω ((TD μ D).mulVec ω)) ^ 2 ∂(sphereGauss n)
      ≤ 3 * haarH0 P ^ 2 / (n : ℝ) ^ 2 := by
    have hs := lem_app_sgd_sphere_iii n 2 hn2 ⟨by norm_num, by norm_num⟩
      (TD μ D) (TD_psd μ D)
    norm_num [Nat.doubleFactorial] at hs
    have hdq : (n : ℝ) ^ 2 ≤ dq n 2 := dq_ge_pow n 2
    have hdq0 : 0 < dq n 2 := lt_of_lt_of_le (pow_pos hn0 2) hdq
    calc
      _ ≤ 3 * (TD μ D).trace ^ 2 / dq n 2 := hs
      _ ≤ 3 * haarH0 P ^ 2 / dq n 2 := by
        apply div_le_div_of_nonneg_right _ hdq0.le
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hT0 hTH 2) (by norm_num)
      _ ≤ _ := div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (sq_nonneg _))
        (pow_pos hn0 2) hdq
  have hint : ∫ ω, g ω ∂(sphereGauss n)
      ≤ (60 * P.L ^ 4 + 3 * haarH0 P ^ 2) / (2 * (n : ℝ) ^ 2) := by
    dsimp [g]
    rw [integral_div, integral_add
      (sphere_integrable _ (by unfold dotProduct Matrix.mulVec; fun_prop))
      (sphere_integrable _ (by unfold dotProduct Matrix.mulVec; fun_prop))]
    calc
      _ ≤ (60 * P.L ^ 4 / (n : ℝ) ^ 2 + 3 * haarH0 P ^ 2 / (n : ℝ) ^ 2) / 2 :=
        div_le_div_of_nonneg_right (add_le_add hfluct henergy) (by norm_num)
      _ = _ := by ring
  refine le_trans (lintegral_mono fun U => ENNReal.ofReal_le_ofReal ?_)
    (lintegral_row_le hν p g hgc hg0 _ hint)
  have hv : haarSigmaOut U μ p p
      = dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)
          (Λ.mulVec (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)) := by
    rw [(haar_forms_app_sgd P μ D hstate U p ⟨0, hstate.1.2.1⟩ p).2.1]
    simp only [Λ]
    unfold dotProduct
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mulVec_diagonal]
    ring
  have he : ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2
      = dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)
          ((TD μ D).mulVec (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)) := by
    rw [quad_TD]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [Matrix.mul_diagonal]
  rw [hv, he]
  dsimp [g]
  nlinarith [sq_nonneg ((dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)
    (Λ.mulVec (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)) - muBar μ) ^ 2
      - dotProduct (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)
        ((TD μ D).mulVec (fun k => (U : Matrix (Fin n) (Fin n) ℝ) p k)))]

private lemma half_frob_sq_orth_left {n m : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Matrix (Fin n) (Fin m) ℝ) :
    frobNorm ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A) ^ 2 = frobNorm A ^ 2 := by
  rw [coord_sum_frob_sq, coord_sum_frob_sq, aux_sum_sq_eq_trace, aux_sum_sq_eq_trace]
  have hUU : (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 U.2
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc A Aᵀ,
    Matrix.mul_assoc (A * Aᵀ), hUU, Matrix.mul_one]

private lemma half_frob_sq_add {n m : ℕ} (A C : Matrix (Fin n) (Fin m) ℝ) :
    frobNorm (A + C) ^ 2 ≤ 2 * frobNorm A ^ 2 + 2 * frobNorm C ^ 2 := by
  simp only [coord_sum_frob_sq, Matrix.add_apply, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  nlinarith [sq_nonneg (A i j - C i j)]

private lemma half_drift_decomp {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (hR : 0 ≤ twoR μ D) (hm : 0 < muBar μ) :
    haarDriftErr B μ D U = (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      (haarErr B μ D U
        + (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
          (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹
              - (Real.sqrt (muBar μ))⁻¹)
            * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)) := by
  let a := Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)
  let b := (Real.sqrt (muBar μ))⁻¹
  let V := Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹)
  let W := Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹ - b)
  let X := (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D
  let Y := Matrix.diagonal μ * D
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hUX : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * X = Y := by
    dsimp [X, Y]
    rw [Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ) (Matrix.diagonal μ) D,
      ← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ
        (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  have hV : V = W + b • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    by_cases hij : i = j <;> simp [V, W, b, hij, Matrix.one_apply]
  have hLB : LB B μ D = a * b := by
    dsimp [a, b]
    unfold LB
    rw [Real.sqrt_mul hR]
    ring
  unfold haarDriftErr haarErr
  simp only [Matrix.mul_assoc]
  dsimp only [a, b, V, W, X, Y] at hV hUX hLB ⊢
  have hUX' : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
      ((U : Matrix (Fin n) (Fin n) ℝ) * (Matrix.diagonal μ * D))
      = Matrix.diagonal μ * D := by
    simpa only [Matrix.mul_assoc] using hUX
  rw [hLB, hV, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, smul_add,
    Matrix.mul_add, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.mul_smul, hUX']
  module

private lemma half_correction_sq {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    frobNorm ((Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
        (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹
            - (Real.sqrt (muBar μ))⁻¹)
          * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)) ^ 2
      = (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) ^ 2
        * ∑ p, ((Real.sqrt (haarSigmaOut U μ p p))⁻¹
            - (Real.sqrt (muBar μ))⁻¹) ^ 2
          * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2 := by
  rw [coord_sum_frob_sq]
  simp only [Matrix.mul_assoc, Matrix.smul_apply, smul_eq_mul, Matrix.diagonal_mul, mul_pow,
    ← Finset.mul_sum]

private lemma half_correction_integral {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν) :
    ∫⁻ U, ENNReal.ofReal (frobNorm
        ((Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
          (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹
              - (Real.sqrt (muBar μ))⁻¹)
            * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)) ^ 2) ∂ν
      ≤ ENNReal.ofReal ((2 / Real.pi) * P.K * (60 * P.L ^ 4 + 3 * haarH0 P ^ 2)
          / (8 * haarPminus P * P.c ^ 3)) := by
  have hb := haar_bounds P n m B μ D hstate
  have hPm : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hR : 0 < twoR μ D := hPm.trans_le hb.1
  have hm : P.c ≤ muBar μ := hb.2.2.2.1
  have hBnat : 1 ≤ B := hstate.1.2.2
  have hNsq : batchConst B ^ 2 ≤ (B : ℝ) := by
    have hN0 : 0 ≤ batchConst B := le_trans (by positivity) (gb_lower_first B hBnat)
    have h := pow_le_pow_left₀ hN0 (gb_upper B hBnat) 2
    simpa only [Real.sq_sqrt (Nat.cast_nonneg B)] using h
  let qfac : ℝ := (2 / Real.pi) * (B : ℝ) / haarPminus P / (4 * P.c ^ 3)
  let rowbd : ℝ := (60 * P.L ^ 4 + 3 * haarH0 P ^ 2) / (2 * (n : ℝ) ^ 2)
  have hqfac : 0 ≤ qfac := by
    dsimp [qfac]
    exact div_nonneg (div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg B)) hPm.le)
      (mul_nonneg (by norm_num) (pow_nonneg P.c_pos.le 3))
  have hrowbd : 0 ≤ rowbd := by
    dsimp [rowbd]
    exact div_nonneg
      (add_nonneg (mul_nonneg (by norm_num) (pow_nonneg (P.c_pos.le.trans P.c_le_L) 4))
        (mul_nonneg (by norm_num) (sq_nonneg _)))
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hsqrtR : Real.sqrt (twoR μ D) ^ 2 = twoR μ D := Real.sq_sqrt hR.le
  have ha : (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) ^ 2
      ≤ (2 / Real.pi) * (B : ℝ) / haarPminus P := by
    rw [div_pow, mul_pow, hsqrt, hsqrtR]
    apply (div_le_div_iff₀ hR hPm).2
    calc
      (2 / Real.pi * batchConst B ^ 2) * haarPminus P
        ≤ (2 / Real.pi * batchConst B ^ 2) * twoR μ D :=
          mul_le_mul_of_nonneg_left hb.1 (mul_nonneg (by positivity) (sq_nonneg _))
      _ ≤ (2 / Real.pi * (B : ℝ)) * twoR μ D :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNsq (by positivity)) hR.le
  have hpoint (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      frobNorm ((Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
          (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹
              - (Real.sqrt (muBar μ))⁻¹)
            * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)) ^ 2
        ≤ qfac * ∑ p, (haarSigmaOut U μ p p - muBar μ) ^ 2
          * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2 := by
    rw [half_correction_sq]
    have hforms := fun p =>
      haar_forms_app_sgd P μ D hstate U p ⟨0, hstate.1.2.1⟩ p
    have hsum : ∑ p, ((Real.sqrt (haarSigmaOut U μ p p))⁻¹
          - (Real.sqrt (muBar μ))⁻¹) ^ 2
          * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2
        ≤ ∑ p, ((haarSigmaOut U μ p p - muBar μ) ^ 2 / (4 * P.c ^ 3))
          * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2 := by
      apply Finset.sum_le_sum
      intro p _
      exact mul_le_mul_of_nonneg_right
        (half_inv_sqrt_sq_bound P.c _ _ P.c_pos (hforms p).2.2.1.1 hm)
        (Finset.sum_nonneg fun j _ => sq_nonneg _)
    calc
      _ ≤ ((2 / Real.pi) * (B : ℝ) / haarPminus P) *
          ∑ p, ((Real.sqrt (haarSigmaOut U μ p p))⁻¹
            - (Real.sqrt (muBar μ))⁻¹) ^ 2
            * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2 :=
        mul_le_mul_of_nonneg_right ha (Finset.sum_nonneg fun p _ => mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg fun j _ => sq_nonneg _))
      _ ≤ ((2 / Real.pi) * (B : ℝ) / haarPminus P) *
          ∑ p, ((haarSigmaOut U μ p p - muBar μ) ^ 2 / (4 * P.c ^ 3))
            * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2 :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = _ := by
        dsimp [qfac]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _
        field_simp [P.c_pos.ne', hPm.ne']
  let F : Fin n → Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun p U =>
    (haarSigmaOut U μ p p - muBar μ) ^ 2
      * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2
  have hF0 : ∀ p U, 0 ≤ F p U := fun p U => by dsimp [F]; positivity
  have hmeas (p : Fin n) : Measurable (fun U => ENNReal.ofReal (F p U)) := by
    apply ENNReal.measurable_ofReal.comp
    have hU : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (U : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val
    have hS : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarSigmaOut U μ) := by
      unfold haarSigmaOut
      fun_prop
    have hX : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) := by fun_prop
    change Measurable fun U => (haarSigmaOut U μ p p - muBar μ) ^ 2
      * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2
    exact (((hS.matrix_elem p p).sub continuous_const).pow 2 |>.mul
      (continuous_finset_sum _ fun j _ => (hX.matrix_elem p j).pow 2)).measurable
  calc
    _ ≤ ∫⁻ U, ENNReal.ofReal (qfac * ∑ p, F p U) ∂ν :=
      lintegral_mono fun U => ENNReal.ofReal_le_ofReal (hpoint U)
    _ = ENNReal.ofReal qfac * ∑ p, ∫⁻ U, ENNReal.ofReal (F p U) ∂ν := by
      simp_rw [ENNReal.ofReal_mul hqfac, ENNReal.ofReal_sum_of_nonneg
        (fun (p : Fin n) _ => hF0 p _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum _ (fun p _ => hmeas p)]
    _ ≤ ENNReal.ofReal qfac * ∑ _p : Fin n, ENNReal.ofReal rowbd := by
      apply mul_le_mul_of_nonneg_left _ zero_le
      exact Finset.sum_le_sum fun p _ => half_fluct_energy_row P μ D hstate ν hν p
    _ = ENNReal.ofReal (qfac * ((n : ℝ) * rowbd)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ENNReal.ofReal_natCast]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg n),
        ← ENNReal.ofReal_mul hqfac]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hnk : kOf n m B ≤ n := by unfold kOf; exact min_le_left _ _
      have hBn : (B : ℝ) ≤ P.K * (n : ℝ) := by
        exact (hstate.2.2.2.2.1).trans
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hnk) (by linarith [P.one_le_K]))
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hstate.1.1
      have hBdiv : (B : ℝ) / (n : ℝ) ≤ P.K := by
        exact (div_le_iff₀ hn0).2 (by simpa [mul_comm] using hBn)
      dsimp [qfac, rowbd]
      have hQ : 0 ≤ 60 * P.L ^ 4 + 3 * haarH0 P ^ 2 := by positivity
      have hcoef : 0 ≤ (2 / Real.pi) / (8 * haarPminus P * P.c ^ 3) :=
        div_nonneg (by positivity)
          (mul_nonneg (mul_nonneg (by norm_num) hPm.le) (pow_nonneg P.c_pos.le 3))
      calc
        (2 / Real.pi * (B : ℝ) / haarPminus P / (4 * P.c ^ 3)) *
            ((n : ℝ) * ((60 * P.L ^ 4 + 3 * haarH0 P ^ 2) / (2 * (n : ℝ) ^ 2)))
          = ((2 / Real.pi) / (8 * haarPminus P * P.c ^ 3)) *
              (((B : ℝ) / (n : ℝ)) * (60 * P.L ^ 4 + 3 * haarH0 P ^ 2)) := by
                field_simp [hPm.ne', P.c_pos.ne', hn0.ne']
                ring
        _ ≤ ((2 / Real.pi) / (8 * haarPminus P * P.c ^ 3)) *
              (P.K * (60 * P.L ^ 4 + 3 * haarH0 P ^ 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hBdiv hQ) hcoef
        _ = _ := by ring

private lemma half_leading_lower {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D) :
    haarBminus P * (B : ℝ) ≤ frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2 := by
  have hb := haar_bounds P n m B μ D hstate
  have hPm : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hR : 0 < twoR μ D := hPm.trans_le hb.1
  have hm : 0 < muBar μ := P.c_pos.trans_le hb.2.2.2.1
  have hden : 0 < twoR μ D * muBar μ := mul_pos hR hm
  have hBnat : 1 ≤ B := hstate.1.2.2
  have hNlo := gb_lower_first B hBnat
  have hNsqlo : (4 / Real.pi ^ 2) * (B : ℝ) ≤ batchConst B ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ (2 / Real.pi) * Real.sqrt (B : ℝ)) hNlo 2
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg B)] at h
    convert h using 1 <;> ring
  have hDsq : frobNorm D ^ 2 = ∑ i, ∑ j, D i j ^ 2 := coord_sum_frob_sq D
  have hFlo : P.fMin ^ 2 ≤ ∑ i, ∑ j, D i j ^ 2 := by
    rw [← hDsq]
    exact pow_le_pow_left₀ P.fMin_pos.le hstate.2.2.2.2.2.2.1 2
  have hμ := hstate.2.2.2.2.2.1
  have hAlo : P.c ^ 2 * P.fMin ^ 2
      ≤ ∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2 := by
    simp only [Matrix.diagonal_mul]
    calc
      P.c ^ 2 * P.fMin ^ 2 ≤ P.c ^ 2 * ∑ i, ∑ j, D i j ^ 2 :=
        mul_le_mul_of_nonneg_left hFlo (sq_nonneg _)
      _ = ∑ i, ∑ j, P.c ^ 2 * D i j ^ 2 := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        convert mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ P.c_pos.le (hμ i).1 2) (sq_nonneg (D i j)) using 1 <;> ring
  have hdenhi : twoR μ D * muBar μ ≤ P.L ^ 2 * P.fMax ^ 2 := by
    have hPp : 0 < haarPplus P := mul_pos (P.c_pos.trans_le P.c_le_L)
      (pow_pos (P.fMin_pos.trans_le P.fMin_le_fMax) 2)
    calc
      _ ≤ haarPplus P * P.L := mul_le_mul hb.2.1 hb.2.2.2.2 hm.le hPp.le
      _ = _ := by unfold haarPplus; ring
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hsqrtden : Real.sqrt (twoR μ D * muBar μ) ^ 2 = twoR μ D * muBar μ :=
    Real.sq_sqrt hden.le
  rw [coord_sum_frob_sq]
  simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  unfold LB
  rw [div_pow, mul_pow, hsqrt, hsqrtden]
  unfold haarBminus
  have hfrac : ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
      / (P.L ^ 2 * P.fMax ^ 2)
      ≤ batchConst B ^ 2 * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
        / (twoR μ D * muBar μ) := by
    apply (div_le_div_iff₀
      (mul_pos (pow_pos (P.c_pos.trans_le P.c_le_L) 2)
        (pow_pos (P.fMin_pos.trans_le P.fMin_le_fMax) 2)) hden).2
    calc
      ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
            * (twoR μ D * muBar μ)
        ≤ ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
            * (P.L ^ 2 * P.fMax ^ 2) :=
          mul_le_mul_of_nonneg_left hdenhi (by positivity)
      _ ≤ (batchConst B ^ 2
            * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2))
            * (P.L ^ 2 * P.fMax ^ 2) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul hNsqlo hAlo (by positivity) (by positivity)) (by positivity)
  calc
    8 * P.c ^ 2 * P.fMin ^ 2 / (Real.pi ^ 3 * P.L ^ 2 * P.fMax ^ 2) * (B : ℝ)
      = (2 / Real.pi) * (((4 / Real.pi ^ 2) * (B : ℝ))
          * (P.c ^ 2 * P.fMin ^ 2) / (P.L ^ 2 * P.fMax ^ 2)) := by
            field_simp
            <;> ring
    _ ≤ (2 / Real.pi) * (batchConst B ^ 2
          * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
            / (twoR μ D * muBar μ)) := mul_le_mul_of_nonneg_left hfrac (by positivity)
    _ = _ := by ring

/-- Part (i) of `thm:app-sgd-half-drift`: an admissible `C_*` (depending on `P` only) with
`E_U‖U^T M(U) − L_B Λ D‖²_F ≤ C_*`, and the relative-error bound in squared form
`E_U‖U^T M(U) − L_B Λ D‖²_F ≤ (C_*/(b₋B)) ‖L_B Λ D‖²_F`. cr-2026-10-23. Source `section.tex` l. 899-911. LaTeX statement (verbatim):
```latex
\begin{theorem}[Half-anisotropic drift]\label{thm:app-sgd-half-drift}
In the Haar model of \cref{def:app-sgd-state-law} with $k\ge k_*$, there is
an admissible constant $C_*$ such that
\begin{equation}\label{eqn:app-sgd-half-drift}
\EE_U\big\|U^\T M(U)-L_B\,\Lambda D\big\|_\F^2\le C_* ,
\end{equation}
while the leading term satisfies
\begin{equation}\label{eqn:app-sgd-half-leading}
b_-B\le\norm{L_B\Lambda D}_\F^2\le b_+B,\qquad b_-\defeq\frac{8c^2f_-^2}{\pi^3L^2f_+^2},\quad b_+\defeq\frac{2L^2f_+^2}{\pi c^2f_-^2}.
\end{equation}
In particular the relative error of the mean update in $L^2(U)$ Frobenius
norm is at most $\sqrt{C_*/(b_-B)}$.
\end{theorem}
``` -/
theorem thm_app_sgd_half_drift_i (P : HaarParams) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
      (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)), IsOrthHaar ν →
      def_app_sgd_state_law P n m B μ D → haarKStar P ≤ kOf n m B →
      (∫⁻ U, ENNReal.ofReal (frobNorm (haarDriftErr B μ D U) ^ 2) ∂ν ≤ ENNReal.ofReal C) ∧
      (∫⁻ U, ENNReal.ofReal (frobNorm (haarDriftErr B μ D U) ^ 2) ∂ν
        ≤ ENNReal.ofReal (C / (haarBminus P * (B : ℝ))
            * frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2)) := by
  obtain ⟨CE, hCE, hcoord⟩ := prop_app_sgd_coordinate_sum P
  let CN := (2 / Real.pi) * P.K * (60 * P.L ^ 4 + 3 * haarH0 P ^ 2)
    / (8 * haarPminus P * P.c ^ 3)
  have hPm : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hCN : 0 ≤ CN := by
    dsimp [CN]
    exact div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by linarith [P.one_le_K]))
      (by positivity)) (mul_nonneg (mul_nonneg (by norm_num) hPm.le)
        (pow_nonneg P.c_pos.le 3))
  refine ⟨2 * CE + 2 * CN, by positivity, ?_⟩
  intro n m B μ D ν hν hstate hk
  let Q : Matrix.orthogonalGroup (Fin n) ℝ → Matrix (Fin n) (Fin m) ℝ := fun U =>
    (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) •
      (Matrix.diagonal (fun p => (Real.sqrt (haarSigmaOut U μ p p))⁻¹
          - (Real.sqrt (muBar μ))⁻¹)
        * (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D)
  have hb := haar_bounds P n m B μ D hstate
  have hR : 0 < twoR μ D := hPm.trans_le hb.1
  have hm : 0 < muBar μ := P.c_pos.trans_le hb.2.2.2.1
  have herrmeas : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    have hs : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∑ p, ∑ j, haarErr B μ D U p j ^ 2) :=
      Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun j _ =>
      (coord_sum_measurable_err μ D p j).pow_const 2
    simpa only [coord_sum_frob_sq] using hs
  have hQmeas : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ENNReal.ofReal (frobNorm (Q U) ^ 2)) := by
    apply ENNReal.measurable_ofReal.comp
    have hU : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (U : Matrix (Fin n) (Fin n) ℝ)) := continuous_subtype_val
    have hS : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ => haarSigmaOut U μ) := by
      unfold haarSigmaOut
      fun_prop
    have hX : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) := by fun_prop
    have hsqrtm : Measurable (fun _U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (Real.sqrt (muBar μ))⁻¹) := measurable_const
    have hs : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        (Real.sqrt (2 / Real.pi) * batchConst B / Real.sqrt (twoR μ D)) ^ 2
          * ∑ p, ((Real.sqrt (haarSigmaOut U μ p p))⁻¹
              - (Real.sqrt (muBar μ))⁻¹) ^ 2
            * ∑ j, (((U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D) p j) ^ 2) := by
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro p _
      apply Measurable.mul
      · exact (((Real.continuous_sqrt.measurable.comp
          (hS.matrix_elem p p).measurable).inv.sub hsqrtm).pow_const 2)
      · exact Finset.measurable_sum _ fun j _ => (hX.matrix_elem p j).measurable.pow_const 2
    dsimp [Q]
    simpa only [half_correction_sq] using hs
  have hpoint (U : Matrix.orthogonalGroup (Fin n) ℝ) :
      frobNorm (haarDriftErr B μ D U) ^ 2
        ≤ 2 * frobNorm (haarErr B μ D U) ^ 2 + 2 * frobNorm (Q U) ^ 2 := by
    rw [half_drift_decomp μ D U hR.le hm, half_frob_sq_orth_left]
    exact half_frob_sq_add _ _
  have hcorr : ∫⁻ U, ENNReal.ofReal (frobNorm (Q U) ^ 2) ∂ν ≤ ENNReal.ofReal CN := by
    exact half_correction_integral P μ D hstate ν hν
  have hmain : ∫⁻ U, ENNReal.ofReal (frobNorm (haarDriftErr B μ D U) ^ 2) ∂ν
      ≤ ENNReal.ofReal (2 * CE + 2 * CN) := by
    calc
      _ ≤ ∫⁻ U, (ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2)
          + ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (Q U) ^ 2)) ∂ν := by
        apply lintegral_mono
        intro U
        change ENNReal.ofReal (frobNorm (haarDriftErr B μ D U) ^ 2) ≤
          ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2) +
            ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (Q U) ^ 2)
        calc
          _ ≤ ENNReal.ofReal (2 * frobNorm (haarErr B μ D U) ^ 2
              + 2 * frobNorm (Q U) ^ 2) := ENNReal.ofReal_le_ofReal (hpoint U)
          _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      _ = ENNReal.ofReal 2 * (∫⁻ U, ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2) ∂ν)
          + ENNReal.ofReal 2 * (∫⁻ U, ENNReal.ofReal (frobNorm (Q U) ^ 2) ∂ν) := by
        have hfmeas : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
            ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (haarErr B μ D U) ^ 2)) :=
          measurable_const.mul herrmeas
        calc
          _ = (∫⁻ U, ENNReal.ofReal 2 * ENNReal.ofReal
                (frobNorm (haarErr B μ D U) ^ 2) ∂ν)
              + (∫⁻ U, ENNReal.ofReal 2 * ENNReal.ofReal (frobNorm (Q U) ^ 2) ∂ν) :=
            lintegral_add_left hfmeas _
          _ = _ := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal CE + ENNReal.ofReal 2 * ENNReal.ofReal CN :=
        add_le_add (mul_le_mul_of_nonneg_left (hcoord n m B μ D ν hν hstate hk) zero_le)
          (mul_le_mul_of_nonneg_left hcorr zero_le)
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ⟨hmain, hmain.trans ?_⟩
  apply ENNReal.ofReal_le_ofReal
  have hlead := half_leading_lower P μ D hstate
  have hbminus : 0 < haarBminus P := by
    unfold haarBminus
    exact div_pos
      (mul_pos (mul_pos (by norm_num) (pow_pos P.c_pos 2)) (pow_pos P.fMin_pos 2))
      (mul_pos (mul_pos (pow_pos Real.pi_pos 3)
        (pow_pos (P.c_pos.trans_le P.c_le_L) 2))
        (pow_pos (P.fMin_pos.trans_le P.fMin_le_fMax) 2))
  have hB : (0 : ℝ) < B := by exact_mod_cast hstate.1.2.2
  have hden : 0 < haarBminus P * (B : ℝ) := mul_pos hbminus hB
  calc
    2 * CE + 2 * CN = (2 * CE + 2 * CN) / (haarBminus P * (B : ℝ))
        * (haarBminus P * (B : ℝ)) := by field_simp
    _ ≤ (2 * CE + 2 * CN) / (haarBminus P * (B : ℝ))
        * frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2 :=
      mul_le_mul_of_nonneg_left hlead (div_nonneg (by positivity) hden.le)

/-- Part (ii) of `thm:app-sgd-half-drift`: the leading term satisfies
`b₋ B ≤ ‖L_B Λ D‖²_F ≤ b₊ B` (`eqn:app-sgd-half-leading`). cr-2026-10-23. Source `section.tex` l. 899-911. LaTeX statement (verbatim):
```latex
\begin{theorem}[Half-anisotropic drift]\label{thm:app-sgd-half-drift}
In the Haar model of \cref{def:app-sgd-state-law} with $k\ge k_*$, there is
an admissible constant $C_*$ such that
\begin{equation}\label{eqn:app-sgd-half-drift}
\EE_U\big\|U^\T M(U)-L_B\,\Lambda D\big\|_\F^2\le C_* ,
\end{equation}
while the leading term satisfies
\begin{equation}\label{eqn:app-sgd-half-leading}
b_-B\le\norm{L_B\Lambda D}_\F^2\le b_+B,\qquad b_-\defeq\frac{8c^2f_-^2}{\pi^3L^2f_+^2},\quad b_+\defeq\frac{2L^2f_+^2}{\pi c^2f_-^2}.
\end{equation}
In particular the relative error of the mean update in $L^2(U)$ Frobenius
norm is at most $\sqrt{C_*/(b_-B)}$.
\end{theorem}
``` -/
theorem thm_app_sgd_half_drift_ii (P : HaarParams) (n m B : ℕ) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D)
    (hk : haarKStar P ≤ kOf n m B) :
    haarBminus P * (B : ℝ) ≤ frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2 ∧
    frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2 ≤ haarBplus P * (B : ℝ) := by
  have hb := haar_bounds P n m B μ D hstate
  have hRlo := hb.1
  have hRhi := hb.2.1
  have hmlo := hb.2.2.2.1
  have hmhi := hb.2.2.2.2
  have hPlo : 0 < haarPminus P := mul_pos P.c_pos (pow_pos P.fMin_pos 2)
  have hL : 0 < P.L := P.c_pos.trans_le P.c_le_L
  have hfMax : 0 < P.fMax := P.fMin_pos.trans_le P.fMin_le_fMax
  have hPhi : 0 < haarPplus P := mul_pos (lt_of_lt_of_le P.c_pos P.c_le_L)
    (pow_pos (P.fMin_pos.trans_le P.fMin_le_fMax) 2)
  have hR : 0 < twoR μ D := hPlo.trans_le hRlo
  have hm : 0 < muBar μ := P.c_pos.trans_le hmlo
  have hden : 0 < twoR μ D * muBar μ := mul_pos hR hm
  have hBpos : 0 < B := hstate.1.2.2
  have hBnat : 1 ≤ B := hBpos
  have hBc : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hNlo := gb_lower_first B hBnat
  have hNhi := gb_upper B hBnat
  have hsB : Real.sqrt (B : ℝ) ^ 2 = (B : ℝ) := Real.sq_sqrt hBc
  have hN0 : 0 ≤ batchConst B := le_trans (by positivity) hNlo
  have hNsqlo : (4 / Real.pi ^ 2) * (B : ℝ) ≤ batchConst B ^ 2 := by
    have := pow_le_pow_left₀ (by positivity : 0 ≤ (2 / Real.pi) * Real.sqrt (B : ℝ)) hNlo 2
    rw [mul_pow, hsB] at this
    convert this using 1 <;> ring
  have hNsqhi : batchConst B ^ 2 ≤ (B : ℝ) := by
    have := pow_le_pow_left₀ hN0 hNhi 2
    simpa only [hsB] using this
  have hDsq : frobNorm D ^ 2 = ∑ i, ∑ j, D i j ^ 2 := coord_sum_frob_sq D
  have hF := hstate.2.2.2.2.2.2.1
  have hF' := hstate.2.2.2.2.2.2.2.1
  have hsum0 : 0 ≤ ∑ i, ∑ j, D i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hFlo : P.fMin ^ 2 ≤ ∑ i, ∑ j, D i j ^ 2 := by
    rw [← hDsq]
    exact pow_le_pow_left₀ P.fMin_pos.le hF 2
  have hFhi : ∑ i, ∑ j, D i j ^ 2 ≤ P.fMax ^ 2 := by
    rw [← hDsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hF' 2
  have hμ := hstate.2.2.2.2.2.1
  have hAlo : P.c ^ 2 * P.fMin ^ 2
      ≤ ∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2 := by
    simp only [Matrix.diagonal_mul]
    calc
      P.c ^ 2 * P.fMin ^ 2 ≤ P.c ^ 2 * ∑ i, ∑ j, D i j ^ 2 :=
        mul_le_mul_of_nonneg_left hFlo (sq_nonneg _)
      _ = ∑ i, ∑ j, P.c ^ 2 * D i j ^ 2 := by rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        convert mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ P.c_pos.le (hμ i).1 2) (sq_nonneg (D i j)) using 1 <;> ring
  have hAhi : ∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2
      ≤ P.L ^ 2 * P.fMax ^ 2 := by
    simp only [Matrix.diagonal_mul]
    calc
      _ ≤ ∑ i, ∑ j, P.L ^ 2 * D i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        convert mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (le_trans P.c_pos.le (hμ i).1) (hμ i).2 2)
            (sq_nonneg (D i j)) using 1 <;> ring
      _ = P.L ^ 2 * ∑ i, ∑ j, D i j ^ 2 := by rw [Finset.mul_sum]; simp_rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hFhi (sq_nonneg _)
  have hdenlo : P.c ^ 2 * P.fMin ^ 2 ≤ twoR μ D * muBar μ := by
    calc
      _ = haarPminus P * P.c := by unfold haarPminus; ring
      _ ≤ twoR μ D * muBar μ := mul_le_mul hRlo hmlo P.c_pos.le hR.le
  have hdenhi : twoR μ D * muBar μ ≤ P.L ^ 2 * P.fMax ^ 2 := by
    calc
      _ ≤ haarPplus P * P.L := mul_le_mul hRhi hmhi hm.le hPhi.le
      _ = _ := by unfold haarPplus; ring
  have hsqrt : Real.sqrt (2 / Real.pi) ^ 2 = 2 / Real.pi :=
    Real.sq_sqrt (by positivity)
  have hsqrtden : Real.sqrt (twoR μ D * muBar μ) ^ 2 = twoR μ D * muBar μ :=
    Real.sq_sqrt hden.le
  have hnorm : frobNorm (LB B μ D • (Matrix.diagonal μ * D)) ^ 2
      = (2 / Real.pi) * batchConst B ^ 2
        * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2) / (twoR μ D * muBar μ) := by
    rw [coord_sum_frob_sq]
    simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    unfold LB
    rw [div_pow, mul_pow, hsqrt, hsqrtden]
    ring
  rw [hnorm]
  constructor
  · unfold haarBminus
    have hfrac : ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
        / (P.L ^ 2 * P.fMax ^ 2)
        ≤ batchConst B ^ 2 * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
          / (twoR μ D * muBar μ) := by
      apply (div_le_div_iff₀ (mul_pos (pow_pos hL 2) (pow_pos hfMax 2)) hden).2
      calc
        ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
              * (twoR μ D * muBar μ)
          ≤ ((4 / Real.pi ^ 2) * (B : ℝ)) * (P.c ^ 2 * P.fMin ^ 2)
              * (P.L ^ 2 * P.fMax ^ 2) :=
            mul_le_mul_of_nonneg_left hdenhi (by positivity)
        _ ≤ (batchConst B ^ 2
              * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2))
              * (P.L ^ 2 * P.fMax ^ 2) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul hNsqlo hAlo (by positivity) (by positivity)) (by positivity)
    calc
      8 * P.c ^ 2 * P.fMin ^ 2 / (Real.pi ^ 3 * P.L ^ 2 * P.fMax ^ 2)
            * (B : ℝ)
        = (2 / Real.pi) * (((4 / Real.pi ^ 2) * (B : ℝ))
            * (P.c ^ 2 * P.fMin ^ 2) / (P.L ^ 2 * P.fMax ^ 2)) := by
              field_simp
              <;> ring
      _ ≤ (2 / Real.pi) * (batchConst B ^ 2
            * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
              / (twoR μ D * muBar μ)) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = _ := by ring
  · have hnumhi : batchConst B ^ 2
        * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
          ≤ (B : ℝ) * (P.L ^ 2 * P.fMax ^ 2) :=
      mul_le_mul hNsqhi hAhi (by positivity) hBc
    have hfrac : batchConst B ^ 2
        * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
          / (twoR μ D * muBar μ)
        ≤ ((B : ℝ) * (P.L ^ 2 * P.fMax ^ 2)) / (P.c ^ 2 * P.fMin ^ 2) := by
      apply (div_le_div_iff₀ hden
        (mul_pos (pow_pos P.c_pos 2) (pow_pos P.fMin_pos 2))).2
      calc
        batchConst B ^ 2 * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
              * (P.c ^ 2 * P.fMin ^ 2)
          ≤ ((B : ℝ) * (P.L ^ 2 * P.fMax ^ 2))
              * (P.c ^ 2 * P.fMin ^ 2) :=
            mul_le_mul_of_nonneg_right hnumhi (by positivity)
        _ ≤ ((B : ℝ) * (P.L ^ 2 * P.fMax ^ 2))
              * (twoR μ D * muBar μ) :=
            mul_le_mul_of_nonneg_left hdenlo (by positivity)
    unfold haarBplus
    calc
      (2 / Real.pi) * batchConst B ^ 2
          * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
            / (twoR μ D * muBar μ)
        = (2 / Real.pi) * (batchConst B ^ 2
            * (∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2)
              / (twoR μ D * muBar μ)) := by ring
      _ ≤ (2 / Real.pi) * (((B : ℝ) * (P.L ^ 2 * P.fMax ^ 2))
            / (P.c ^ 2 * P.fMin ^ 2)) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = 2 * P.L ^ 2 * P.fMax ^ 2 / (Real.pi * P.c ^ 2 * P.fMin ^ 2)
            * (B : ℝ) := by
              field_simp
              <;> ring

private lemma half_orth_entry_abs_le_one {n : ℕ}
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (p i : Fin n) :
    |(U : Matrix (Fin n) (Fin n) ℝ) p i| ≤ 1 := by
  have hUU : (U : Matrix (Fin n) (Fin n) ℝ) * (U : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 U.2
  have h := congrFun (congrFun hUU p) p
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] at h
  have hsingle : (U : Matrix (Fin n) (Fin n) ℝ) p i ^ 2
      ≤ ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have hs : (U : Matrix (Fin n) (Fin n) ℝ) p i ^ 2 ≤ 1 := by
    calc
      _ ≤ ∑ k, (U : Matrix (Fin n) (Fin n) ℝ) p k ^ 2 := hsingle
      _ = 1 := by simpa [sq] using h
  nlinarith [sq_abs ((U : Matrix (Fin n) (Fin n) ℝ) p i)]

private lemma half_sign_abs_le_one (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · simp [Real.sign_of_neg hx]
  · simp [hx]
  · simp [Real.sign_of_pos hx]

private lemma half_weighted_sign_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (p i : Fin n) (j : Fin m) :
    Integrable (fun x => (x.1 : Matrix (Fin n) (Fin n) ℝ) p i
      * haarSign μ D x.1 x.2 p j) (ν.prod (batchLaw n m B)) := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hgrad : Continuous (fun x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      physGrad (haarDelta x.1 D) (haarBatch μ x.1 x.2) p j) := by
    unfold physGrad residual haarBatch linBatch haarDelta Matrix.mulVec dotProduct
    fun_prop
  have hmeas : Measurable (fun x : Matrix.orthogonalGroup (Fin n) ℝ ×
      (Fin B → (Fin n → ℝ) × (Fin m → ℝ)) =>
      (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j) :=
    ((continuous_subtype_val.matrix_elem p i).comp continuous_fst).measurable.mul
      (aux_sign_measurable.comp hgrad.measurable)
  refine Integrable.of_bound hmeas.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have hsign : |haarSign μ D x.1 x.2 p j| ≤ 1 := by
    simpa only [haarSign, Matrix.map_apply] using
      half_sign_abs_le_one (physGrad (haarDelta x.1 D) (haarBatch μ x.1 x.2) p j)
  nlinarith [mul_nonneg
    (sub_nonneg.mpr (half_orth_entry_abs_le_one x.1 p i))
    (abs_nonneg (haarSign μ D x.1 x.2 p j))]

private lemma half_weighted_sign_integral {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (p i : Fin n) (j : Fin m) :
    ∫ x, (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        ∂(ν.prod (batchLaw n m B))
      = ∫ U, (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j ∂ν := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have hint := half_weighted_sign_integrable (B := B) μ D ν p i j
  rw [integral_prod _ hint]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun (U : Matrix.orthogonalGroup (Fin n) ℝ) => by
    change (∫ y, (U : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D U y p j
      ∂batchLaw n m B) = (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j
    rw [integral_const_mul]
    rfl

private lemma half_weighted_mean_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (p i : Fin n) (j : Fin m) :
    Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j) ν := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  have h := (half_weighted_sign_integrable (B := B) μ D ν p i j).integral_prod_left
  refine h.congr (Filter.Eventually.of_forall fun (U : Matrix.orthogonalGroup (Fin n) ℝ) => ?_)
  change (∫ y, (U : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D U y p j
      ∂batchLaw n m B) = (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j
  rw [integral_const_mul]
  rfl

private lemma half_row_pair_eq {n m : ℕ} (D : Matrix (Fin n) (Fin m) ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    dotProduct (Matrix.mulVec (haarDelta U D)ᵀ (haarCol U i))
        (Matrix.mulVec Aᵀ (haarCol U i))
      = ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A) i j) := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hDA : (haarDelta U D)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = Dᵀ := by
    unfold haarDelta
    rw [Matrix.transpose_mul, Matrix.mul_assoc, hUt, Matrix.mul_one]
  have hvD : Matrix.mulVec (haarDelta U D)ᵀ (haarCol U i) = fun j => D i j := by
    funext j
    have h := congrFun (congrFun hDA j) i
    rw [Matrix.mul_apply] at h
    simpa [Matrix.mulVec, dotProduct, haarCol, Matrix.transpose_apply] using h
  have hvA : Matrix.mulVec Aᵀ (haarCol U i) = fun j =>
      ((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A) i j := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, haarCol, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [hvD, hvA]
  rfl

private lemma half_risk_pair_eq {n m : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (A : Matrix (Fin n) (Fin m) ℝ) :
    pairIdIn (haarSigmaOut U μ) (haarDelta U D) A
      = ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * A) i j) := by
  have hUt : (U : Matrix (Fin n) (Fin n) ℝ)ᵀ * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hSD : haarSigmaOut U μ * haarDelta U D
      = (U : Matrix (Fin n) (Fin n) ℝ) * Matrix.diagonal μ * D := by
    unfold haarSigmaOut haarDelta
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U : Matrix (Fin n) (Fin n) ℝ)ᵀ
      (U : Matrix (Fin n) (Fin n) ℝ), hUt, Matrix.one_mul]
  unfold pairIdIn
  rw [hSD]
  have htrace : ((U : Matrix (Fin n) (Fin n) ℝ) * (Matrix.diagonal μ * D * Aᵀ)).trace
      = ((Matrix.diagonal μ * D * Aᵀ) * (U : Matrix (Fin n) (Fin n) ℝ)).trace :=
    Matrix.trace_mul_comm _ _
  have hDA : (Matrix.diagonal μ * D) * Aᵀ =
      fun i p => ∑ j, μ i * D i j * A p j := by
    ext i p
    rw [Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.transpose_apply, Matrix.diagonal_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal μ) D Aᵀ, htrace]
  rw [hDA]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  change (∑ p, (∑ j, μ i * D i j * A p j) *
      (U : Matrix (Fin n) (Fin n) ℝ) p i) =
    ∑ j, μ i * D i j * ∑ p, (U : Matrix (Fin n) (Fin n) ℝ) p i * A p j
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

private lemma half_row_pair_integral {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ x, dotProduct
        (Matrix.mulVec (haarDelta x.1 D)ᵀ (haarCol x.1 i))
        (Matrix.mulVec (haarSign μ D x.1 x.2)ᵀ (haarCol x.1 i))
      ∂(ν.prod (batchLaw n m B)))
      = ∫ U, ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ
          * haarMean B μ D U) i j) ∂ν := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  calc
    _ = ∫ x, ∑ j, D i j * ∑ p,
          (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        ∂(ν.prod (batchLaw n m B)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change dotProduct
          (Matrix.mulVec (haarDelta x.1 D)ᵀ (haarCol x.1 i))
          (Matrix.mulVec (haarSign μ D x.1 x.2)ᵀ (haarCol x.1 i))
          = ∑ j, D i j * ∑ p,
            (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        rw [half_row_pair_eq]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ j, ∑ p, D i j * (∫ x,
          (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        ∂(ν.prod (batchLaw n m B))) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun p _ =>
        (half_weighted_sign_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun p _ =>
        (half_weighted_sign_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_const_mul]
    _ = ∑ j, ∑ p, D i j * (∫ U,
          (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j ∂ν) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      rw [half_weighted_sign_integral]
    _ = ∫ U, ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ
          * haarMean B μ D U) i j) ∂ν := by
      simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun p _ =>
        (half_weighted_mean_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun p _ =>
        (half_weighted_mean_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_const_mul]

private lemma half_risk_pair_integral {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] :
    (∫ x, pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D) (haarSign μ D x.1 x.2)
      ∂(ν.prod (batchLaw n m B)))
      = ∫ U, ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ
          * haarMean B μ D U) i j) ∂ν := by
  haveI : IsProbabilityMeasure (gaussBatch n m) := by unfold gaussBatch; infer_instance
  haveI : IsProbabilityMeasure (batchLaw n m B) := by unfold batchLaw; infer_instance
  calc
    _ = ∫ x, ∑ i, ∑ j, μ i * D i j * ∑ p,
          (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        ∂(ν.prod (batchLaw n m B)) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D)
          (haarSign μ D x.1 x.2) = ∑ i, ∑ j, μ i * D i j * ∑ p,
            (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        rw [half_risk_pair_eq]
        simp only [Matrix.mul_apply, Matrix.transpose_apply]
    _ = ∑ i, ∑ j, ∑ p, μ i * D i j * (∫ x,
          (x.1 : Matrix (Fin n) (Fin n) ℝ) p i * haarSign μ D x.1 x.2 p j
        ∂(ν.prod (batchLaw n m B))) := by
      simp_rw [Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun p _ =>
          (half_weighted_sign_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun p _ =>
        (half_weighted_sign_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun p _ =>
        (half_weighted_sign_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_const_mul]
    _ = ∑ i, ∑ j, ∑ p, μ i * D i j * (∫ U,
          (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j ∂ν) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro p _
      rw [half_weighted_sign_integral]
    _ = ∫ U, ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ
          * haarMean B μ D U) i j) ∂ν := by
      simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun p _ =>
          (half_weighted_mean_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun p _ =>
        (half_weighted_mean_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum _ (fun p _ =>
        (half_weighted_mean_integrable μ D ν p i j).const_mul _)]
      apply Finset.sum_congr rfl
      intro p _
      rw [integral_const_mul]

private lemma half_drift_entry_integrable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (i : Fin n) (j : Fin m) :
    Integrable (fun U => haarDriftErr B μ D U i j) ν := by
  have hsum : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ p, (U : Matrix (Fin n) (Fin n) ℝ) p i * haarMean B μ D U p j) ν :=
    integrable_finsetSum _ fun p _ => half_weighted_mean_integrable μ D ν p i j
  have hconst : Integrable (fun _U : Matrix.orthogonalGroup (Fin n) ℝ =>
      LB B μ D * (Matrix.diagonal μ * D) i j) ν := integrable_const _
  convert hsum.sub hconst using 1
  ext U
  unfold haarDriftErr
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    smul_eq_mul, Pi.sub_apply]

private lemma half_drift_frob_aestronglyMeasurable {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] :
    AEStronglyMeasurable (fun U => frobNorm (haarDriftErr B μ D U)) ν := by
  have hsq : AEMeasurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ i, ∑ j, haarDriftErr B μ D U i j ^ 2) ν := by
    have hinner (i : Fin n) : AEMeasurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∑ j, haarDriftErr B μ D U i j ^ 2) ν := by
      have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin m)) fun j _ =>
        (half_drift_entry_integrable (B := B) μ D ν i j).aestronglyMeasurable.aemeasurable.pow_const 2
      exact h.congr (Filter.Eventually.of_forall fun U => by
        simp only [Finset.sum_apply])
    have h := Finset.aemeasurable_sum (Finset.univ : Finset (Fin n)) fun i _ => hinner i
    exact h.congr (Filter.Eventually.of_forall fun U => by
      simp only [Finset.sum_apply])
  exact (by
    unfold frobNorm
    exact hsq.sqrt.aestronglyMeasurable)

private lemma half_integral_le_sqrt { α : Type*} [MeasurableSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (f : α → ℝ)
    (hf : AEStronglyMeasurable f ν) (hf0 : ∀ x, 0 ≤ f x) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν ≤ ENNReal.ofReal C) :
    ∫ x, f x ∂ν ≤ Real.sqrt C := by
  have hfin : (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbound
  have hf2 : Integrable (fun x => f x ^ 2) ν :=
    (lintegral_ofReal_ne_top_iff_integrable (hf.pow 2)
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x))).mp hfin
  have hfmem : MemLp f 2 ν := (memLp_two_iff_integrable_sq hf).2 hf2
  have hone : MemLp (fun _x : α => (1 : ℝ)) 2 ν := memLp_const 1
  have htwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hfmem' : MemLp f (ENNReal.ofReal 2) ν := by simpa only [htwo] using hfmem
  have hone' : MemLp (fun _x : α => (1 : ℝ)) (ENNReal.ofReal 2) ν := by
    simpa only [htwo] using hone
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall fun _ => zero_le_one) hfmem' hone'
  have hsquare : ∫ x, f x ^ 2 ∂ν ≤ C := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    rw [← ofReal_integral_eq_lintegral_ofReal hf2
      (Filter.Eventually.of_forall fun x => sq_nonneg (f x)),
      ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg (f x)),
      ENNReal.toReal_ofReal hC] at ht
    exact ht
  simp only [mul_one, Real.rpow_two, one_div, integral_const, probReal_univ, one_smul,
    Real.one_rpow, mul_one] at hholder
  norm_num at hholder
  rw [← Real.sqrt_eq_rpow] at hholder
  exact hholder.trans (Real.sqrt_le_sqrt hsquare)

private lemma half_frob_inner_abs_le {n m : ℕ}
    (A T : Matrix (Fin n) (Fin m) ℝ) :
    |∑ i, ∑ j, A i j * T i j| ≤ frobNorm A * frobNorm T := by
  unfold frobNorm
  rw [abs_le]
  constructor
  · have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin m))
      (fun x => -A x.1 x.2) (fun x => T x.1 x.2)
    have h' : -(∑ i, ∑ j, A i j * T i j) ≤
        Real.sqrt (∑ i, ∑ j, A i j ^ 2) * Real.sqrt (∑ i, ∑ j, T i j ^ 2) := by
      simpa only [Fintype.sum_prod_type, neg_mul, neg_sq, Finset.sum_neg_distrib] using h
    linarith
  · have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin n × Fin m))
      (fun x => A x.1 x.2) (fun x => T x.1 x.2)
    simpa only [Fintype.sum_prod_type] using h

private lemma half_row_sum_abs_le {n m : ℕ}
    (D T : Matrix (Fin n) (Fin m) ℝ) :
    ∑ i, |∑ j, D i j * T i j| ≤ frobNorm D * frobNorm T := by
  let r : Fin n → ℝ := fun i => ∑ j, D i j * T i j
  let S : Matrix (Fin n) (Fin m) ℝ := fun i j => (SignType.sign (r i) : ℝ) * D i j
  have hleft : ∑ i, |r i| = ∑ i, ∑ j, S i j * T i j := by
    apply Finset.sum_congr rfl
    intro i _
    rw [← sign_mul_self (r i)]
    dsimp [r, S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hS : frobNorm S ≤ frobNorm D := by
    unfold frobNorm
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    have hs : ((SignType.sign (r i) : ℝ)) ^ 2 ≤ 1 := by
      rcases lt_trichotomy (r i) 0 with hi | hi | hi <;> simp [sign_apply, hi]
    dsimp [S]
    rw [mul_pow]
    nlinarith [sq_nonneg (D i j)]
  change ∑ i, |r i| ≤ frobNorm D * frobNorm T
  rw [hleft]
  exact (le_abs_self _).trans ((half_frob_inner_abs_le S T).trans
    (mul_le_mul_of_nonneg_right hS (Real.sqrt_nonneg _)))

private lemma half_weighted_frob_le {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D) :
    frobNorm (Matrix.diagonal μ * D) ≤ P.L * P.fMax := by
  have hmu := hstate.2.2.2.2.2.1
  have hF := hstate.2.2.2.2.2.2.2.1
  have hsq : ∑ i, ∑ j, (Matrix.diagonal μ * D) i j ^ 2 ≤ P.L ^ 2 * P.fMax ^ 2 := by
    simp only [Matrix.diagonal_mul]
    calc
      _ ≤ ∑ i, ∑ j, P.L ^ 2 * D i j ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        convert mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (le_trans P.c_pos.le (hmu i).1) (hmu i).2 2)
            (sq_nonneg (D i j)) using 1 <;> ring
      _ = P.L ^ 2 * ∑ i, ∑ j, D i j ^ 2 := by
        rw [Finset.mul_sum]
        simp_rw [Finset.mul_sum]
      _ = P.L ^ 2 * frobNorm D ^ 2 := by rw [coord_sum_frob_sq]
      _ ≤ P.L ^ 2 * P.fMax ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) hF 2) (sq_nonneg _)
  unfold frobNorm
  calc
    _ ≤ Real.sqrt (P.L ^ 2 * P.fMax ^ 2) := Real.sqrt_le_sqrt hsq
    _ = P.L * P.fMax := by
      rw [← mul_pow, Real.sqrt_sq_eq_abs, abs_of_pos
        (mul_pos (P.c_pos.trans_le P.c_le_L) (P.fMin_pos.trans_le P.fMin_le_fMax))]

private lemma half_total_leading_lower {n m B : ℕ} (P : HaarParams) (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (hstate : def_app_sgd_state_law P n m B μ D) :
    haarDminus P * Real.sqrt (B : ℝ) ≤
      LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2 := by
  have hb := haar_bounds P n m B μ D hstate
  have hR : 0 < twoR μ D := (mul_pos P.c_pos (pow_pos P.fMin_pos 2)).trans_le hb.1
  have hm : 0 < muBar μ := P.c_pos.trans_le hb.2.2.2.1
  have hden : 0 < twoR μ D * muBar μ := mul_pos hR hm
  have hPhi : 0 ≤ haarPplus P := by
    unfold haarPplus
    exact mul_nonneg (P.c_pos.trans_le P.c_le_L).le (sq_nonneg _)
  have hLf : 0 < P.L * P.fMax :=
    mul_pos (P.c_pos.trans_le P.c_le_L) (P.fMin_pos.trans_le P.fMin_le_fMax)
  have hdenle : Real.sqrt (twoR μ D * muBar μ) ≤ P.L * P.fMax := by
    apply (Real.sqrt_le_iff).2
    refine ⟨hLf.le, ?_⟩
    calc
      _ ≤ haarPplus P * P.L := mul_le_mul hb.2.1 hb.2.2.2.2
        (P.c_pos.trans_le hb.2.2.2.1).le hPhi
      _ = (P.L * P.fMax) ^ 2 := by unfold haarPplus; ring
  have hBnat : 1 ≤ B := hstate.1.2.2
  have hN := gb_lower_first B hBnat
  have hbase : 0 ≤ (2 / Real.pi) * Real.sqrt (B : ℝ) := by positivity
  have hN0 : 0 ≤ batchConst B := hbase.trans hN
  have hF := hstate.2.2.2.2.2.2.1
  have hmu := hstate.2.2.2.2.2.1
  have hA : P.c ^ 2 * P.fMin ^ 2 ≤
      frobNorm (Matrix.diagonal μ * D) ^ 2 := by
    rw [coord_sum_frob_sq]
    simp only [Matrix.diagonal_mul]
    calc
      _ ≤ P.c ^ 2 * frobNorm D ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ P.fMin_pos.le hF 2) (sq_nonneg _)
      _ = ∑ i, ∑ j, P.c ^ 2 * D i j ^ 2 := by
        rw [coord_sum_frob_sq, Finset.mul_sum]
        simp_rw [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        convert mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ P.c_pos.le (hmu i).1 2) (sq_nonneg (D i j)) using 1 <;> ring
  have hnum : Real.sqrt (2 / Real.pi) * ((2 / Real.pi) * Real.sqrt (B : ℝ)) *
      (P.c ^ 2 * P.fMin ^ 2) ≤ Real.sqrt (2 / Real.pi) * batchConst B *
        frobNorm (Matrix.diagonal μ * D) ^ 2 := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left hN (Real.sqrt_nonneg _)) hA
      (by positivity) (mul_nonneg (Real.sqrt_nonneg _) hN0)
  unfold haarDminus LB
  calc
    2 * Real.sqrt (2 / Real.pi) * P.c ^ 2 * P.fMin ^ 2 /
          (Real.pi * P.L * P.fMax) * Real.sqrt (B : ℝ)
      = (Real.sqrt (2 / Real.pi) * ((2 / Real.pi) * Real.sqrt (B : ℝ)) *
          (P.c ^ 2 * P.fMin ^ 2)) / (P.L * P.fMax) := by ring
    _ ≤ (Real.sqrt (2 / Real.pi) * batchConst B *
          frobNorm (Matrix.diagonal μ * D) ^ 2) /
          Real.sqrt (twoR μ D * muBar μ) :=
      div_le_div₀ (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hN0) (sq_nonneg _))
        hnum (Real.sqrt_pos.mpr hden) hdenle
    _ = Real.sqrt (2 / Real.pi) * batchConst B /
          Real.sqrt (twoR μ D * muBar μ) *
          frobNorm (Matrix.diagonal μ * D) ^ 2 := by ring

private lemma half_row_difference_eq_integral {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ x, dotProduct (Matrix.mulVec (haarDelta x.1 D)ᵀ (haarCol x.1 i))
        (Matrix.mulVec (haarSign μ D x.1 x.2)ᵀ (haarCol x.1 i))
      ∂(ν.prod (batchLaw n m B))) - LB B μ D * μ i * (∑ j, D i j ^ 2)
      = ∫ U, ∑ j, D i j * haarDriftErr B μ D U i j ∂ν := by
  rw [half_row_pair_integral]
  have hleft : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarMean B μ D U) i j)) ν := by
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun p _ =>
      (half_weighted_mean_integrable μ D ν p i j).const_mul _
  have herr : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ j, D i j * haarDriftErr B μ D U i j) ν :=
    integrable_finsetSum _ fun j _ => (half_drift_entry_integrable μ D ν i j).const_mul _
  calc
    (∫ U, ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          haarMean B μ D U) i j) ∂ν) - LB B μ D * μ i * (∑ j, D i j ^ 2)
      = (∫ U, ∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          haarMean B μ D U) i j) ∂ν) -
          ∫ _U, LB B μ D * μ i * (∑ j, D i j ^ 2) ∂ν := by
            rw [integral_const, probReal_univ, one_smul]
    _ = ∫ U, (∑ j, D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
          haarMean B μ D U) i j)) - LB B μ D * μ i * (∑ j, D i j ^ 2) ∂ν :=
      (integral_sub hleft (integrable_const _)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => by
        have he (j : Fin m) : haarDriftErr B μ D U i j =
            (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarMean B μ D U) i j) -
              LB B μ D * μ i * D i j := by
          unfold haarDriftErr
          rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_mul]
          change _ - LB B μ D * (μ i * D i j) = _
          ring
        simp_rw [he, mul_sub, Finset.sum_sub_distrib]
        rw [Finset.mul_sum]
        ring

private lemma half_risk_difference_eq_integral {n m B : ℕ} (μ : Fin n → ℝ)
    (D : Matrix (Fin n) (Fin m) ℝ) (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ))
    [IsProbabilityMeasure ν] :
    (∫ x, pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D) (haarSign μ D x.1 x.2)
      ∂(ν.prod (batchLaw n m B))) - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2
      = ∫ U, ∑ i, ∑ j, μ i * D i j * haarDriftErr B μ D U i j ∂ν := by
  rw [half_risk_pair_integral]
  have hleft : Integrable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ
        * haarMean B μ D U) i j)) ν := by
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun p _ => (half_weighted_mean_integrable μ D ν p i j).const_mul _
  calc
    (∫ U, ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        haarMean B μ D U) i j) ∂ν) - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2
      = (∫ U, ∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        haarMean B μ D U) i j) ∂ν) -
          ∫ _U, LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2 ∂ν := by
            rw [integral_const, probReal_univ, one_smul]
    _ = ∫ U, (∑ i, ∑ j, μ i * D i j * (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        haarMean B μ D U) i j)) - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2 ∂ν :=
      (integral_sub hleft (integrable_const _)).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun U => by
        have he (i : Fin n) (j : Fin m) : haarDriftErr B μ D U i j =
            (((U : Matrix (Fin n) (Fin n) ℝ)ᵀ * haarMean B μ D U) i j) -
              LB B μ D * μ i * D i j := by
          unfold haarDriftErr
          rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.diagonal_mul]
          change _ - LB B μ D * (μ i * D i j) = _
          ring
        rw [coord_sum_frob_sq]
        simp_rw [he, mul_sub, Finset.sum_sub_distrib, Matrix.diagonal_mul]
        have hfac : LB B μ D * ∑ i, ∑ j, (μ i * D i j) ^ 2 =
            ∑ i, ∑ j, μ i * D i j * (LB B μ D * μ i * D i j) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [hfac]

/-! ## `cor:app-sgd-half-pairings` -/

/-- `cor:app-sgd-half-pairings`: with the admissible `C_*` of `thm:app-sgd-half-drift`, the row drift
`∑_i |E⟨Δᵀu_i, Sᵀu_i⟩ − L_B μ_i 𝒬_i(Δ)| ≤ f₊√C_*`, the risk drift
`|E⟨Δ,S⟩_Σ − L_B‖ΛD‖²_F| ≤ L f₊√C_*`, and `L_B‖ΛD‖²_F ≥ d₋√B`. Expectations are over the
product `ν ⊗ batchLaw` (the state law of `def:app-sgd-state-law`). cr-2026-10-23. Source `section.tex` l. 950-959. LaTeX statement (verbatim):
```latex
\begin{corollary}[Row and risk drift]\label{cor:app-sgd-half-pairings}
Under the hypotheses of \cref{thm:app-sgd-half-drift},
\begin{align}
\sum_{i=1}^{\Nout}\Big|\EE\big\langle\Delta^\T u_i,S^\T u_i\big\rangle-L_B\,\mu_i\,\CMscr Q_i(\Delta)\Big|&\le f_+\sqrt{C_*},\label{eqn:app-sgd-row-drift}\\
\Big|\EE\big\langle\Delta,S\big\rangle_\Sigma-L_B\,\norm{\Lambda D}_\F^2\Big|&\le Lf_+\sqrt{C_*},\label{eqn:app-sgd-risk-drift}
\end{align}
and the leading total satisfies
$L_B\norm{\Lambda D}_\F^2\ge d_-\sqrt B$ with
$d_-\defeq2\sqrt{2/\pi}\,c^2f_-^2/(\pi Lf_+)$.
\end{corollary}
``` -/
theorem cor_app_sgd_half_pairings (P : HaarParams) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n m B : ℕ) (μ : Fin n → ℝ) (D : Matrix (Fin n) (Fin m) ℝ)
      (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) [IsProbabilityMeasure ν],
      IsOrthHaar ν → def_app_sgd_state_law P n m B μ D → haarKStar P ≤ kOf n m B →
      (∫⁻ U, ENNReal.ofReal (frobNorm (haarDriftErr B μ D U) ^ 2) ∂ν ≤ ENNReal.ofReal C) ∧
      (∑ i, |(∫ x, dotProduct
            (Matrix.mulVec (haarDelta x.1 D)ᵀ (haarCol x.1 i))
            (Matrix.mulVec (haarSign μ D x.1 x.2)ᵀ (haarCol x.1 i))
          ∂(ν.prod (batchLaw n m B)))
          - LB B μ D * μ i * (∑ j, D i j ^ 2)| ≤ P.fMax * Real.sqrt C) ∧
      (|(∫ x, pairIdIn (haarSigmaOut x.1 μ) (haarDelta x.1 D) (haarSign μ D x.1 x.2)
          ∂(ν.prod (batchLaw n m B)))
          - LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2| ≤ P.L * P.fMax * Real.sqrt C) ∧
      (haarDminus P * Real.sqrt (B : ℝ) ≤ LB B μ D * frobNorm (Matrix.diagonal μ * D) ^ 2) := by
  obtain ⟨C, hC, hmain⟩ := thm_app_sgd_half_drift_i P
  refine ⟨C, hC, ?_⟩
  intro n m B μ D ν hprob hν hstate hk
  have hL2 := (hmain n m B μ D ν hν hstate hk).1
  let f : Matrix.orthogonalGroup (Fin n) ℝ → ℝ :=
    fun U => frobNorm (haarDriftErr B μ D U)
  have hfmeas : AEStronglyMeasurable f ν :=
    half_drift_frob_aestronglyMeasurable μ D ν
  have hf2int : Integrable (fun U => f U ^ 2) ν := by
    apply (lintegral_ofReal_ne_top_iff_integrable (hfmeas.pow 2)
      (Filter.Eventually.of_forall fun U => sq_nonneg (f U))).1
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hL2
  have hfmem : MemLp f 2 ν := (memLp_two_iff_integrable_sq hfmeas).2 hf2int
  have hfint : Integrable f ν := hfmem.integrable (by norm_num)
  have hfL1 : ∫ U, f U ∂ν ≤ Real.sqrt C :=
    half_integral_le_sqrt ν f hfmeas (fun U => Real.sqrt_nonneg _) hC hL2
  refine ⟨hL2, ?_, ?_, half_total_leading_lower P μ D hstate⟩
  · simp_rw [half_row_difference_eq_integral μ D ν]
    let r : Fin n → Matrix.orthogonalGroup (Fin n) ℝ → ℝ :=
      fun i U => ∑ j, D i j * haarDriftErr B μ D U i j
    have hr (i : Fin n) : Integrable (r i) ν :=
      integrable_finsetSum _ fun j _ =>
        (half_drift_entry_integrable μ D ν i j).const_mul _
    calc
      ∑ i, |∫ U, ∑ j, D i j * haarDriftErr B μ D U i j ∂ν|
        = ∑ i, |∫ U, r i U ∂ν| := by rfl
      _ ≤ ∑ i, ∫ U, |r i U| ∂ν := Finset.sum_le_sum fun i _ => by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (r i)
      _ = ∫ U, ∑ i, |r i U| ∂ν := by
        rw [integral_finsetSum _ fun i _ => (hr i).abs]
      _ ≤ ∫ U, frobNorm D * f U ∂ν := by
        apply integral_mono (integrable_finsetSum _ fun i _ => (hr i).abs)
          (hfint.const_mul _)
        intro U
        exact half_row_sum_abs_le D (haarDriftErr B μ D U)
      _ = frobNorm D * ∫ U, f U ∂ν := by rw [integral_const_mul]
      _ ≤ P.fMax * Real.sqrt C :=
        mul_le_mul hstate.2.2.2.2.2.2.2.1 hfL1
          (integral_nonneg fun U => Real.sqrt_nonneg _)
          (P.fMin_pos.trans_le P.fMin_le_fMax).le
  · rw [half_risk_difference_eq_integral μ D ν]
    let q : Matrix.orthogonalGroup (Fin n) ℝ → ℝ := fun U =>
      ∑ i, ∑ j, μ i * D i j * haarDriftErr B μ D U i j
    have hq : Integrable q ν := integrable_finsetSum _ fun i _ =>
      integrable_finsetSum _ fun j _ =>
        (half_drift_entry_integrable μ D ν i j).const_mul _
    calc
      |∫ U, ∑ i, ∑ j, μ i * D i j * haarDriftErr B μ D U i j ∂ν|
        = |∫ U, q U ∂ν| := by rfl
      _ ≤ ∫ U, |q U| ∂ν := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm q
      _ ≤ ∫ U, frobNorm (Matrix.diagonal μ * D) * f U ∂ν := by
        apply integral_mono hq.abs (hfint.const_mul _)
        intro U
        simpa only [q, f, Matrix.diagonal_mul] using
          half_frob_inner_abs_le (Matrix.diagonal μ * D) (haarDriftErr B μ D U)
      _ = frobNorm (Matrix.diagonal μ * D) * ∫ U, f U ∂ν := by
        rw [integral_const_mul]
      _ ≤ (P.L * P.fMax) * Real.sqrt C :=
        mul_le_mul (half_weighted_frob_le P μ D hstate) hfL1
          (integral_nonneg fun U => Real.sqrt_nonneg _)
          (mul_nonneg (P.c_pos.trans_le P.c_le_L).le
            (P.fMin_pos.trans_le P.fMin_le_fMax).le)
      _ = P.L * P.fMax * Real.sqrt C := rfl

end Muon.SignSGD
