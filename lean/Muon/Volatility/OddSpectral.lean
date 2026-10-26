import Muon.Foundations.Conventions
import Muon.DetEquiv.Resolvent
import Muon.Setup.Frozen
import Muon.Foundations.OperatorLipschitz
import Muon.Setup.Truncation

/-!
# Appendix D, part 1: odd spectral functions, tested contractions, square truncation

Work package L-D.1 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `eqn:app-vol-sharp` (l.186), `eqn:app-vol-filters` (l.191),
`eqn:app-vol-filters-sharp` (l.196), `lem:app-vol-sharp` (l.203–223), `eqn:app-vol-contraction`
(l.259), `lem:app-vol-finite` (l.268–286), `eqn:app-vol-QT` (l.325), `lem:app-vol-square`
(l.330–345). Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.1).

Reused, not redefined: `Muon.opNorm`, `Muon.fro`, `Muon.nuc`, `Muon.Q`
(`Muon.Foundations.Conventions`); `Muon.DetEquiv.Xs` (the mixed resolvent `𝖷_s(M) = R_s(M) M`,
`Muon.DetEquiv.Resolvent`); `Muon.Setup.FrozenParams`, `Muon.Setup.FrozenSamples`,
`Muon.Setup.frozenBuf` (`Muon.Setup.Frozen`).

Encoding decisions (all recorded in the result JSON):
* The odd spectral function `f^♯` is the upper-right block of the continuous functional calculus of
  the symmetric dilation `𝒟(K) = [[0,K],[Kᵀ,0]]`, namely `Muon.Foundations.hermDilation` (indexed by
  `Fin (m+n)`, shared with L-A.F2). No SVD is used (Mathlib has no matrix SVD, card §2).
* Sup norms and Lipschitz constants are the least bounds `supNorm`, `lipConst` (real `iSup`). The
  hypothesis "odd, bounded and Lipschitz" is `IsOddBddLip`, which asserts existence of some bound.
* The minimum dimension hypothesis `min(N_out,N_in) ≤ γ⋆ B` used by `lem:app-vol-finite` and
  `lem:app-vol-square` (hidden in the source, card §6 R16) is an explicit hypothesis `hdim`.
* Second moments of random matrices are stated with `lintegral` (no junk value when not integrable).
* `Q_{ϱ,T}` of `eqn:app-vol-QT` is `oddSharp (omegaT ϱ T)` by its first equality; the integral form
  of its second equality is a proof obligation, not stated here.

No cited results (certificates) enter this module.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology
open Matrix
open Muon.Foundations (hermDilation upperRight)

noncomputable section

namespace Muon.Volatility

/-! ## Dilation and odd spectral functions -/

/-- `eqn:app-vol-sharp`, odd spectral function `f^♯(K)`, snapshot `cr-2026-10-23`. LaTeX:

\begin{equation}\label{eqn:app-vol-sharp}
f^\sharp(K)\defeq\sum_kf(s_k)\,p_k\tensor r_k .
\end{equation}

Declaration: `oddSharp f K := upperRight (cfc f (hermDilation K))`, with `hermDilation` and
`upperRight` from `Muon.Foundations.OperatorLipschitz`. Independence of the decomposition is
automatic from this definition (`section.tex` l.189). -/
def oddSharp {m n : ℕ} (f : ℝ → ℝ) (K : Mat m n) : Mat m n :=
  upperRight (cfc f (hermDilation K))

/-- `eqn:app-vol-filters`, resolvent filter `ι_s(x) = x / (x² + s)`, snapshot `cr-2026-10-23`. LaTeX
(the `ι_s` line):

\begin{equation}\label{eqn:app-vol-filters}
\iota_s(x)\defeq\frac{x}{x^2+s}\quad(s>0),\qquad
\omega_\ridge(x)\defeq\frac{x}{\sqrt{x^2+\ridge}}\quad(\ridge>0),
\end{equation}

Declaration `iotaF s x`, with `s > 0` as a hypothesis of each statement that uses it. -/
def iotaF (s x : ℝ) : ℝ := x / (x ^ 2 + s)

/-- `eqn:app-vol-filters`, regularized filter `ω_ϱ(x) = x / √(x² + ϱ)`, snapshot `cr-2026-10-23`.
LaTeX (the `ω_ϱ` line): the same display as `iotaF`, `ω_ϱ(x) = x / √(x² + ϱ)` for `ϱ > 0`. -/
def omegaF (ϱ x : ℝ) : ℝ := x / Real.sqrt (x ^ 2 + ϱ)

/-- `eqn:app-vol-QT`, truncated filter `ω_{ϱ,T}(x) = (2/π) ∫_0^T ι_{ϱ+y²}(x) dy`, first display,
snapshot `cr-2026-10-23`. LaTeX:

\begin{equation}\label{eqn:app-vol-QT}
\omega_{\ridge,T}(x)\defeq\frac2\pi\int_0^T\iota_{\ridge+y^2}(x)\,dy,\qquad
\Qridge{\ridge,T}(K)\defeq\omega_{\ridge,T}^\sharp(K)=\frac2\pi\int_0^T\mathsf X_{\ridge+y^2}(K)\,dy .
\end{equation}

The matrix `Q_{ϱ,T}(K) = ω_{ϱ,T}^♯(K)` of the same display is `oddSharp (omegaT ϱ T) K`. -/
def omegaT (ϱ T x : ℝ) : ℝ := (2 / Real.pi) * ∫ y in (0 : ℝ)..T, iotaF (ϱ + y ^ 2) x

/-- Sup norm `‖f‖_∞ = sup_x |f(x)|` (`section.tex` l.191–200, `lem:app-vol-sharp` statement),
snapshot `cr-2026-10-23`.
Real `iSup`: it is the least bound for a bounded function, which is the only case used. -/
def supNorm (f : ℝ → ℝ) : ℝ := ⨆ x : ℝ, |f x|

/-- Lipschitz constant `Lip(f) = sup_{x ≠ y} |f(x) − f(y)| / |x − y|` (`lem:app-vol-sharp`
statement), snapshot `cr-2026-10-23`. Real `iSup`; it is the least Lipschitz constant when `f` is
Lipschitz, which is the only case used. -/
def lipConst (f : ℝ → ℝ) : ℝ :=
  ⨆ p : ℝ × ℝ, if p.1 = p.2 then 0 else |f p.1 - f p.2| / |p.1 - p.2|

/-- The class of "odd, bounded and Lipschitz" functions `ℝ → ℝ` of `lem:app-vol-sharp` and
`lem:app-vol-finite`, snapshot `cr-2026-10-23`: `f(−x) = −f(x)`, `f` bounded, and `f` Lipschitz. The bounds are existential
because `supNorm` and `lipConst` already give the least constants. -/
def IsOddBddLip (f : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, f (-x) = -f x) ∧ (∃ M : ℝ, ∀ x : ℝ, |f x| ≤ M) ∧
    (∃ L : ℝ, ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|)

/-! ## Tested contractions -/

/-- `eqn:app-vol-contraction`, tested contraction `𝒦^{F,G}[f₁,f₂](K,H) = B⁻¹ Tr[F f₁^♯(K) G f₂^♯(H)ᵀ]`,
snapshot `cr-2026-10-23`. LaTeX:

\begin{equation}\label{eqn:app-vol-contraction}
\mathcal K^{F,G}[f_1,f_2](K,H)\defeq\frac1B\Tr\big[F\,f_1^\sharp(K)\,G\,f_2^\sharp(H)^\T\big],
\qquad
\mathcal K^{F,G}_{s,u}(K,H)\defeq\mathcal K^{F,G}[\iota_s,\iota_u](K,H).
\end{equation}

`B` is a separate parameter (the batch size), `F` and `G` are deterministic. -/
def contraction {m n : ℕ} (B : ℕ) (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (f₁ f₂ : ℝ → ℝ) (K H : Mat m n) : ℝ :=
  (B : ℝ)⁻¹ * Matrix.trace (F * oddSharp f₁ K * G * (oddSharp f₂ H)ᵀ)

/-- `eqn:app-vol-contraction`, resolvent-filter contraction `𝒦^{F,G}_{s,u}(K,H) = 𝒦^{F,G}[ι_s, ι_u](K,H)`
(the sentence after the display), snapshot `cr-2026-10-23`. -/
def contractionRes {m n : ℕ} (B : ℕ) (F : Matrix (Fin m) (Fin m) ℝ)
    (G : Matrix (Fin n) (Fin n) ℝ) (s u : ℝ) (K H : Mat m n) : ℝ :=
  contraction B F G (iotaF s) (iotaF u) K H

/-! ## Odd spectral functions: statements -/

/-! ### Helpers for `eqn_app_vol_filters_sharp_i` (block form of the dilation resolvent) -/

private lemma filt_hermDilation_eq {m n : ℕ} (K : Mat m n) :
    hermDilation K = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 K Kᵀ 0) :=
  rfl

private lemma filt_reindex_mul {m n : ℕ} (M N : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) ℝ) :
    Matrix.reindex finSumFinEquiv finSumFinEquiv M * Matrix.reindex finSumFinEquiv finSumFinEquiv N
      = Matrix.reindex finSumFinEquiv finSumFinEquiv (M * N) :=
  (map_mul (reindexAlgEquiv ℝ ℝ finSumFinEquiv) M N).symm

private lemma filt_isUnit {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat a a)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'

private lemma filt_sq_add {m n : ℕ} (K : Mat m n) (s : ℝ) :
    hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n))
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m)) 0 0 (Kᵀ * K + s • (1 : Mat n n))) := by
  have hX : hermDilation K ^ 2 = Matrix.reindex finSumFinEquiv finSumFinEquiv
      (Matrix.fromBlocks (K * Kᵀ) 0 0 (Kᵀ * K)) := by
    rw [sq, filt_hermDilation_eq K, filt_reindex_mul, Matrix.fromBlocks_multiply]
    simp
  rw [hX]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.one_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.add_apply, Matrix.smul_apply, Fin.ext_iff]
  all_goals first | done | (intro h; exfalso; omega)

private lemma filt_dil_resolvent {m n : ℕ} (K : Mat m n) (s : ℝ) (hs : 0 < s) :
    cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K)
      = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹) := by
  have hsaX : IsSelfAdjoint (hermDilation K) := Muon.Foundations.hermDilation_isHermitian K
  have hcont : ContinuousOn (fun x : ℝ => x ^ 2 + s) (spectrum ℝ (hermDilation K)) :=
    (by fun_prop : Continuous fun x : ℝ => x ^ 2 + s).continuousOn
  have hcontI : ContinuousOn (fun x : ℝ => (x ^ 2 + s)⁻¹) (spectrum ℝ (hermDilation K)) :=
    (by fun_prop : Continuous fun x : ℝ => x ^ 2 + s).continuousOn.inv₀
      (fun x _ => by positivity)
  have hpoly : cfc (fun x : ℝ => x ^ 2 + s) (hermDilation K)
      = hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n)) := by
    rw [cfc_add (a := hermDilation K) (f := fun x : ℝ => x ^ 2) (g := fun _ : ℝ => s),
      cfc_pow_id (hermDilation K) 2 hsaX, cfc_const s (hermDilation K) hsaX,
      Algebra.algebraMap_eq_smul_one]
  have hAu := filt_isUnit K s hs
  have hBu : IsUnit (Kᵀ * K + s • (1 : Mat n n)).det := by
    have h := filt_isUnit Kᵀ s hs
    rwa [Matrix.transpose_transpose] at h
  have hmulW : (hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n)))
      * cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K) = 1 := by
    rw [← hpoly, ← cfc_mul (fun x : ℝ => x ^ 2 + s) (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K)
      hcont hcontI]
    have hfun : (fun x : ℝ => (x ^ 2 + s) * (x ^ 2 + s)⁻¹) = (1 : ℝ → ℝ) :=
      funext fun x => mul_inv_cancel₀ (by positivity)
    rw [hfun]
    exact cfc_one (R := ℝ) (ha := hsaX)
  have hW0 : (hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n)))
      * Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹)
        = 1 := by
    rw [filt_sq_add K s, filt_reindex_mul, Matrix.fromBlocks_multiply]
    simp only [Matrix.mul_nonsing_inv _ hAu, Matrix.mul_nonsing_inv _ hBu, Matrix.zero_mul,
      Matrix.mul_zero, add_zero, zero_add]
    rw [Matrix.fromBlocks_one]
    exact map_one (reindexAlgEquiv ℝ ℝ finSumFinEquiv)
  have hc := mul_eq_one_comm.mp hW0
  calc cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K)
      = 1 * cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K) := (one_mul _).symm
    _ = (Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹)
          * (hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n)))) *
          cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K) := by rw [hc]
    _ = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹)
          * ((hermDilation K ^ 2 + s • (1 : Mat (m + n) (m + n)))
            * cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K)) := by
          rw [Matrix.mul_assoc]
    _ = Matrix.reindex finSumFinEquiv finSumFinEquiv
          (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹) := by
          rw [hmulW, Matrix.mul_one]

private lemma filt_upperRight_block {m n : ℕ} (K : Mat m n) (s : ℝ) :
    upperRight (hermDilation K * Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (K * Kᵀ + s • (1 : Mat m m))⁻¹ 0 0 (Kᵀ * K + s • (1 : Mat n n))⁻¹))
      = K * (Kᵀ * K + s • (1 : Mat n n))⁻¹ := by
  rw [filt_hermDilation_eq K, filt_reindex_mul, Matrix.fromBlocks_multiply]
  ext i j
  simp [upperRight, Matrix.reindex_apply, Matrix.mul_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]

/-- `eqn:app-vol-filters-sharp`, first identity, snapshot `cr-2026-10-23`. Declaration
`Muon.Volatility.eqn_app_vol_filters_sharp_i`. Here `Muon.DetEquiv.Xs K s = R_s(K) K =
(KKᵀ + s Id)⁻¹ K` (`eqn:app-de-RXdef`). LaTeX (display of `eqn:app-vol-filters-sharp`):

\begin{equation}\label{eqn:app-vol-filters-sharp}
\iota_s^\sharp(K)=\mathsf X_s(K)=\big(KK^\T+s\Id\big)^{-1}K,\qquad
\omega_\ridge^\sharp(K)=\Qridge\ridge(K),
\end{equation} -/
theorem eqn_app_vol_filters_sharp_i {m n : ℕ} {s : ℝ} (hs : 0 < s) (K : Mat m n) :
    oddSharp (iotaF s) K = Muon.DetEquiv.Xs K s := by
  have hsaX : IsSelfAdjoint (hermDilation K) := Muon.Foundations.hermDilation_isHermitian K
  have hcfc : cfc (iotaF s) (hermDilation K)
      = hermDilation K * cfc (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K) := by
    have hf : iotaF s = fun x : ℝ => (fun x : ℝ => x) x * (fun x : ℝ => (x ^ 2 + s)⁻¹) x :=
      funext fun x => div_eq_mul_inv _ _
    rw [hf, cfc_mul (fun x : ℝ => x) (fun x : ℝ => (x ^ 2 + s)⁻¹) (hermDilation K)
      (by fun_prop) ((by fun_prop : Continuous fun x : ℝ => x ^ 2 + s).continuousOn.inv₀
        (fun x _ => by positivity)), cfc_id' ℝ (hermDilation K) hsaX]
  have hXs : Muon.DetEquiv.Xs K s = K * (Kᵀ * K + s • (1 : Mat n n))⁻¹ := by
    unfold Muon.DetEquiv.Xs
    rw [(Muon.DetEquiv.lem_app_de_resolvent K s hs).2.2.2.1]
    rfl
  rw [hXs, oddSharp, hcfc, filt_dil_resolvent K s hs, filt_upperRight_block K s]

/-- `eqn:app-vol-filters-sharp`, second identity `ω_ϱ^♯(K) = Q_ϱ(K)`, snapshot `cr-2026-10-23`.
Declaration `Muon.Volatility.eqn_app_vol_filters_sharp_ii`. Its proof is the bridge
`Muon.Foundations.upperRight_cfc_hermDilation` (L-A.F2) after the function identity
`x ↦ x (x²+ϱ)^{-1/2} = omegaF ϱ`. LaTeX (same display as part (i)):

\begin{equation}\label{eqn:app-vol-filters-sharp}
\iota_s^\sharp(K)=\mathsf X_s(K)=\big(KK^\T+s\Id\big)^{-1}K,\qquad
\omega_\ridge^\sharp(K)=\Qridge\ridge(K),
\end{equation} -/
theorem eqn_app_vol_filters_sharp_ii {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) :
    oddSharp (omegaF ϱ) K = Muon.Q ϱ K := by
  have hfun : omegaF ϱ = fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ)) := by
    funext x
    have hpos : 0 < x ^ 2 + ϱ := by positivity
    unfold omegaF
    rw [Real.sqrt_eq_rpow, Real.rpow_neg hpos.le, div_eq_mul_inv]
  unfold oddSharp
  rw [hfun, Muon.Foundations.upperRight_cfc_hermDilation hϱ K]

/-! ### Helpers for `lem:app-vol-sharp` part (i) (proved; the Lipschitz conjunct) -/

private lemma upperRight_sub_aux {m n : ℕ} (X Y : Mat (m + n) (m + n)) :
    upperRight (X - Y) = upperRight X - upperRight Y := by
  ext i j; simp [upperRight]

private lemma hermDilation_sub_aux {m n : ℕ} (K L : Mat m n) :
    hermDilation (K - L) = hermDilation K - hermDilation L := by
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [hermDilation, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd, Matrix.transpose_apply]

private lemma lipConst_bound_aux (f : ℝ → ℝ) (hf : IsOddBddLip f) :
    0 ≤ lipConst f ∧ ∀ x y : ℝ, |f x - f y| ≤ lipConst f * |x - y| := by
  obtain ⟨_, _, ⟨L, hL⟩⟩ := hf
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ =>
      if p.1 = p.2 then (0 : ℝ) else |f p.1 - f p.2| / |p.1 - p.2|) := by
    refine ⟨max L 0, ?_⟩
    rintro _ ⟨p, rfl⟩
    by_cases h : p.1 = p.2
    · simp only [h, ite_true]; exact le_max_right _ _
    · simp only [h, ite_false]
      have hpos : 0 < |p.1 - p.2| := abs_pos.mpr (sub_ne_zero.mpr h)
      rw [div_le_iff₀ hpos]
      exact (hL p.1 p.2).trans (by nlinarith [le_max_left L 0, abs_nonneg (p.1 - p.2)])
  have hnn : 0 ≤ lipConst f := by
    have := le_ciSup hbdd (1, 0)
    simp only [lipConst]
    refine le_trans ?_ this
    simp only [show ((1:ℝ), (0:ℝ)).1 ≠ ((1:ℝ), (0:ℝ)).2 by norm_num, ite_false]
    positivity
  refine ⟨hnn, fun x y => ?_⟩
  by_cases h : x = y
  · subst h; simp
  · have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr h)
    have := le_ciSup hbdd (x, y)
    simp only [ite_eq_right h] at this
    unfold lipConst
    rw [← div_le_iff₀ hpos]
    exact this

private lemma fro_nn_aux {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma fro_part3_aux {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) (K K' : Mat m n) :
    fro (oddSharp f K - oddSharp f K') ≤ lipConst f * fro (K - K') := by
  obtain ⟨hnn, hlip⟩ := lipConst_bound_aux f hf
  have hLW : LipschitzWith (Real.toNNReal (lipConst f)) f := by
    refine LipschitzWith.of_dist_le' (fun x y => ?_)
    simp only [Real.dist_eq, Real.coe_toNNReal _ hnn]
    exact hlip x y
  have hA := Muon.Foundations.hermDilation_isHermitian K
  have hB := Muon.Foundations.hermDilation_isHermitian K'
  have hcA : (cfc f (hermDilation K)).IsHermitian := by
    have : IsSelfAdjoint (cfc f (hermDilation K)) := cfc_predicate _ _
    exact this
  have hcB : (cfc f (hermDilation K')).IsHermitian := by
    have : IsSelfAdjoint (cfc f (hermDilation K')) := cfc_predicate _ _
    exact this
  have hX := Muon.Foundations.fro_cfc_sub_cfc_le (hermDilation K) (hermDilation K') hA hB f Set.univ
    Set.ordConnected_univ (Real.toNNReal (lipConst f)) hLW.lipschitzOnWith
    (Set.subset_univ _) (Set.subset_univ _)
  rw [Real.coe_toNNReal _ hnn, ← hermDilation_sub_aux] at hX
  have hsub : oddSharp f K - oddSharp f K' =
      upperRight (cfc f (hermDilation K) - cfc f (hermDilation K')) := by
    unfold oddSharp; rw [upperRight_sub_aux]
  have hsq := Muon.Foundations.fro_upperRight_sq_le _ (hcA.sub hcB)
  have h2 := Muon.Foundations.fro_hermDilation (K - K')
  rw [hsub]
  have h1 : fro (cfc f (hermDilation K) - cfc f (hermDilation K')) ^ 2 ≤
      (lipConst f * fro (hermDilation (K - K'))) ^ 2 :=
    pow_le_pow_left₀ (fro_nn_aux _) hX 2
  rw [mul_pow, h2] at h1
  have h3 : fro (upperRight (cfc f (hermDilation K) - cfc f (hermDilation K'))) ^ 2 ≤
      (lipConst f * fro (K - K')) ^ 2 := by
    rw [mul_pow]; nlinarith [h1, hsq]
  exact (pow_le_pow_iff_left₀ (fro_nn_aux _) (mul_nonneg hnn (fro_nn_aux _)) two_ne_zero).mp h3

private theorem opNorm_cfc_le_P1 {k : ℕ} (A : Mat k k) (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x, |f x| ≤ M) : opNorm (cfc f A) ≤ M := by
  rw [Muon.opNorm_eq_norm]
  open scoped Matrix.Norms.L2Operator in
  exact norm_cfc_le hM (fun x _ => by simpa using h x)

private theorem opNorm_upperRight_le_P1 {m n : ℕ} (X : Mat (m + n) (m + n)) :
    opNorm (upperRight X) ≤ opNorm X := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) (fun x => ?_)
  set y : EuclideanSpace ℝ (Fin (m + n)) := WithLp.toLp 2 (Fin.append (0 : Fin m → ℝ) x.ofLp) with hy
  have hyn : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [hy, Fin.sum_univ_add, Fin.append_left, Fin.append_right]
  have hle := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)).le_opNorm y
  rw [← hyn]
  refine le_trans ?_ hle
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_add]
  have h2 : 0 ≤ ∑ i : Fin n, ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) y) (Fin.natAdd m i)‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  refine le_trans (le_of_eq ?_) (le_add_of_nonneg_right h2)
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [hy, Matrix.mulVec, dotProduct, upperRight, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right]

private theorem fro_sq_cfc_P1 {k : ℕ} (A : Mat k k) (hA : A.IsHermitian) (f : ℝ → ℝ) :
    fro (cfc f A) ^ 2 = ∑ i, f (hA.eigenvalues i) ^ 2 := by
  have hY : (cfc f A).IsHermitian := by
    have : IsSelfAdjoint (cfc f A) := cfc_predicate _ _
    exact this
  have h1 : fro (cfc f A) ^ 2 = Matrix.trace (cfc f A * cfc f A) := by
    unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := hY.apply i j
    simp only [star_trivial] at this
    rw [Real.norm_eq_abs, sq_abs, sq]
    rw [this]
  rw [h1, hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [show ∀ (U D : Mat k k), (U * D * (star U)) * (U * D * (star U)) =
      U * (D * (star U * U) * D) * star U from fun U D => by simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc]
  rw [show (star (hA.eigenvectorUnitary : Mat k k)) * (hA.eigenvectorUnitary : Mat k k) = 1 from
    Unitary.coe_star_mul_self _]
  rw [← Matrix.mul_assoc, Matrix.mul_one, Matrix.mul_assoc]
  rw [Matrix.one_mul, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  simp [sq]

private theorem rank_add_le_aux_P1 {k l : ℕ} (A B : Matrix (Fin k) (Fin l) ℝ) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rw [Matrix.mulVecLin_add]
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem rank_hermDilation_le_P1 {m n : ℕ} (K : Mat m n) :
    (hermDilation K).rank ≤ 2 * min m n := by
  classical
  let P : Mat (m + n) m := Matrix.of fun i j => if i = Fin.castAdd n j then 1 else 0
  let Q : Mat (m + n) n := Matrix.of fun i j => if i = Fin.natAdd m j then 1 else 0
  have hne : ∀ (a : Fin m) (b : Fin n), Fin.castAdd n a ≠ Fin.natAdd m b := fun a b h => by
    have := congrArg Fin.val h; simp at this; omega
  have hne' : ∀ (a : Fin m) (b : Fin n), Fin.natAdd m b ≠ Fin.castAdd n a := fun a b h => hne a b h.symm
  have hD : hermDilation K = P * K * Qᵀ + Q * Kᵀ * Pᵀ := by
    ext i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp [hermDilation, P, Q, Matrix.mul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, finSumFinEquiv_symm_apply_castAdd, hne, hne',
        finSumFinEquiv_symm_apply_natAdd]
  have h1 : (P * K * Qᵀ).rank ≤ K.rank :=
    (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  have h2 : (Q * Kᵀ * Pᵀ).rank ≤ K.rank :=
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans
      (Matrix.rank_transpose K).le
  have h3 : K.rank ≤ min m n := by
    refine le_min ?_ ?_
    · simpa using Matrix.rank_le_height K
    · simpa using Matrix.rank_le_width K
  rw [hD]
  have := rank_add_le_aux_P1 (P * K * Qᵀ) (Q * Kᵀ * Pᵀ)
  omega

private theorem sharp_op_fro_aux_P1 {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) (K : Mat m n) :
    opNorm (oddSharp f K) ≤ supNorm f ∧
    fro (oddSharp f K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f := by
  obtain ⟨hodd, ⟨B, hB⟩, _⟩ := hf
  have hbdd : BddAbove (Set.range fun x : ℝ => |f x|) := ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  have hle : ∀ x, |f x| ≤ supNorm f := fun x => le_ciSup hbdd x
  have hM : 0 ≤ supNorm f := (abs_nonneg _).trans (hle 0)
  have hf0 : f 0 = 0 := by have := hodd 0; simp at this; linarith
  have hA := Muon.Foundations.hermDilation_isHermitian K
  refine ⟨?_, ?_⟩
  · exact (opNorm_upperRight_le_P1 _).trans (opNorm_cfc_le_P1 _ f _ hM hle)
  · have hcA : (cfc f (hermDilation K)).IsHermitian := by
      have : IsSelfAdjoint (cfc f (hermDilation K)) := cfc_predicate _ _
      exact this
    have h1 := Muon.Foundations.fro_upperRight_sq_le _ hcA
    rw [fro_sq_cfc_P1 _ hA] at h1
    have hcount : ∑ i, f (hA.eigenvalues i) ^ 2 ≤
        ((min m n : ℕ) : ℝ) * 2 * supNorm f ^ 2 := by
      have h2 : ∑ i, f (hA.eigenvalues i) ^ 2 ≤
          ∑ i, if hA.eigenvalues i ≠ 0 then supNorm f ^ 2 else 0 := by
        refine Finset.sum_le_sum fun i _ => ?_
        by_cases h : hA.eigenvalues i = 0
        · simp [h, hf0]
        · simp only [ne_eq, h, not_false_eq_true, ite_true]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (hle _) 2
      refine h2.trans ?_
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hc : (Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card ≤ 2 * min m n := by
        rw [← Fintype.card_subtype, ← hA.rank_eq_card_non_zero_eigs]
        exact rank_hermDilation_le_P1 K
      have : ((Finset.univ.filter fun i => hA.eigenvalues i ≠ 0).card : ℝ) ≤ 2 * ((min m n : ℕ) : ℝ) := by
        exact_mod_cast hc
      nlinarith [sq_nonneg (supNorm f)]
    have h3 : fro (oddSharp f K) ^ 2 ≤ ((min m n : ℕ) : ℝ) * supNorm f ^ 2 := by
      unfold oddSharp; linarith
    calc fro (oddSharp f K) = Real.sqrt (fro (oddSharp f K) ^ 2) :=
          (Real.sqrt_sq (fro_nn_aux _)).symm
      _ ≤ Real.sqrt (((min m n : ℕ) : ℝ) * supNorm f ^ 2) := Real.sqrt_le_sqrt h3
      _ = Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f := by
          rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hM]

/-- `lem:app-vol-sharp`, part (i): the operator, Frobenius and Lipschitz bounds for odd spectral
functions, snapshot `cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_sharp_i`.
The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Odd spectral functions]\label{lem:app-vol-sharp}
Let $f$ be odd, bounded and Lipschitz on $\R$, with $\norm f_\infty\defeq\sup_x\abs{f(x)}$
and Lipschitz constant $\operatorname{Lip}(f)$. For all $K,K'\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-vol-sharp-bounds}
\begin{gathered}
\norm{f^\sharp(K)}\le\norm f_\infty,\qquad
\norm{f^\sharp(K)}_\F\le\sqrt{\min(\Nout,\Nin)}\,\norm f_\infty,\\
\norm{f^\sharp(K)-f^\sharp(K')}_\F\le\operatorname{Lip}(f)\,\norm{K-K'}_\F .
\end{gathered}
\end{equation}
The filters \cref{eqn:app-vol-filters} satisfy
\begin{equation}\label{eqn:app-vol-filter-constants}
\norm{\iota_s}_\infty=\frac1{2\sqrt s},\quad \operatorname{Lip}(\iota_s)\le\frac1s,\qquad
\norm{\omega_\ridge}_\infty=1,\quad \operatorname{Lip}(\omega_\ridge)\le\ridge^{-1/2},
\end{equation}
and, for all $s,s'\ge s_\circ>0$ and $\ridge,\ridge'\ge\ridge_\circ>0$,
\begin{equation}\label{eqn:app-vol-filter-parameter}
\norm{\iota_s-\iota_{s'}}_\infty\le\frac{\abs{s-s'}}{s_\circ^{3/2}},\qquad
\norm{\omega_\ridge-\omega_{\ridge'}}_\infty\le\frac{\abs{\ridge-\ridge'}}{2\ridge_\circ} .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_sharp_i {m n : ℕ} (f : ℝ → ℝ) (hf : IsOddBddLip f) (K K' : Mat m n) :
    opNorm (oddSharp f K) ≤ supNorm f ∧
    fro (oddSharp f K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f ∧
    fro (oddSharp f K - oddSharp f K') ≤ lipConst f * fro (K - K') := by
  obtain ⟨h1, h2⟩ := sharp_op_fro_aux_P1 f hf K
  exact ⟨h1, h2, fro_part3_aux f hf K K'⟩

private lemma iota_abs_le_P2 {s : ℝ} (hs : 0 < s) (x : ℝ) :
    |iotaF s x| ≤ 1 / (2 * Real.sqrt s) := by
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hP : 0 < x ^ 2 + s := by nlinarith [sq_nonneg x]
  unfold iotaF
  rw [abs_div, abs_of_pos hP, div_le_div_iff₀ hP (by positivity)]
  have h1 : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - Real.sqrt s), abs_nonneg x]

private lemma supNorm_iota_P2 {s : ℝ} (hs : 0 < s) :
    supNorm (iotaF s) = 1 / (2 * Real.sqrt s) := by
  have hsp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  unfold supNorm
  apply ciSup_eq_of_forall_le_of_forall_lt_exists_gt
  · intro x; exact iota_abs_le_P2 hs x
  · intro w hw
    refine ⟨Real.sqrt s, ?_⟩
    have hval : |iotaF s (Real.sqrt s)| = 1 / (2 * Real.sqrt s) := by
      unfold iotaF
      rw [abs_of_pos (div_pos hsp (by rw [hsq]; linarith))]
      rw [hsq]
      field_simp
      nlinarith [hsq]
    rw [hval]; exact hw

private lemma iota_lip_P2 {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    |iotaF s x - iotaF s y| ≤ (1 / s) * |x - y| := by
  have hx : 0 < x ^ 2 + s := by nlinarith [sq_nonneg x]
  have hy : 0 < y ^ 2 + s := by nlinarith [sq_nonneg y]
  have key : iotaF s x - iotaF s y = (x - y) * (s - x * y) / ((x ^ 2 + s) * (y ^ 2 + s)) := by
    unfold iotaF
    field_simp
    ring
  have hk : s * |s - x * y| ≤ (x ^ 2 + s) * (y ^ 2 + s) := by
    rcases abs_cases (s - x * y) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h]
    · nlinarith [mul_nonneg hs.le (sq_nonneg (x + y)), mul_nonneg hs.le (sq_nonneg x),
        mul_nonneg hs.le (sq_nonneg y), sq_nonneg (x * y)]
    · nlinarith [mul_nonneg hs.le (sq_nonneg (x - y)), mul_nonneg hs.le (sq_nonneg x),
        mul_nonneg hs.le (sq_nonneg y), sq_nonneg (x * y), sq_nonneg (x + y), mul_pos hs hs]
  have hP : 0 < (x ^ 2 + s) * (y ^ 2 + s) := mul_pos hx hy
  have hdiv : |s - x * y| ≤ (x ^ 2 + s) * (y ^ 2 + s) / s := by
    rw [le_div_iff₀ hs]; linarith [mul_comm s |s - x * y|]
  rw [key, abs_div, abs_mul, abs_of_pos hP, div_le_iff₀ hP]
  have hfin : 1 / s * |x - y| * ((x ^ 2 + s) * (y ^ 2 + s)) =
      |x - y| * ((x ^ 2 + s) * (y ^ 2 + s) / s) := by ring
  rw [hfin]
  exact mul_le_mul_of_nonneg_left hdiv (abs_nonneg _)

private lemma lipConst_le_P2 (f : ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (h : ∀ x y : ℝ, |f x - f y| ≤ L * |x - y|) : lipConst f ≤ L := by
  unfold lipConst
  apply ciSup_le
  rintro ⟨a, b⟩
  dsimp only
  split_ifs with hab
  · exact hL
  · have hpos : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    rw [div_le_iff₀ hpos]
    exact h a b

private lemma iota_odd_bdd_lip_P2 {s : ℝ} (hs : 0 < s) : IsOddBddLip (iotaF s) := by
  unfold IsOddBddLip
  refine ⟨fun x => ?_, ⟨1 / (2 * Real.sqrt s), fun x => iota_abs_le_P2 hs x⟩,
    ⟨1 / s, fun x y => iota_lip_P2 hs x y⟩⟩
  unfold iotaF
  rw [neg_sq, neg_div]

-- omega helpers
private lemma omega_abs_le_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) (x : ℝ) : |omegaF ϱ x| ≤ 1 := by
  have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
  have hsp : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
  have hle : |x| ≤ Real.sqrt (x ^ 2 + ϱ) := Real.abs_le_sqrt (by nlinarith)
  unfold omegaF
  rw [abs_div, abs_of_pos hsp, div_le_one hsp]
  exact hle

private lemma omega_odd_P2 (ϱ : ℝ) (x : ℝ) : omegaF ϱ (-x) = -omegaF ϱ x := by
  unfold omegaF
  rw [neg_sq, neg_div]

private lemma omega_hasDeriv_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) (x : ℝ) :
    HasDerivAt (omegaF ϱ) (ϱ / (Real.sqrt (x ^ 2 + ϱ)) ^ 3) x := by
  have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
  have hsp : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
  have hsq : Real.sqrt (x ^ 2 + ϱ) ^ 2 = x ^ 2 + ϱ := Real.sq_sqrt hP.le
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2 + ϱ) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).add_const ϱ
  have h2 := h1.sqrt hP.ne'
  have h3 := (hasDerivAt_id' x).div h2 hsp.ne'
  refine h3.congr_deriv ?_
  have h4 : x * (2 * x / (2 * Real.sqrt (x ^ 2 + ϱ))) = x ^ 2 / Real.sqrt (x ^ 2 + ϱ) := by
    field_simp
  have h5 : Real.sqrt (x ^ 2 + ϱ) - x ^ 2 / Real.sqrt (x ^ 2 + ϱ) = ϱ / Real.sqrt (x ^ 2 + ϱ) := by
    rw [eq_div_iff hsp.ne', sub_mul, div_mul_cancel₀ _ hsp.ne']
    nlinarith [hsq]
  rw [h4, one_mul, h5]
  have h6 : ϱ / Real.sqrt (x ^ 2 + ϱ) / Real.sqrt (x ^ 2 + ϱ) ^ 2 = ϱ / Real.sqrt (x ^ 2 + ϱ) ^ 3 := by
    field_simp
  exact h6

private lemma omega_deriv_bound_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) (x : ℝ) :
    ‖ϱ / (Real.sqrt (x ^ 2 + ϱ)) ^ 3‖ ≤ 1 / Real.sqrt ϱ := by
  have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
  have hsp : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
  have hrp : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hrsq : Real.sqrt ϱ ^ 2 = ϱ := Real.sq_sqrt hϱ.le
  have hA : Real.sqrt ϱ ≤ Real.sqrt (x ^ 2 + ϱ) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  have hA3 : (Real.sqrt ϱ) ^ 3 ≤ (Real.sqrt (x ^ 2 + ϱ)) ^ 3 :=
    pow_le_pow_left₀ hrp.le hA 3
  rw [Real.norm_eq_abs, abs_of_pos (div_pos hϱ (pow_pos hsp 3)), div_le_div_iff₀ (pow_pos hsp 3) hrp]
  have : ϱ * Real.sqrt ϱ = Real.sqrt ϱ ^ 3 := by
    have h3 : Real.sqrt ϱ ^ 3 = Real.sqrt ϱ ^ 2 * Real.sqrt ϱ := by ring
    rw [h3, hrsq]
  nlinarith

private lemma omega_lip_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) (x y : ℝ) :
    |omegaF ϱ x - omegaF ϱ y| ≤ (1 / Real.sqrt ϱ) * |x - y| := by
  have hd : ∀ z ∈ (Set.univ : Set ℝ), HasDerivWithinAt (omegaF ϱ)
      (ϱ / (Real.sqrt (z ^ 2 + ϱ)) ^ 3) Set.univ z :=
    fun z _ => (omega_hasDeriv_P2 hϱ z).hasDerivWithinAt
  have hb : ∀ z ∈ (Set.univ : Set ℝ), ‖ϱ / (Real.sqrt (z ^ 2 + ϱ)) ^ 3‖ ≤ 1 / Real.sqrt ϱ :=
    fun z _ => omega_deriv_bound_P2 hϱ z
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hb convex_univ
    (Set.mem_univ x) (Set.mem_univ y)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at this
  rw [abs_sub_comm (omegaF ϱ x), abs_sub_comm x y]
  exact this

private lemma supNorm_omega_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) : supNorm (omegaF ϱ) = 1 := by
  have hbdd : BddAbove (Set.range fun x : ℝ => |omegaF ϱ x|) := ⟨1, by
    rintro _ ⟨x, rfl⟩; exact omega_abs_le_P2 hϱ x⟩
  unfold supNorm
  apply le_antisymm
  · exact ciSup_le fun x => omega_abs_le_P2 hϱ x
  · by_contra hcon
    set M := ⨆ x : ℝ, |omegaF ϱ x| with hMdef
    have hcon' : M < 1 := not_le.mp hcon
    have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (le_ciSup hbdd 0)
    have hMle : ∀ x : ℝ, |omegaF ϱ x| ≤ M := fun x => le_ciSup hbdd x
    -- witness x = n with n > M^2 ϱ / (1 - M^2)
    have hpos : 0 < 1 - M ^ 2 := by nlinarith
    obtain ⟨n, hn⟩ := exists_nat_gt (M ^ 2 * ϱ / (1 - M ^ 2))
    have hn' : M ^ 2 * ϱ < n * (1 - M ^ 2) := by
      rw [div_lt_iff₀ hpos] at hn; linarith
    have hn1 : (1 : ℝ) ≤ n := by
      have : (0:ℝ) < n := by
        have : (0:ℝ) ≤ M ^ 2 * ϱ / (1 - M ^ 2) := by positivity
        linarith
      have : 0 < n := by exact_mod_cast this
      exact_mod_cast this
    set x : ℝ := (n : ℝ) with hx
    have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
    have hsp : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
    have hsq : Real.sqrt (x ^ 2 + ϱ) ^ 2 = x ^ 2 + ϱ := Real.sq_sqrt hP.le
    have hv : M < |omegaF ϱ x| := by
      unfold omegaF
      rw [abs_div, abs_of_pos hsp, lt_div_iff₀ hsp]
      have hxx : |x| ^ 2 = x ^ 2 := sq_abs x
      have key : (M * Real.sqrt (x ^ 2 + ϱ)) ^ 2 < |x| ^ 2 := by
        rw [mul_pow, hsq, hxx]
        nlinarith [mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ x) (by linarith : (0:ℝ) ≤ x - 1)) hpos.le]
      nlinarith [key, abs_nonneg x, mul_nonneg hM0 hsp.le]
    exact absurd (hMle x) (not_le.mpr hv)

private lemma omega_odd_bdd_lip_P2 {ϱ : ℝ} (hϱ : 0 < ϱ) : IsOddBddLip (omegaF ϱ) := by
  unfold IsOddBddLip
  exact ⟨omega_odd_P2 ϱ, ⟨1, omega_abs_le_P2 hϱ⟩, ⟨1 / Real.sqrt ϱ, omega_lip_P2 hϱ⟩⟩

private lemma iota_param_P2 {s s' s₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hs' : s₀ ≤ s')
    (x : ℝ) : |iotaF s x - iotaF s' x| ≤ |s - s'| / (s₀ * Real.sqrt s₀) := by
  have hsp₀ : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
  have hsv : 0 < s := lt_of_lt_of_le hs₀ hs
  have hP' : 0 < x ^ 2 + s' := by nlinarith [sq_nonneg x]
  have key : iotaF s x - iotaF s' x = iotaF s x * ((s' - s) / (x ^ 2 + s')) := by
    unfold iotaF
    field_simp
    ring
  have h1 : |iotaF s x| ≤ 1 / (2 * Real.sqrt s₀) := by
    refine (iota_abs_le_P2 hsv x).trans ?_
    exact one_div_le_one_div_of_le (mul_pos two_pos hsp₀)
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (by norm_num))
  have h2 : |s' - s| / (x ^ 2 + s') ≤ |s - s'| / s₀ := by
    rw [abs_sub_comm]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hs₀ (by nlinarith [sq_nonneg x])
  rw [key, abs_mul, abs_div, abs_of_pos hP']
  calc |iotaF s x| * (|s' - s| / (x ^ 2 + s'))
      ≤ (1 / (2 * Real.sqrt s₀)) * (|s - s'| / s₀) :=
        mul_le_mul h1 h2 (div_nonneg (abs_nonneg _) hP'.le)
          (one_div_pos.mpr (mul_pos two_pos hsp₀)).le
    _ = (|s - s'| / (s₀ * Real.sqrt s₀)) * (1 / 2) := by
        field_simp
    _ ≤ |s - s'| / (s₀ * Real.sqrt s₀) :=
        mul_le_of_le_one_right (div_nonneg (abs_nonneg _) (mul_pos hs₀ hsp₀).le) (by norm_num)

private lemma omega_param_P2 {ϱ ϱ' ϱ₀ : ℝ} (hϱ₀ : 0 < ϱ₀) (hϱ : ϱ₀ ≤ ϱ) (hϱ' : ϱ₀ ≤ ϱ')
    (x : ℝ) : |omegaF ϱ x - omegaF ϱ' x| ≤ |ϱ - ϱ'| / (2 * ϱ₀) := by
  have hP : 0 < x ^ 2 + ϱ := by nlinarith [sq_nonneg x]
  have hP' : 0 < x ^ 2 + ϱ' := by nlinarith [sq_nonneg x]
  have hrp : 0 < Real.sqrt ϱ₀ := Real.sqrt_pos.mpr hϱ₀
  have hrr : Real.sqrt ϱ₀ * Real.sqrt ϱ₀ = ϱ₀ := Real.mul_self_sqrt hϱ₀.le
  have hA' : Real.sqrt ϱ₀ ≤ Real.sqrt (x ^ 2 + ϱ) :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  have hB' : Real.sqrt ϱ₀ ≤ Real.sqrt (x ^ 2 + ϱ') :=
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
  have hxA : |x| ≤ Real.sqrt (x ^ 2 + ϱ) := Real.abs_le_sqrt (by linarith)
  have hid : omegaF ϱ x - omegaF ϱ' x =
      x * (ϱ' - ϱ) / (Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') *
        (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ'))) := by
    unfold omegaF
    have hA : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
    have hB : 0 < Real.sqrt (x ^ 2 + ϱ') := Real.sqrt_pos.mpr hP'
    have hA2 : Real.sqrt (x ^ 2 + ϱ) ^ 2 = x ^ 2 + ϱ := Real.sq_sqrt hP.le
    have hB2 : Real.sqrt (x ^ 2 + ϱ') ^ 2 = x ^ 2 + ϱ' := Real.sq_sqrt hP'.le
    have hϱd : ϱ' - ϱ = (Real.sqrt (x ^ 2 + ϱ') - Real.sqrt (x ^ 2 + ϱ)) *
        (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ')) := by
      linear_combination hA2 - hB2
    rw [div_sub_div _ _ hA.ne' hB.ne', div_eq_div_iff (mul_pos hA hB).ne'
      (mul_pos (mul_pos hA hB) (add_pos hA hB)).ne', hϱd]
    ring
  have hden : 0 < Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') *
      (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ')) := by
    have hA : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
    have hB : 0 < Real.sqrt (x ^ 2 + ϱ') := Real.sqrt_pos.mpr hP'
    exact mul_pos (mul_pos hA hB) (add_pos hA hB)
  have hk : |x| / (Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') *
      (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ'))) ≤ 1 / (2 * ϱ₀) := by
    have hA : 0 < Real.sqrt (x ^ 2 + ϱ) := Real.sqrt_pos.mpr hP
    have hB : 0 < Real.sqrt (x ^ 2 + ϱ') := Real.sqrt_pos.mpr hP'
    have hB2 : Real.sqrt (x ^ 2 + ϱ') ^ 2 = x ^ 2 + ϱ' := Real.sq_sqrt hP'.le
    have hAB : ϱ₀ ≤ Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') := by
      nlinarith [mul_le_mul hA' hB' hrp.le hA.le]
    have hB2' : ϱ₀ ≤ Real.sqrt (x ^ 2 + ϱ') ^ 2 := by rw [hB2]; nlinarith [sq_nonneg x]
    have hBA : 2 * ϱ₀ ≤ Real.sqrt (x ^ 2 + ϱ') *
        (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ')) := by nlinarith
    rw [div_le_div_iff₀ hden (by linarith)]
    have h1 : |x| * (2 * ϱ₀) ≤ Real.sqrt (x ^ 2 + ϱ) * (2 * ϱ₀) :=
      mul_le_mul_of_nonneg_right hxA (by linarith)
    have h2 : Real.sqrt (x ^ 2 + ϱ) * (2 * ϱ₀) ≤
        Real.sqrt (x ^ 2 + ϱ) * (Real.sqrt (x ^ 2 + ϱ') *
          (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ'))) :=
      mul_le_mul_of_nonneg_left hBA hA.le
    nlinarith [h1, h2]
  rw [hid, abs_div, abs_mul, abs_of_pos hden, abs_sub_comm ϱ ϱ']
  calc |x| * |ϱ' - ϱ| / (Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') *
        (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ')))
      = (|x| / (Real.sqrt (x ^ 2 + ϱ) * Real.sqrt (x ^ 2 + ϱ') *
          (Real.sqrt (x ^ 2 + ϱ) + Real.sqrt (x ^ 2 + ϱ')))) * |ϱ' - ϱ| := by ring
    _ ≤ (1 / (2 * ϱ₀)) * |ϱ' - ϱ| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)
    _ = |ϱ' - ϱ| / (2 * ϱ₀) := by ring

/-- `lem:app-vol-sharp`, part (ii): the filter constants `‖ι_s‖_∞ = 1/(2√s)`, `Lip(ι_s) ≤ 1/s`,
`‖ω_ϱ‖_∞ = 1`, `Lip(ω_ϱ) ≤ ϱ^{-1/2}`, snapshot `cr-2026-10-23`. The filters are odd, bounded and
Lipschitz (conjuncts 1–2), so the Lipschitz bounds are not vacuous (review item 1). Declaration of record
`Muon.Volatility.lem_app_vol_sharp_ii`. The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Odd spectral functions]\label{lem:app-vol-sharp}
Let $f$ be odd, bounded and Lipschitz on $\R$, with $\norm f_\infty\defeq\sup_x\abs{f(x)}$
and Lipschitz constant $\operatorname{Lip}(f)$. For all $K,K'\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-vol-sharp-bounds}
\begin{gathered}
\norm{f^\sharp(K)}\le\norm f_\infty,\qquad
\norm{f^\sharp(K)}_\F\le\sqrt{\min(\Nout,\Nin)}\,\norm f_\infty,\\
\norm{f^\sharp(K)-f^\sharp(K')}_\F\le\operatorname{Lip}(f)\,\norm{K-K'}_\F .
\end{gathered}
\end{equation}
The filters \cref{eqn:app-vol-filters} satisfy
\begin{equation}\label{eqn:app-vol-filter-constants}
\norm{\iota_s}_\infty=\frac1{2\sqrt s},\quad \operatorname{Lip}(\iota_s)\le\frac1s,\qquad
\norm{\omega_\ridge}_\infty=1,\quad \operatorname{Lip}(\omega_\ridge)\le\ridge^{-1/2},
\end{equation}
and, for all $s,s'\ge s_\circ>0$ and $\ridge,\ridge'\ge\ridge_\circ>0$,
\begin{equation}\label{eqn:app-vol-filter-parameter}
\norm{\iota_s-\iota_{s'}}_\infty\le\frac{\abs{s-s'}}{s_\circ^{3/2}},\qquad
\norm{\omega_\ridge-\omega_{\ridge'}}_\infty\le\frac{\abs{\ridge-\ridge'}}{2\ridge_\circ} .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_sharp_ii {s ϱ : ℝ} (hs : 0 < s) (hϱ : 0 < ϱ) :
    IsOddBddLip (iotaF s) ∧ IsOddBddLip (omegaF ϱ) ∧
    supNorm (iotaF s) = 1 / (2 * Real.sqrt s) ∧ lipConst (iotaF s) ≤ 1 / s ∧
    supNorm (omegaF ϱ) = 1 ∧ lipConst (omegaF ϱ) ≤ 1 / Real.sqrt ϱ := by
  refine ⟨iota_odd_bdd_lip_P2 hs, omega_odd_bdd_lip_P2 hϱ, supNorm_iota_P2 hs,
    lipConst_le_P2 _ _ (one_div_pos.mpr hs).le (iota_lip_P2 hs), supNorm_omega_P2 hϱ,
    lipConst_le_P2 _ _ (one_div_pos.mpr (Real.sqrt_pos.mpr hϱ)).le (omega_lip_P2 hϱ)⟩

/-- `lem:app-vol-sharp`, part (iii): the parameter bounds
`‖ι_s − ι_{s'}‖_∞ ≤ |s − s'| / s∘^{3/2}` and `‖ω_ϱ − ω_{ϱ'}‖_∞ ≤ |ϱ − ϱ'| / (2 ϱ∘)` for
`s, s' ≥ s∘ > 0` and `ϱ, ϱ' ≥ ϱ∘ > 0`, snapshot `cr-2026-10-23`. Declaration of record
`Muon.Volatility.lem_app_vol_sharp_iii`. The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Odd spectral functions]\label{lem:app-vol-sharp}
Let $f$ be odd, bounded and Lipschitz on $\R$, with $\norm f_\infty\defeq\sup_x\abs{f(x)}$
and Lipschitz constant $\operatorname{Lip}(f)$. For all $K,K'\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-vol-sharp-bounds}
\begin{gathered}
\norm{f^\sharp(K)}\le\norm f_\infty,\qquad
\norm{f^\sharp(K)}_\F\le\sqrt{\min(\Nout,\Nin)}\,\norm f_\infty,\\
\norm{f^\sharp(K)-f^\sharp(K')}_\F\le\operatorname{Lip}(f)\,\norm{K-K'}_\F .
\end{gathered}
\end{equation}
The filters \cref{eqn:app-vol-filters} satisfy
\begin{equation}\label{eqn:app-vol-filter-constants}
\norm{\iota_s}_\infty=\frac1{2\sqrt s},\quad \operatorname{Lip}(\iota_s)\le\frac1s,\qquad
\norm{\omega_\ridge}_\infty=1,\quad \operatorname{Lip}(\omega_\ridge)\le\ridge^{-1/2},
\end{equation}
and, for all $s,s'\ge s_\circ>0$ and $\ridge,\ridge'\ge\ridge_\circ>0$,
\begin{equation}\label{eqn:app-vol-filter-parameter}
\norm{\iota_s-\iota_{s'}}_\infty\le\frac{\abs{s-s'}}{s_\circ^{3/2}},\qquad
\norm{\omega_\ridge-\omega_{\ridge'}}_\infty\le\frac{\abs{\ridge-\ridge'}}{2\ridge_\circ} .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_sharp_iii {s s' ϱ ϱ' s₀ ϱ₀ : ℝ} (hs₀ : 0 < s₀) (hϱ₀ : 0 < ϱ₀)
    (hs : s₀ ≤ s) (hs' : s₀ ≤ s') (hϱ : ϱ₀ ≤ ϱ) (hϱ' : ϱ₀ ≤ ϱ') :
    supNorm (fun x => iotaF s x - iotaF s' x) ≤ |s - s'| / s₀ ^ ((3 : ℝ) / 2) ∧
    supNorm (fun x => omegaF ϱ x - omegaF ϱ' x) ≤ |ϱ - ϱ'| / (2 * ϱ₀) := by
  have hpow : s₀ ^ ((3 : ℝ) / 2) = s₀ * Real.sqrt s₀ := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hs₀, Real.rpow_one,
      Real.sqrt_eq_rpow]
  refine ⟨?_, ?_⟩
  · rw [hpow]
    unfold supNorm
    exact ciSup_le fun x => iota_param_P2 hs₀ hs hs' x
  · unfold supNorm
    exact ciSup_le fun x => omega_param_P2 hϱ₀ hϱ hϱ' x

/-! ## Helpers for `lem:app-vol-finite` (norm products, trace duality, scalar coefficient) -/

private lemma fro_transpose_P4 {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma opNorm_transpose_P4 {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma opNorm_nonneg_P4 {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma fro_sq_P4 {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-- Operator-on-the-left Frobenius bound `‖MN‖_F ≤ ‖M‖ ‖N‖_F`, column by column. -/
private lemma fro_mul_le_left_P4 {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [fro_sq_P4, mul_pow, fro_sq_P4, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (fro_nn_aux _) (mul_nonneg (opNorm_nonneg_P4 M) (fro_nn_aux N))
    two_ne_zero).mp hfro

private lemma fro_mul_le_right_P4 {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := fro_mul_le_left_P4 Nᵀ Mᵀ
  rw [opNorm_transpose_P4, fro_transpose_P4, ← Matrix.transpose_mul, fro_transpose_P4] at h
  linarith [mul_comm (opNorm N) (fro M)]

/-- Sandwich bound `‖F D G‖_F ≤ ‖D‖_F` for contractions `F`, `G`. -/
private lemma fro_sandwich_P4 {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) : fro (F * D * G) ≤ fro D := by
  have h1 : opNorm F * fro D ≤ fro D := mul_le_of_le_one_left (fro_nn_aux D) hF
  calc fro (F * D * G) ≤ fro (F * D) * opNorm G := fro_mul_le_right_P4 _ _
    _ ≤ (opNorm F * fro D) * opNorm G :=
        mul_le_mul_of_nonneg_right (fro_mul_le_left_P4 _ _) (opNorm_nonneg_P4 _)
    _ ≤ fro D * 1 := mul_le_mul h1 hG (opNorm_nonneg_P4 G) (fro_nn_aux D)
    _ = fro D := mul_one _

/-- Trace duality for the Frobenius pairing: `|Tr(X Cᵀ)| ≤ ‖X‖_F ‖C‖_F`. -/
private lemma trace_mul_transpose_le_P4 {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [fro_sq_P4, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [fro_sq_P4, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (fro_nn_aux X) (fro_nn_aux C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

private lemma supNorm_nonneg_P4 (f : ℝ → ℝ) (hf : IsOddBddLip f) : 0 ≤ supNorm f := by
  obtain ⟨_, ⟨B, hB⟩, _⟩ := hf
  have hbdd : BddAbove (Set.range fun x : ℝ => |f x|) := ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  have hle : ∀ x, |f x| ≤ supNorm f := fun x => le_ciSup hbdd x
  exact (abs_nonneg _).trans (hle 0)

/-- The scalar comparison `B⁻¹ √k ≤ √(γ/B)` when `k ≤ γ B`. -/
private lemma coef_P4 (B k : ℕ) (hB : 0 < B) (γ : ℝ) (hdim : (k : ℝ) ≤ γ * B) :
    (B : ℝ)⁻¹ * Real.sqrt (k : ℝ) ≤ Real.sqrt (γ / B) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc (B : ℝ)⁻¹ * Real.sqrt (k : ℝ) = Real.sqrt (((B : ℝ)⁻¹ * Real.sqrt (k : ℝ)) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt (γ / B) := by
        apply Real.sqrt_le_sqrt
        rw [mul_pow, Real.sq_sqrt hk, inv_pow, ← div_eq_inv_mul, div_le_div_iff₀ (by positivity) hBpos]
        nlinarith [hdim, hBpos]

/-! ## Helpers for `lem_app_vol_finite_iii` and `lem_app_vol_finite_iv` (P-D.1.P5) -/

private lemma cont_of_isOddBddLip_P5 (f : ℝ → ℝ) (hf : IsOddBddLip f) : Continuous f := by
  obtain ⟨hnn, hlip⟩ := lipConst_bound_aux f hf
  have hLW : LipschitzWith (Real.toNNReal (lipConst f)) f := by
    refine LipschitzWith.of_dist_le' (fun x y => ?_)
    simp only [Real.dist_eq, Real.coe_toNNReal _ hnn]
    exact hlip x y
  exact hLW.continuous

private lemma isOddBddLip_sub_P5 (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    IsOddBddLip (fun x => f x - g x) := by
  obtain ⟨hfo, ⟨M1, hM1⟩, ⟨L1, hL1⟩⟩ := hf
  obtain ⟨hgo, ⟨M2, hM2⟩, ⟨L2, hL2⟩⟩ := hg
  refine ⟨fun x => ?_, ⟨M1 + M2, fun x => ?_⟩, ⟨L1 + L2, fun x y => ?_⟩⟩
  · show f (-x) - g (-x) = -(f x - g x)
    rw [hfo x, hgo x]; ring
  · have h1 := abs_le.mp (hM1 x)
    have h2 := abs_le.mp (hM2 x)
    show |f x - g x| ≤ M1 + M2
    rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  · have h1 := abs_le.mp (hL1 x y)
    have h2 := abs_le.mp (hL2 x y)
    have e : (L1 + L2) * |x - y| = L1 * |x - y| + L2 * |x - y| := by ring
    show |(f x - g x) - (f y - g y)| ≤ (L1 + L2) * |x - y|
    rw [e, abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

private lemma oddSharp_sub_fun_P5 {m n : ℕ} (f g : ℝ → ℝ) (hf : IsOddBddLip f)
    (hg : IsOddBddLip g) (K : Mat m n) :
    oddSharp (fun x => f x - g x) K = oddSharp f K - oddSharp g K := by
  unfold oddSharp
  rw [cfc_sub f g (hermDilation K) (cont_of_isOddBddLip_P5 f hf).continuousOn
    (cont_of_isOddBddLip_P5 g hg).continuousOn, upperRight_sub_aux]

private lemma opNorm_mul_P5 {k l p : ℕ} (A : Mat k l) (B : Mat l p) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

/-- Trace bound with the nuclear norm on the second factor `D`: `|Tr(F D G Cᵀ)| ≤ ‖C‖ ‖D‖_*`. -/
private lemma trace_left_nuc_P5 {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (C : Mat m n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) :
    |Matrix.trace (F * D * G * Cᵀ)| ≤ opNorm C * nuc D := by
  have hop : opNorm (G * Cᵀ * F) ≤ opNorm C := by
    calc opNorm (G * Cᵀ * F) ≤ opNorm (G * Cᵀ) * opNorm F := opNorm_mul_P5 _ _
      _ ≤ (opNorm G * opNorm Cᵀ) * opNorm F :=
          mul_le_mul_of_nonneg_right (opNorm_mul_P5 _ _) (opNorm_nonneg_P4 _)
      _ ≤ (1 * opNorm Cᵀ) * 1 :=
          mul_le_mul (mul_le_mul hG le_rfl (opNorm_nonneg_P4 _) zero_le_one) hF
            (opNorm_nonneg_P4 _) (mul_nonneg zero_le_one (opNorm_nonneg_P4 _))
      _ = opNorm C := by rw [opNorm_transpose_P4]; ring
  have htr : Matrix.trace (F * D * G * Cᵀ) = Matrix.trace ((G * Cᵀ * F) * D) := by
    calc Matrix.trace (F * D * G * Cᵀ) = Matrix.trace (F * (D * (G * Cᵀ))) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((D * (G * Cᵀ)) * F) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (D * (G * Cᵀ * F)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((G * Cᵀ * F) * D) := Matrix.trace_mul_comm _ _
  rw [htr]
  exact (trace_mul_le_opNorm_mul_nuc (G * Cᵀ * F) D).trans
    (mul_le_mul_of_nonneg_right hop (nuc_nonneg D))

/-- Trace bound with the nuclear norm on the second matrix `C`: `|Tr(F D G Cᵀ)| ≤ ‖D‖ ‖C‖_*`. -/
private lemma trace_right_nuc_P5 {m n : ℕ} (F : Mat m m) (D : Mat m n) (G : Mat n n)
    (C : Mat m n) (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1) :
    |Matrix.trace (F * D * G * Cᵀ)| ≤ opNorm D * nuc C := by
  have hop : opNorm (F * D * G) ≤ opNorm D := by
    calc opNorm (F * D * G) ≤ opNorm (F * D) * opNorm G := opNorm_mul_P5 _ _
      _ ≤ (opNorm F * opNorm D) * opNorm G :=
          mul_le_mul_of_nonneg_right (opNorm_mul_P5 _ _) (opNorm_nonneg_P4 _)
      _ ≤ (1 * opNorm D) * 1 :=
          mul_le_mul (mul_le_mul hF le_rfl (opNorm_nonneg_P4 _) zero_le_one) hG
            (opNorm_nonneg_P4 _) (mul_nonneg zero_le_one (opNorm_nonneg_P4 _))
      _ = opNorm D := by ring
  have h := trace_mul_le_opNorm_mul_nuc (F * D * G) Cᵀ
  rw [nuc_transpose] at h
  exact h.trans (mul_le_mul_of_nonneg_right hop (nuc_nonneg C))

/-- Algebra of the mixed resolvent difference, with `R = R_s(K)`, `R' = R_s(K')`, `T' = R̃_s(K')`. -/
private lemma xs_alg_P5 {m n : ℕ} (K K' : Mat m n) (s : ℝ) (R R' : Mat m m) (T' : Mat n n)
    (hRA : R * (K * Kᵀ + s • (1 : Mat m m)) = 1)
    (hcA' : (K' * K'ᵀ + s • (1 : Mat m m)) * R' = 1)
    (hJ : K'ᵀ * R' * K' = (1 : Mat n n) - s • T') :
    R * K - R' * K' = (-s) • (R * (K' - K) * T') + R * K * (K' - K)ᵀ * (R' * K') := by
  have e1 : R * (K' * K'ᵀ + s • (1 : Mat m m)) * R' = R := by
    rw [Matrix.mul_assoc, hcA', Matrix.mul_one]
  have e2 : R * (K * Kᵀ + s • (1 : Mat m m)) * R' = R' := by
    rw [hRA, Matrix.one_mul]
  have e3 : R * (K' * K'ᵀ - K * Kᵀ) * R' =
      R * (K' * K'ᵀ + s • (1 : Mat m m)) * R' - R * (K * Kᵀ + s • (1 : Mat m m)) * R' := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul]
    abel
  have hdiff : R - R' = R * (K' * K'ᵀ - K * Kᵀ) * R' := by
    rw [e3, e1, e2]
  have eA : K' * K'ᵀ - K * Kᵀ = (K' - K) * K'ᵀ + K * (K' - K)ᵀ := by
    rw [Matrix.transpose_sub]
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hX : R * K - R' * K' = R * (K - K') + (R - R') * K' := by
    rw [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hY : (R - R') * K' = R * (K' - K) * (K'ᵀ * R' * K') + R * K * (K' - K)ᵀ * (R' * K') := by
    rw [hdiff, eA]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hW : R * (K' - K) * ((1 : Mat n n) - s • T') = R * (K' - K) - s • (R * (K' - K) * T') := by
    simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul]
  have hZ2 : R * (K - K') = -(R * (K' - K)) := by
    rw [← Matrix.mul_neg, neg_sub]
  rw [hX, hY, hJ, hW, neg_smul, hZ2]
  abel

/-- Nuclear Lipschitz bound for `𝖷_s`: `‖𝖷_s(K) − 𝖷_s(K')‖_* ≤ (2/s) ‖K − K'‖_*`. -/
private lemma xs_nuc_lip_P5 {m n : ℕ} (K K' : Mat m n) {s : ℝ} (hs : 0 < s) :
    nuc (Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s) ≤ 2 / s * nuc (K - K') := by
  obtain ⟨hR, hT, hXop, _, _, hI6, _⟩ := Muon.DetEquiv.lem_app_de_resolvent K s hs
  obtain ⟨hR', hT', hXop', _, hJ5, hJ6, _⟩ := Muon.DetEquiv.lem_app_de_resolvent K' s hs
  have hRA : Muon.DetEquiv.Rs K s * (K * Kᵀ + s • (1 : Mat m m)) = 1 := by
    rw [Matrix.mul_add, hI6, Matrix.mul_smul, Matrix.mul_one, sub_add_cancel]
  have hRA' : Muon.DetEquiv.Rs K' s * (K' * K'ᵀ + s • (1 : Mat m m)) = 1 := by
    rw [Matrix.mul_add, hJ6, Matrix.mul_smul, Matrix.mul_one, sub_add_cancel]
  have hcA' : (K' * K'ᵀ + s • (1 : Mat m m)) * Muon.DetEquiv.Rs K' s = 1 :=
    mul_eq_one_comm.mp hRA'
  have key := xs_alg_P5 K K' s (Muon.DetEquiv.Rs K s) (Muon.DetEquiv.Rs K' s)
    (Muon.DetEquiv.Rts K' s) hRA hcA' hJ5
  have hXid : Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s =
      (-s) • (Muon.DetEquiv.Rs K s * (K' - K) * Muon.DetEquiv.Rts K' s) +
        Muon.DetEquiv.Rs K s * K * (K' - K)ᵀ * (Muon.DetEquiv.Rs K' s * K') := key
  have hneg : nuc (K' - K) = nuc (K - K') := by
    have h : K' - K = (-1 : ℝ) • (K - K') := by rw [neg_one_smul, neg_sub]
    rw [h, nuc_smul]; simp
  have hY : nuc (Muon.DetEquiv.Rs K s * (K' - K) * Muon.DetEquiv.Rts K' s) ≤
      1 / s * nuc (K' - K) * (1 / s) :=
    le_trans (nuc_mul_three_le _ _ _)
      (mul_le_mul (mul_le_mul_of_nonneg_right hR (nuc_nonneg _)) hT' (opNorm_nonneg_P4 _)
        (mul_nonneg (one_div_pos.mpr hs).le (nuc_nonneg _)))
  have hb1 : nuc ((-s) • (Muon.DetEquiv.Rs K s * (K' - K) * Muon.DetEquiv.Rts K' s)) ≤
      nuc (K - K') / s := by
    rw [nuc_smul, abs_neg, abs_of_pos hs]
    calc s * nuc (Muon.DetEquiv.Rs K s * (K' - K) * Muon.DetEquiv.Rts K' s)
        ≤ s * (1 / s * nuc (K' - K) * (1 / s)) := mul_le_mul_of_nonneg_left hY hs.le
      _ = nuc (K - K') / s := by rw [hneg]; field_simp
  have hb2 : nuc (Muon.DetEquiv.Rs K s * K * (K' - K)ᵀ * (Muon.DetEquiv.Rs K' s * K')) ≤
      1 / (2 * Real.sqrt s) * nuc (K' - K)ᵀ * (1 / (2 * Real.sqrt s)) :=
    le_trans (nuc_mul_three_le _ _ _)
      (mul_le_mul (mul_le_mul_of_nonneg_right hXop (nuc_nonneg _)) hXop' (opNorm_nonneg_P4 _)
        (mul_nonneg (by positivity) (nuc_nonneg _)))
  have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  have hq : 1 / (2 * Real.sqrt s) * nuc (K' - K)ᵀ * (1 / (2 * Real.sqrt s)) =
      nuc (K - K') / (4 * s) := by
    rw [nuc_transpose, hneg, show 1 / (2 * Real.sqrt s) * nuc (K - K') * (1 / (2 * Real.sqrt s))
      = nuc (K - K') * (1 / ((2 * Real.sqrt s) * (2 * Real.sqrt s))) by ring,
      show (2 * Real.sqrt s) * (2 * Real.sqrt s) = 4 * s by linear_combination 4 * hsq]
    ring
  have hN : 0 ≤ nuc (K - K') := nuc_nonneg _
  rw [hXid]
  refine (nuc_add_le _ _).trans ?_
  refine (add_le_add hb1 (hb2.trans (le_of_eq hq))).trans ?_
  have e1 : nuc (K - K') / (4 * s) = 1 / 4 * (nuc (K - K') / s) := by ring
  have e2 : 2 / s * nuc (K - K') = 2 * (nuc (K - K') / s) := by ring
  rw [e1, e2]
  have hNs : 0 ≤ nuc (K - K') / s := div_nonneg hN hs.le
  linarith

/-! ## Tested contractions: statements -/

/-- `lem:app-vol-finite`, part (i): `|𝒦^{F,G}[f₁,f₂](K,H)| ≤ γ⋆ ‖f₁‖_∞ ‖f₂‖_∞`, snapshot
`cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_finite_i`. Hypotheses:
`hdim` is the hidden assumption `min(N_out,N_in) ≤ γ⋆ B` (`section.tex` l.290; card R16); `hB` is
the standing `B > 0`. The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Finite bounds for tested contractions]\label{lem:app-vol-finite}
Let $\norm F,\norm G\le1$, let $f_1,f_2$ be odd, bounded and Lipschitz, and
let $K,K',H,H'\in\R^{\Nout\times\Nin}$. Then
\begin{align}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)}&\le\gamma_\star\norm{f_1}_\infty\norm{f_2}_\infty ,\label{eqn:app-vol-finite-sup}\\
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1,f_2](K',H')}
&\le\sqrt{\frac{\gamma_\star}{B}}\Big(\operatorname{Lip}(f_1)\norm{f_2}_\infty\norm{K-K'}_\F\notag\\
&\qquad\qquad+\norm{f_1}_\infty\operatorname{Lip}(f_2)\norm{H-H'}_\F\Big),\label{eqn:app-vol-finite-lip}
\end{align}
and the bilinear dependence on the filters gives
\begin{equation}\label{eqn:app-vol-finite-filters}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1',f_2'](K,H)}
\le\gamma_\star\big(\norm{f_1-f_1'}_\infty\norm{f_2}_\infty+\norm{f_1'}_\infty\norm{f_2-f_2'}_\infty\big).
\end{equation}
For the resolvent filters, with $s,u\ge s_\circ>0$,
\begin{equation}\label{eqn:app-vol-finite-nuclear}
\abs{\mathcal K^{F,G}_{s,u}(K,K)-\mathcal K^{F,G}_{s,u}(K',K')}\le\frac{2}{B\,s_\circ^{3/2}}\norm{K-K'}_* .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_finite_i {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂) (K H : Mat m n) :
    |contraction B F G f₁ f₂ K H| ≤ γstar * supNorm f₁ * supNorm f₂ := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBi : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hBpos.le
  have hS1 := supNorm_nonneg_P4 f₁ hf₁
  have hS2 := supNorm_nonneg_P4 f₂ hf₂
  have hA := (sharp_op_fro_aux_P1 f₁ hf₁ K).2
  have hC := (sharp_op_fro_aux_P1 f₂ hf₂ H).2
  have hT : |Matrix.trace (F * oddSharp f₁ K * G * (oddSharp f₂ H)ᵀ)| ≤
      fro (oddSharp f₁ K) * fro (oddSharp f₂ H) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul_of_nonneg_right (fro_sandwich_P4 F _ G hF hG) (fro_nn_aux _))
  have hprod : fro (oddSharp f₁ K) * fro (oddSharp f₂ H) ≤
      ((min m n : ℕ) : ℝ) * supNorm f₁ * supNorm f₂ := by
    calc fro (oddSharp f₁ K) * fro (oddSharp f₂ H)
        ≤ (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁) *
            (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) :=
          mul_le_mul hA hC (fro_nn_aux _) (mul_nonneg (Real.sqrt_nonneg _) hS1)
      _ = (Real.sqrt ((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ)) *
            supNorm f₁ * supNorm f₂ := by ring
      _ = ((min m n : ℕ) : ℝ) * supNorm f₁ * supNorm f₂ := by
          rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have hk2 : ((min m n : ℕ) : ℝ) * supNorm f₁ * supNorm f₂ ≤ γstar * B * supNorm f₁ * supNorm f₂ := by
    calc ((min m n : ℕ) : ℝ) * supNorm f₁ * supNorm f₂
        = ((min m n : ℕ) : ℝ) * (supNorm f₁ * supNorm f₂) := by ring
      _ ≤ γstar * B * (supNorm f₁ * supNorm f₂) :=
          mul_le_mul_of_nonneg_right hdim (mul_nonneg hS1 hS2)
      _ = γstar * B * supNorm f₁ * supNorm f₂ := by ring
  unfold contraction
  rw [abs_mul, abs_of_nonneg hBi]
  calc (B : ℝ)⁻¹ * |Matrix.trace (F * oddSharp f₁ K * G * (oddSharp f₂ H)ᵀ)|
      ≤ (B : ℝ)⁻¹ * (γstar * B * supNorm f₁ * supNorm f₂) :=
        mul_le_mul_of_nonneg_left (hT.trans (hprod.trans hk2)) hBi
    _ = γstar * supNorm f₁ * supNorm f₂ := by field_simp

/-- `lem:app-vol-finite`, part (ii): the Lipschitz bound in the two matrix arguments with constant
`√(γ⋆/B)`, snapshot `cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_finite_ii`.
Hypotheses as in part (i). The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Finite bounds for tested contractions]\label{lem:app-vol-finite}
Let $\norm F,\norm G\le1$, let $f_1,f_2$ be odd, bounded and Lipschitz, and
let $K,K',H,H'\in\R^{\Nout\times\Nin}$. Then
\begin{align}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)}&\le\gamma_\star\norm{f_1}_\infty\norm{f_2}_\infty ,\label{eqn:app-vol-finite-sup}\\
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1,f_2](K',H')}
&\le\sqrt{\frac{\gamma_\star}{B}}\Big(\operatorname{Lip}(f_1)\norm{f_2}_\infty\norm{K-K'}_\F\notag\\
&\qquad\qquad+\norm{f_1}_\infty\operatorname{Lip}(f_2)\norm{H-H'}_\F\Big),\label{eqn:app-vol-finite-lip}
\end{align}
and the bilinear dependence on the filters gives
\begin{equation}\label{eqn:app-vol-finite-filters}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1',f_2'](K,H)}
\le\gamma_\star\big(\norm{f_1-f_1'}_\infty\norm{f_2}_\infty+\norm{f_1'}_\infty\norm{f_2-f_2'}_\infty\big).
\end{equation}
For the resolvent filters, with $s,u\ge s_\circ>0$,
\begin{equation}\label{eqn:app-vol-finite-nuclear}
\abs{\mathcal K^{F,G}_{s,u}(K,K)-\mathcal K^{F,G}_{s,u}(K',K')}\le\frac{2}{B\,s_\circ^{3/2}}\norm{K-K'}_* .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_finite_ii {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f₁ f₂ : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂)
    (K K' H H' : Mat m n) :
    |contraction B F G f₁ f₂ K H - contraction B F G f₁ f₂ K' H'| ≤
      Real.sqrt (γstar / B) *
        (lipConst f₁ * supNorm f₂ * fro (K - K') +
          supNorm f₁ * lipConst f₂ * fro (H - H')) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBi : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hBpos.le
  have hS1 := supNorm_nonneg_P4 f₁ hf₁
  have hS2 := supNorm_nonneg_P4 f₂ hf₂
  have hL1 := (lipConst_bound_aux f₁ hf₁).1
  have hL2 := (lipConst_bound_aux f₂ hf₂).1
  have hA := (sharp_op_fro_aux_P1 f₁ hf₁ K).2
  have hA' := (sharp_op_fro_aux_P1 f₁ hf₁ K').2
  have hC := (sharp_op_fro_aux_P1 f₂ hf₂ H).2
  have hdA := (lem_app_vol_sharp_i f₁ hf₁ K K').2.2
  have hdC := (lem_app_vol_sharp_i f₂ hf₂ H H').2.2
  have hcoef := coef_P4 B (min m n) hB γstar hdim
  have hmat : F * oddSharp f₁ K * G * (oddSharp f₂ H)ᵀ
      - F * oddSharp f₁ K' * G * (oddSharp f₂ H')ᵀ
      = F * (oddSharp f₁ K - oddSharp f₁ K') * G * (oddSharp f₂ H)ᵀ
        + F * oddSharp f₁ K' * G * (oddSharp f₂ H - oddSharp f₂ H')ᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub]
    abel
  have key : contraction B F G f₁ f₂ K H - contraction B F G f₁ f₂ K' H' =
      (B : ℝ)⁻¹ * (Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁ K') * G * (oddSharp f₂ H)ᵀ)
        + Matrix.trace (F * oddSharp f₁ K' * G * (oddSharp f₂ H - oddSharp f₂ H')ᵀ)) := by
    unfold contraction
    rw [← mul_sub, ← Matrix.trace_sub, hmat, Matrix.trace_add]
  have ht1 : |Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁ K') * G * (oddSharp f₂ H)ᵀ)| ≤
      (lipConst f₁ * fro (K - K')) * (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hdA) hC (fro_nn_aux _)
        (mul_nonneg hL1 (fro_nn_aux _)))
  have ht2 : |Matrix.trace (F * oddSharp f₁ K' * G * (oddSharp f₂ H - oddSharp f₂ H')ᵀ)| ≤
      (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁) * (lipConst f₂ * fro (H - H')) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hA') hdC (fro_nn_aux _)
        (mul_nonneg (Real.sqrt_nonneg _) hS1))
  have hnn : 0 ≤ lipConst f₁ * supNorm f₂ * fro (K - K') +
      supNorm f₁ * lipConst f₂ * fro (H - H') :=
    add_nonneg (mul_nonneg (mul_nonneg hL1 hS2) (fro_nn_aux _))
      (mul_nonneg (mul_nonneg hS1 hL2) (fro_nn_aux _))
  rw [key, abs_mul, abs_of_nonneg hBi]
  calc (B : ℝ)⁻¹ * |Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁ K') * G * (oddSharp f₂ H)ᵀ)
        + Matrix.trace (F * oddSharp f₁ K' * G * (oddSharp f₂ H - oddSharp f₂ H')ᵀ)|
      ≤ (B : ℝ)⁻¹ * ((lipConst f₁ * fro (K - K')) * (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂)
          + (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁) * (lipConst f₂ * fro (H - H'))) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ht1 ht2)) hBi
    _ = ((B : ℝ)⁻¹ * Real.sqrt ((min m n : ℕ) : ℝ)) *
          (lipConst f₁ * supNorm f₂ * fro (K - K') + supNorm f₁ * lipConst f₂ * fro (H - H')) := by
        ring
    _ ≤ Real.sqrt (γstar / B) *
          (lipConst f₁ * supNorm f₂ * fro (K - K') + supNorm f₁ * lipConst f₂ * fro (H - H')) :=
        mul_le_mul_of_nonneg_right hcoef hnn

/-- `lem:app-vol-finite`, part (iii): the bilinear dependence on the filters,
`|𝒦[f₁,f₂] − 𝒦[f₁',f₂']| ≤ γ⋆(‖f₁ − f₁'‖_∞ ‖f₂‖_∞ + ‖f₁'‖_∞ ‖f₂ − f₂'‖_∞)`, snapshot
`cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_finite_iii`. The primed filters
are in the same class (the source states the bound for "odd bounded and Lipschitz" filters).
The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Finite bounds for tested contractions]\label{lem:app-vol-finite}
Let $\norm F,\norm G\le1$, let $f_1,f_2$ be odd, bounded and Lipschitz, and
let $K,K',H,H'\in\R^{\Nout\times\Nin}$. Then
\begin{align}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)}&\le\gamma_\star\norm{f_1}_\infty\norm{f_2}_\infty ,\label{eqn:app-vol-finite-sup}\\
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1,f_2](K',H')}
&\le\sqrt{\frac{\gamma_\star}{B}}\Big(\operatorname{Lip}(f_1)\norm{f_2}_\infty\norm{K-K'}_\F\notag\\
&\qquad\qquad+\norm{f_1}_\infty\operatorname{Lip}(f_2)\norm{H-H'}_\F\Big),\label{eqn:app-vol-finite-lip}
\end{align}
and the bilinear dependence on the filters gives
\begin{equation}\label{eqn:app-vol-finite-filters}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1',f_2'](K,H)}
\le\gamma_\star\big(\norm{f_1-f_1'}_\infty\norm{f_2}_\infty+\norm{f_1'}_\infty\norm{f_2-f_2'}_\infty\big).
\end{equation}
For the resolvent filters, with $s,u\ge s_\circ>0$,
\begin{equation}\label{eqn:app-vol-finite-nuclear}
\abs{\mathcal K^{F,G}_{s,u}(K,K)-\mathcal K^{F,G}_{s,u}(K',K')}\le\frac{2}{B\,s_\circ^{3/2}}\norm{K-K'}_* .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_finite_iii {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f₁ f₂ f₁' f₂' : ℝ → ℝ) (hf₁ : IsOddBddLip f₁) (hf₂ : IsOddBddLip f₂)
    (hf₁' : IsOddBddLip f₁') (hf₂' : IsOddBddLip f₂') (K H : Mat m n) :
    |contraction B F G f₁ f₂ K H - contraction B F G f₁' f₂' K H| ≤
      γstar * (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x)) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (B : ℝ) ≠ 0 := hBpos.ne'
  have hBi : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hBpos.le
  have hg1 := isOddBddLip_sub_P5 f₁ f₁' hf₁ hf₁'
  have hg2 := isOddBddLip_sub_P5 f₂ f₂' hf₂ hf₂'
  have hS1 := supNorm_nonneg_P4 _ hg1
  have hS2 := supNorm_nonneg_P4 f₂ hf₂
  have hS3 := supNorm_nonneg_P4 f₁' hf₁'
  have hS4 := supNorm_nonneg_P4 _ hg2
  have hA := (sharp_op_fro_aux_P1 _ hg1 K).2
  rw [oddSharp_sub_fun_P5 f₁ f₁' hf₁ hf₁' K] at hA
  have hC := (sharp_op_fro_aux_P1 f₂ hf₂ H).2
  have hC' := (sharp_op_fro_aux_P1 _ hg2 H).2
  rw [oddSharp_sub_fun_P5 f₂ f₂' hf₂ hf₂' H] at hC'
  have hA' := (sharp_op_fro_aux_P1 f₁' hf₁' K).2
  have hmat : F * oddSharp f₁ K * G * (oddSharp f₂ H)ᵀ
      - F * oddSharp f₁' K * G * (oddSharp f₂' H)ᵀ
      = F * (oddSharp f₁ K - oddSharp f₁' K) * G * (oddSharp f₂ H)ᵀ
        + F * oddSharp f₁' K * G * (oddSharp f₂ H - oddSharp f₂' H)ᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub]
    abel
  have ht1 : |Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁' K) * G * (oddSharp f₂ H)ᵀ)| ≤
      (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₁ x - f₁' x)) *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hA) hC (fro_nn_aux _)
        (mul_nonneg (Real.sqrt_nonneg _) hS1))
  have ht2 : |Matrix.trace (F * oddSharp f₁' K * G * (oddSharp f₂ H - oddSharp f₂' H)ᵀ)| ≤
      (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁') *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₂ x - f₂' x)) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hA') hC' (fro_nn_aux _)
        (mul_nonneg (Real.sqrt_nonneg _) hS3))
  have hsq : Real.sqrt ((min m n : ℕ) : ℝ) * Real.sqrt ((min m n : ℕ) : ℝ) = ((min m n : ℕ) : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hX : 0 ≤ supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
      supNorm f₁' * supNorm (fun x => f₂ x - f₂' x) :=
    add_nonneg (mul_nonneg hS1 hS2) (mul_nonneg hS3 hS4)
  have hsum : (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₁ x - f₁' x)) *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) +
      (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁') *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₂ x - f₂' x)) =
      ((min m n : ℕ) : ℝ) * (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x)) := by
    linear_combination (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x)) * hsq
  have key : contraction B F G f₁ f₂ K H - contraction B F G f₁' f₂' K H =
      (B : ℝ)⁻¹ * (Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁' K) * G * (oddSharp f₂ H)ᵀ)
        + Matrix.trace (F * oddSharp f₁' K * G * (oddSharp f₂ H - oddSharp f₂' H)ᵀ)) := by
    unfold contraction
    rw [← mul_sub, ← Matrix.trace_sub, hmat, Matrix.trace_add]
  rw [key, abs_mul, abs_of_nonneg hBi]
  calc (B : ℝ)⁻¹ * |Matrix.trace (F * (oddSharp f₁ K - oddSharp f₁' K) * G * (oddSharp f₂ H)ᵀ)
        + Matrix.trace (F * oddSharp f₁' K * G * (oddSharp f₂ H - oddSharp f₂' H)ᵀ)|
      ≤ (B : ℝ)⁻¹ * ((Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₁ x - f₁' x)) *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₂) +
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm f₁') *
        (Real.sqrt ((min m n : ℕ) : ℝ) * supNorm (fun x => f₂ x - f₂' x))) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ht1 ht2)) hBi
    _ = (B : ℝ)⁻¹ * (((min m n : ℕ) : ℝ) * (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x))) := by rw [hsum]
    _ ≤ (B : ℝ)⁻¹ * (γstar * B * (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdim hX) hBi
    _ = γstar * (supNorm (fun x => f₁ x - f₁' x) * supNorm f₂ +
        supNorm f₁' * supNorm (fun x => f₂ x - f₂' x)) := by field_simp

/-- `lem:app-vol-finite`, part (iv): the nuclear-norm bound for the resolvent filters,
`|𝒦_{s,u}(K,K) − 𝒦_{s,u}(K',K')| ≤ 2/(B s∘^{3/2}) ‖K − K'‖_*` for `s, u ≥ s∘ > 0`, snapshot
`cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_finite_iv`. The full environment,
verbatim from `section.tex`:
```latex
\begin{lemma}[Finite bounds for tested contractions]\label{lem:app-vol-finite}
Let $\norm F,\norm G\le1$, let $f_1,f_2$ be odd, bounded and Lipschitz, and
let $K,K',H,H'\in\R^{\Nout\times\Nin}$. Then
\begin{align}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)}&\le\gamma_\star\norm{f_1}_\infty\norm{f_2}_\infty ,\label{eqn:app-vol-finite-sup}\\
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1,f_2](K',H')}
&\le\sqrt{\frac{\gamma_\star}{B}}\Big(\operatorname{Lip}(f_1)\norm{f_2}_\infty\norm{K-K'}_\F\notag\\
&\qquad\qquad+\norm{f_1}_\infty\operatorname{Lip}(f_2)\norm{H-H'}_\F\Big),\label{eqn:app-vol-finite-lip}
\end{align}
and the bilinear dependence on the filters gives
\begin{equation}\label{eqn:app-vol-finite-filters}
\abs{\mathcal K^{F,G}[f_1,f_2](K,H)-\mathcal K^{F,G}[f_1',f_2'](K,H)}
\le\gamma_\star\big(\norm{f_1-f_1'}_\infty\norm{f_2}_\infty+\norm{f_1'}_\infty\norm{f_2-f_2'}_\infty\big).
\end{equation}
For the resolvent filters, with $s,u\ge s_\circ>0$,
\begin{equation}\label{eqn:app-vol-finite-nuclear}
\abs{\mathcal K^{F,G}_{s,u}(K,K)-\mathcal K^{F,G}_{s,u}(K',K')}\le\frac{2}{B\,s_\circ^{3/2}}\norm{K-K'}_* .
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_finite_iv {m n B : ℕ} (hB : 0 < B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    {s u s₀ : ℝ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hu : s₀ ≤ u) (K K' : Mat m n) :
    |contractionRes B F G s u K K - contractionRes B F G s u K' K'| ≤
      2 / (B * s₀ ^ ((3 : ℝ) / 2)) * nuc (K - K') := by
  have hs_pos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hu_pos : 0 < u := lt_of_lt_of_le hs₀ hu
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hB0 : (B : ℝ) ≠ 0 := hBpos.ne'
  have hBi : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hBpos.le
  have hN : 0 ≤ nuc (K - K') := nuc_nonneg _
  have hsr : 0 < Real.sqrt s₀ := Real.sqrt_pos.mpr hs₀
  have hr : 0 < s₀ * Real.sqrt s₀ := mul_pos hs₀ hsr
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu_pos
  have hss : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs_pos
  have hpow : s₀ ^ ((3 : ℝ) / 2) = s₀ * Real.sqrt s₀ := by
    rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add hs₀, Real.rpow_one,
      Real.sqrt_eq_rpow]
  have hmat : F * Muon.DetEquiv.Xs K s * G * (Muon.DetEquiv.Xs K u)ᵀ
      - F * Muon.DetEquiv.Xs K' s * G * (Muon.DetEquiv.Xs K' u)ᵀ
      = F * (Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s) * G * (Muon.DetEquiv.Xs K u)ᵀ
        + F * Muon.DetEquiv.Xs K' s * G * (Muon.DetEquiv.Xs K u - Muon.DetEquiv.Xs K' u)ᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub]
    abel
  have hopQ := (Muon.DetEquiv.lem_app_de_resolvent K u hu_pos).2.2.1
  have hopP := (Muon.DetEquiv.lem_app_de_resolvent K' s hs_pos).2.2.1
  have hT1 : |Matrix.trace (F * (Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s) * G *
      (Muon.DetEquiv.Xs K u)ᵀ)| ≤ 1 / (2 * Real.sqrt u) * (2 / s * nuc (K - K')) :=
    (trace_left_nuc_P5 F (Muon.DetEquiv.Xs K s - Muon.DetEquiv.Xs K' s) G
      (Muon.DetEquiv.Xs K u) hF hG).trans
      (mul_le_mul hopQ (xs_nuc_lip_P5 K K' hs_pos) (nuc_nonneg _) (by positivity))
  have hT2 : |Matrix.trace (F * Muon.DetEquiv.Xs K' s * G *
      (Muon.DetEquiv.Xs K u - Muon.DetEquiv.Xs K' u)ᵀ)| ≤ 1 / (2 * Real.sqrt s) * (2 / u * nuc (K - K')) :=
    (trace_right_nuc_P5 F (Muon.DetEquiv.Xs K' s) G
      (Muon.DetEquiv.Xs K u - Muon.DetEquiv.Xs K' u) hF hG).trans
      (mul_le_mul hopP (xs_nuc_lip_P5 K K' hu_pos) (nuc_nonneg _) (by positivity))
  have hc1 : 1 / (2 * Real.sqrt u) * (2 / s * nuc (K - K')) ≤
      1 / (s₀ * Real.sqrt s₀) * nuc (K - K') := by
    have e : 1 / (2 * Real.sqrt u) * (2 / s * nuc (K - K')) =
        1 / (s * Real.sqrt u) * nuc (K - K') := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le hr (mul_le_mul hs (Real.sqrt_le_sqrt hu) hsr.le hs_pos.le)) hN
  have hc2 : 1 / (2 * Real.sqrt s) * (2 / u * nuc (K - K')) ≤
      1 / (s₀ * Real.sqrt s₀) * nuc (K - K') := by
    have e : 1 / (2 * Real.sqrt s) * (2 / u * nuc (K - K')) =
        1 / (u * Real.sqrt s) * nuc (K - K') := by
      field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_right
      (one_div_le_one_div_of_le hr (mul_le_mul hu (Real.sqrt_le_sqrt hs) hsr.le hu_pos.le)) hN
  unfold contractionRes contraction
  rw [eqn_app_vol_filters_sharp_i hs_pos K, eqn_app_vol_filters_sharp_i hu_pos K,
    eqn_app_vol_filters_sharp_i hs_pos K', eqn_app_vol_filters_sharp_i hu_pos K', hpow,
    ← mul_sub, ← Matrix.trace_sub, hmat, Matrix.trace_add, abs_mul, abs_of_nonneg hBi]
  refine (mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add (hT1.trans hc1)
    (hT2.trans hc2))) hBi).trans (le_of_eq ?_)
  field_simp
  ring

/-! ## Square truncation: statements -/

private lemma int_inv_sq_P6 {s : ℝ} (hs : 0 < s) (T : ℝ) :
    ∫ y in (0 : ℝ)..T, 1 / (s ^ 2 + y ^ 2) = Real.arctan (T / s) / s := by
  have hs0 : s ≠ 0 := hs.ne'
  have hderiv : ∀ y ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun y : ℝ => Real.arctan (y / s) / s) (1 / (s ^ 2 + y ^ 2)) y := by
    intro y _
    have h1 : HasDerivAt (fun y : ℝ => y / s) (1 / s) y := by
      simpa using (hasDerivAt_id y).div_const s
    have h2 := (h1.arctan).div_const s
    convert h2 using 1
    have hq : (s ^ 2 + y ^ 2) ≠ 0 := (add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg y)).ne'
    field_simp
  have hcont : Continuous (fun y : ℝ => 1 / (s ^ 2 + y ^ 2)) := by
    apply Continuous.div continuous_const (by fun_prop)
    intro y
    exact (add_pos_of_pos_of_nonneg (pow_pos hs 2) (sq_nonneg y)).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp

private lemma omegaT_closed_P6 {ϱ T x s : ℝ} (hs : 0 < s) (hs2 : s ^ 2 = x ^ 2 + ϱ) :
    omegaT ϱ T x = (2 / Real.pi) * (x * (Real.arctan (T / s) / s)) := by
  unfold omegaT iotaF
  have h : ∀ y : ℝ, x / (x ^ 2 + (ϱ + y ^ 2)) = x * (1 / (s ^ 2 + y ^ 2)) := by
    intro y
    rw [hs2, show x ^ 2 + (ϱ + y ^ 2) = x ^ 2 + ϱ + y ^ 2 by ring]
    ring
  simp only [h]
  rw [intervalIntegral.integral_const_mul, int_inv_sq_P6 hs T]

/-- `lem:app-vol-square`, part (i): the scalar truncation bounds
`0 ≤ ω_{ϱ,T}(x)/ω_ϱ(x) ≤ 1` for `x ≠ 0` and `|ω_ϱ(x) − ω_{ϱ,T}(x)| ≤ 2|x|/(πT)`, snapshot
`cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_square_i`. The full environment,
verbatim from `section.tex`:
```latex
\begin{lemma}[Square truncation]\label{lem:app-vol-square}
For $\ridge>0$, $T>0$ and $x\in\R$,
\begin{equation}\label{eqn:app-vol-QT-scalar}
0\le\frac{\omega_{\ridge,T}(x)}{\omega_\ridge(x)}\le1\quad(x\ne0),\qquad
\abs{\omega_\ridge(x)-\omega_{\ridge,T}(x)}\le\frac{2\abs x}{\pi T}.
\end{equation}
Consequently, for random $K,H\in\R^{\Nout\times\Nin}$ with
$B^{-1}\EE\norm K_\F^2\le C_M$ and $B^{-1}\EE\norm H_\F^2\le C_M$, and for
$\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-square}
\Big|\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](K,H)
-\frac4{\pi^2}\int_0^T\!\!\int_0^T\EE\,\mathcal K^{F,G}_{\ridge+x^2,\ridge'+y^2}(K,H)\,dx\,dy\Big|
\le\frac{4\sqrt{\gamma_\star C_M}}{\pi T}.
\end{equation}
In the frozen-state model, $B^{-1}\EE\norm{\Mt}_\F^2\le C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\end{lemma}
```
-/
theorem lem_app_vol_square_i (ϱ T : ℝ) (hϱ : 0 < ϱ) (hT : 0 < T) :
    (∀ x : ℝ, x ≠ 0 → 0 ≤ omegaT ϱ T x / omegaF ϱ x ∧ omegaT ϱ T x / omegaF ϱ x ≤ 1) ∧
    ∀ x : ℝ, |omegaF ϱ x - omegaT ϱ T x| ≤ 2 * |x| / (Real.pi * T) := by
  have hP : ∀ x : ℝ, 0 < x ^ 2 + ϱ := fun x => by nlinarith [sq_nonneg x]
  have hs : ∀ x : ℝ, 0 < Real.sqrt (x ^ 2 + ϱ) := fun x => Real.sqrt_pos.mpr (hP x)
  have hs2 : ∀ x : ℝ, Real.sqrt (x ^ 2 + ϱ) ^ 2 = x ^ 2 + ϱ := fun x => Real.sq_sqrt (hP x).le
  have hF : ∀ x : ℝ, omegaF ϱ x = x / Real.sqrt (x ^ 2 + ϱ) := fun x => rfl
  have hT' : ∀ x : ℝ, omegaT ϱ T x =
      (2 / Real.pi) * (x * (Real.arctan (T / Real.sqrt (x ^ 2 + ϱ)) / Real.sqrt (x ^ 2 + ϱ))) :=
    fun x => omegaT_closed_P6 (hs x) (hs2 x)
  constructor
  · intro x hx
    have hsx := hs x
    have hs0 : Real.sqrt (x ^ 2 + ϱ) ≠ 0 := hsx.ne'
    have hx' : x ≠ 0 := hx
    have hA0 : 0 ≤ Real.arctan (T / Real.sqrt (x ^ 2 + ϱ)) :=
      Real.arctan_nonneg.mpr (div_nonneg hT.le hsx.le)
    have hA1 : Real.arctan (T / Real.sqrt (x ^ 2 + ϱ)) < Real.pi / 2 :=
      Real.arctan_lt_pi_div_two _
    have hratio : omegaT ϱ T x / omegaF ϱ x =
        (2 / Real.pi) * Real.arctan (T / Real.sqrt (x ^ 2 + ϱ)) := by
      rw [hT' x, hF x]
      field_simp
    rw [hratio]
    refine ⟨mul_nonneg (by positivity) hA0, ?_⟩
    have h2 : (2 / Real.pi) * (Real.pi / 2) = 1 := by
      field_simp
    calc (2 / Real.pi) * Real.arctan (T / Real.sqrt (x ^ 2 + ϱ))
        ≤ (2 / Real.pi) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hA1.le (by positivity)
      _ = 1 := h2
  · intro x
    have hsx := hs x
    have hs0 : Real.sqrt (x ^ 2 + ϱ) ≠ 0 := hsx.ne'
    have hT0 : T ≠ 0 := hT.ne'
    have hB : Real.arctan (Real.sqrt (x ^ 2 + ϱ) / T) =
        Real.pi / 2 - Real.arctan (T / Real.sqrt (x ^ 2 + ϱ)) := by
      have hinv : Real.sqrt (x ^ 2 + ϱ) / T = (T / Real.sqrt (x ^ 2 + ϱ))⁻¹ :=
        (inv_div _ _).symm
      rw [hinv, Real.arctan_inv_of_pos (div_pos hT hsx)]
    have key : omegaF ϱ x - omegaT ϱ T x =
        (x / Real.sqrt (x ^ 2 + ϱ)) * ((2 / Real.pi) * Real.arctan (Real.sqrt (x ^ 2 + ϱ) / T)) := by
      rw [hF x, hT' x, hB]
      field_simp
    have hB0 : 0 ≤ Real.arctan (Real.sqrt (x ^ 2 + ϱ) / T) :=
      Real.arctan_nonneg.mpr (div_nonneg hsx.le hT.le)
    have hB1 : Real.arctan (Real.sqrt (x ^ 2 + ϱ) / T) ≤ Real.sqrt (x ^ 2 + ϱ) / T :=
      Real.arctan_le_self (div_nonneg hsx.le hT.le)
    have hpos : 0 ≤ 2 / Real.pi := by positivity
    rw [key, abs_mul, abs_div, abs_of_pos hsx, abs_of_nonneg (mul_nonneg hpos hB0)]
    calc |x| / Real.sqrt (x ^ 2 + ϱ) * ((2 / Real.pi) * Real.arctan (Real.sqrt (x ^ 2 + ϱ) / T))
        ≤ |x| / Real.sqrt (x ^ 2 + ϱ) *
            ((2 / Real.pi) * (Real.sqrt (x ^ 2 + ϱ) / T)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hB1 hpos)
            (div_nonneg (abs_nonneg x) hsx.le)
      _ = 2 * |x| / (Real.pi * T) := by
          field_simp

/-! ## Helpers for `lem_app_vol_square_ii` (P-D.1.P7) -/

private lemma entries_spectral_P7 {m n : ℕ} (K : Mat m n) :
    ∃ (w : Fin m → Fin n → Fin (m + n) → ℝ) (lam : Fin (m + n) → ℝ),
      ∀ (g : ℝ → ℝ) (i : Fin m) (j : Fin n), oddSharp g K i j = ∑ l, w i j l * g (lam l) := by
  have hA := Muon.Foundations.hermDilation_isHermitian K
  refine ⟨fun i j l => (hA.eigenvectorUnitary : Mat (m + n) (m + n)) (Fin.castAdd n i) l *
    (hA.eigenvectorUnitary : Mat (m + n) (m + n)) (Fin.natAdd m j) l, hA.eigenvalues,
    fun g i j => ?_⟩
  unfold oddSharp upperRight
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply]
  exact Finset.sum_congr rfl fun l _ => by ring

private lemma fro_oddSharp_le_P7 {m n : ℕ} (g : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hg : ∀ x, |g x| ≤ c * |x|) (K : Mat m n) :
    fro (oddSharp g K) ≤ c * fro K := by
  have hA := Muon.Foundations.hermDilation_isHermitian K
  have hcA : (cfc g (hermDilation K)).IsHermitian := by
    have : IsSelfAdjoint (cfc g (hermDilation K)) := cfc_predicate _ _
    exact this
  have h1 := Muon.Foundations.fro_upperRight_sq_le _ hcA
  rw [fro_sq_cfc_P1 _ hA] at h1
  have h2 := fro_sq_cfc_P1 _ hA (fun x : ℝ => x)
  have hsa : IsSelfAdjoint (hermDilation K) := hA
  rw [cfc_id' ℝ (hermDilation K) hsa] at h2
  have h3 := Muon.Foundations.fro_hermDilation K
  have h4 : ∑ i, g (hA.eigenvalues i) ^ 2 ≤ c ^ 2 * ∑ i, hA.eigenvalues i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have := hg (hA.eigenvalues i)
    have h5 : g (hA.eigenvalues i) ^ 2 ≤ (c * |hA.eigenvalues i|) ^ 2 := by
      rw [← sq_abs (g (hA.eigenvalues i))]
      exact pow_le_pow_left₀ (abs_nonneg _) this 2
    calc g (hA.eigenvalues i) ^ 2 ≤ (c * |hA.eigenvalues i|) ^ 2 := h5
      _ = c ^ 2 * hA.eigenvalues i ^ 2 := by rw [mul_pow, sq_abs]
  have h6 : fro (oddSharp g K) ^ 2 ≤ (c * fro K) ^ 2 := by
    unfold oddSharp
    rw [mul_pow]
    nlinarith [h1, h2, h3, h4]
  exact (pow_le_pow_iff_left₀ (fro_nn_aux _) (mul_nonneg hc (fro_nn_aux _)) two_ne_zero).mp h6

private lemma iota_cont_P7 {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Continuous (fun p : ℝ × ℝ => iotaF (ϱ + p.1 ^ 2) p.2) := by
  unfold iotaF
  refine Continuous.div (by fun_prop) (by fun_prop) (fun p => ?_)
  nlinarith [sq_nonneg p.2, sq_nonneg p.1]

private lemma iota_odd_P7 (s x : ℝ) : iotaF s (-x) = -iotaF s x := by
  unfold iotaF; rw [neg_sq, neg_div]

private lemma omegaT_abs_le_P7 {ϱ T : ℝ} (hϱ : 0 < ϱ) (hT : 0 < T) (x : ℝ) :
    |omegaT ϱ T x| ≤ 1 := by
  by_cases hx : x = 0
  · subst hx
    simp [omegaT, iotaF]
  · have hsq := (lem_app_vol_square_i ϱ T hϱ hT).1
    obtain ⟨h0, h1⟩ := hsq x hx
    have hF : omegaF ϱ x ≠ 0 := by
      unfold omegaF
      exact div_ne_zero hx (Real.sqrt_pos.mpr (by nlinarith [sq_nonneg x])).ne'
    have e : omegaT ϱ T x = (omegaT ϱ T x / omegaF ϱ x) * omegaF ϱ x := by field_simp
    rw [e, abs_mul, abs_of_nonneg h0]
    calc _ ≤ 1 * |omegaF ϱ x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ 1 := by rw [one_mul]; exact omega_abs_le_P2 hϱ x


private lemma omegaT_odd_bdd_lip_P7 {ϱ T : ℝ} (hϱ : 0 < ϱ) (hT : 0 < T) :
    IsOddBddLip (omegaT ϱ T) := by
  have hc : ∀ x : ℝ, Continuous (fun y : ℝ => iotaF (ϱ + y ^ 2) x) := fun x =>
    (iota_cont_P7 hϱ).comp (continuous_id.prodMk continuous_const)
  refine ⟨fun x => ?_, ⟨1, fun x => ?_⟩, ⟨2 / Real.pi * T / ϱ, fun x x' => ?_⟩⟩
  · unfold omegaT
    simp only [iota_odd_P7, intervalIntegral.integral_neg]
    ring
  · exact omegaT_abs_le_P7 hϱ hT x
  · unfold omegaT
    rw [← mul_sub, ← intervalIntegral.integral_sub
      ((hc x).intervalIntegrable _ _) ((hc x').intervalIntegrable _ _), abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / Real.pi)]
    have hb : ‖∫ y in (0 : ℝ)..T, (iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y ^ 2) x')‖ ≤
        (1 / ϱ * |x - x'|) * |T - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const (fun y _ => ?_)
      rw [Real.norm_eq_abs]
      refine (iota_lip_P2 (by positivity) x x').trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      exact one_div_le_one_div_of_le hϱ (by nlinarith [sq_nonneg y])
    rw [Real.norm_eq_abs, sub_zero, abs_of_pos hT] at hb
    calc 2 / Real.pi * |∫ y in (0 : ℝ)..T, (iotaF (ϱ + y ^ 2) x - iotaF (ϱ + y ^ 2) x')|
        ≤ 2 / Real.pi * ((1 / ϱ * |x - x'|) * T) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 / Real.pi * T / ϱ * |x - x'| := by ring

private lemma supNorm_omegaT_le_P7 {ϱ T : ℝ} (hϱ : 0 < ϱ) (hT : 0 < T) : supNorm (omegaT ϱ T) ≤ 1 :=
  ciSup_le fun x => omegaT_abs_le_P7 hϱ hT x

private lemma pointwise_trunc_P7 {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (ϱ ϱ' T : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (hT : 0 < T) (K H : Mat m n) :
    |contraction B F G (omegaF ϱ) (omegaF ϱ') K H -
        contraction B F G (omegaT ϱ T) (omegaT ϱ' T) K H| ≤
      Real.sqrt (γstar / B) * (2 / (Real.pi * T)) * (fro K + fro H) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hBi : (0 : ℝ) ≤ (B : ℝ)⁻¹ := inv_nonneg.mpr hBpos.le
  have hcoef := coef_P4 B (min m n) hB γstar hdim
  have hc0 : 0 ≤ 2 / (Real.pi * T) := by positivity
  have hF1 := omega_odd_bdd_lip_P2 hϱ
  have hF2 := omega_odd_bdd_lip_P2 hϱ'
  have hT1 := omegaT_odd_bdd_lip_P7 hϱ hT
  have hT2 := omegaT_odd_bdd_lip_P7 hϱ' hT
  -- the four matrices
  set A := oddSharp (omegaF ϱ) K with hAdef
  set AT := oddSharp (omegaT ϱ T) K with hATdef
  set C := oddSharp (omegaF ϱ') H with hCdef
  set CT := oddSharp (omegaT ϱ' T) H with hCTdef
  have hdA : fro (A - AT) ≤ 2 / (Real.pi * T) * fro K := by
    have := fro_oddSharp_le_P7 (fun x => omegaF ϱ x - omegaT ϱ T x) _ hc0
      (fun x => by
        have := (lem_app_vol_square_i ϱ T hϱ hT).2 x
        calc _ ≤ 2 * |x| / (Real.pi * T) := this
          _ = 2 / (Real.pi * T) * |x| := by ring) K
    rwa [oddSharp_sub_fun_P5 _ _ hF1 hT1] at this
  have hdC : fro (C - CT) ≤ 2 / (Real.pi * T) * fro H := by
    have := fro_oddSharp_le_P7 (fun x => omegaF ϱ' x - omegaT ϱ' T x) _ hc0
      (fun x => by
        have := (lem_app_vol_square_i ϱ' T hϱ' hT).2 x
        calc _ ≤ 2 * |x| / (Real.pi * T) := this
          _ = 2 / (Real.pi * T) * |x| := by ring) H
    rwa [oddSharp_sub_fun_P5 _ _ hF2 hT2] at this
  have hC1 : fro C ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
    have := (sharp_op_fro_aux_P1 (omegaF ϱ') hF2 H).2
    rwa [supNorm_omega_P2 hϱ', mul_one] at this
  have hAT1 : fro AT ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
    have := (sharp_op_fro_aux_P1 (omegaT ϱ T) hT1 K).2
    refine this.trans ?_
    calc _ ≤ Real.sqrt ((min m n : ℕ) : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left (supNorm_omegaT_le_P7 hϱ hT) (Real.sqrt_nonneg _)
      _ = _ := mul_one _
  have hmat : F * A * G * Cᵀ - F * AT * G * CTᵀ =
      F * (A - AT) * G * Cᵀ + F * AT * G * (C - CT)ᵀ := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub]
    abel
  have key : contraction B F G (omegaF ϱ) (omegaF ϱ') K H -
      contraction B F G (omegaT ϱ T) (omegaT ϱ' T) K H =
      (B : ℝ)⁻¹ * (Matrix.trace (F * (A - AT) * G * Cᵀ) + Matrix.trace (F * AT * G * (C - CT)ᵀ)) := by
    unfold contraction
    rw [← mul_sub, ← Matrix.trace_sub, hmat, Matrix.trace_add]
  have ht1 : |Matrix.trace (F * (A - AT) * G * Cᵀ)| ≤
      (2 / (Real.pi * T) * fro K) * Real.sqrt ((min m n : ℕ) : ℝ) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hdA) hC1 (fro_nn_aux _)
        (mul_nonneg hc0 (fro_nn_aux _)))
  have ht2 : |Matrix.trace (F * AT * G * (C - CT)ᵀ)| ≤
      Real.sqrt ((min m n : ℕ) : ℝ) * (2 / (Real.pi * T) * fro H) :=
    (trace_mul_transpose_le_P4 _ _).trans
      (mul_le_mul ((fro_sandwich_P4 F _ G hF hG).trans hAT1) hdC (fro_nn_aux _) (Real.sqrt_nonneg _))
  rw [key, abs_mul, abs_of_nonneg hBi]
  have hnn : 0 ≤ 2 / (Real.pi * T) * (fro K + fro H) :=
    mul_nonneg hc0 (add_nonneg (fro_nn_aux _) (fro_nn_aux _))
  calc (B : ℝ)⁻¹ * |Matrix.trace (F * (A - AT) * G * Cᵀ) + Matrix.trace (F * AT * G * (C - CT)ᵀ)|
      ≤ (B : ℝ)⁻¹ * ((2 / (Real.pi * T) * fro K) * Real.sqrt ((min m n : ℕ) : ℝ) +
          Real.sqrt ((min m n : ℕ) : ℝ) * (2 / (Real.pi * T) * fro H)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ht1 ht2)) hBi
    _ = ((B : ℝ)⁻¹ * Real.sqrt ((min m n : ℕ) : ℝ)) * (2 / (Real.pi * T) * (fro K + fro H)) := by
        ring
    _ ≤ Real.sqrt (γstar / B) * (2 / (Real.pi * T) * (fro K + fro H)) :=
        mul_le_mul_of_nonneg_right hcoef hnn
    _ = _ := by ring

private lemma integral_fro_le_P7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (hB : 0 < B) (CM : ℝ)
    (K : Ω → Mat m n) (hK : ∀ i j, Measurable fun ω => K ω i j)
    (hKm : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (K ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM) :
    Integrable (fun ω => fro (K ω)) P ∧ ∫ ω, fro (K ω) ∂P ≤ Real.sqrt (B * CM) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hmeas : Measurable fun ω => fro (K ω) :=
    Measurable.sqrt (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ =>
      ((hK i j).norm.pow_const 2))
  have hmeas2 : Measurable fun ω => fro (K ω) ^ 2 := hmeas.pow_const 2
  set E := ∫⁻ ω, ENNReal.ofReal (fro (K ω) ^ 2) ∂P with hE
  have hE1 : E ≤ ENNReal.ofReal B * ENNReal.ofReal CM := by
    have h1 : ENNReal.ofReal B * (ENNReal.ofReal ((B : ℝ)⁻¹) * E) ≤
        ENNReal.ofReal B * ENNReal.ofReal CM := by gcongr
    rwa [← mul_assoc, ← ENNReal.ofReal_mul hBpos.le, mul_inv_cancel₀ hBpos.ne', ENNReal.ofReal_one,
      one_mul] at h1
  have hEfin : E < ⊤ := lt_of_le_of_lt hE1 (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hint2 : Integrable (fun ω => fro (K ω) ^ 2) P := by
    refine ⟨hmeas2.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact hEfin
  have hint1 : Integrable (fun ω => fro (K ω)) P := by
    refine Integrable.mono' (hint2.add (integrable_const (1 : ℝ))) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (fro_nn_aux _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (fro (K ω) - 1)]
  refine ⟨hint1, ?_⟩
  have hI2' : ∫ ω, fro (K ω) ^ 2 ∂P ≤ Real.sqrt (B * CM) ^ 2 := by
    have h1 : ENNReal.ofReal (∫ ω, fro (K ω) ^ 2 ∂P) = E := by
      rw [ofReal_integral_eq_lintegral_ofReal hint2 (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    have h2 : ENNReal.ofReal (∫ ω, fro (K ω) ^ 2 ∂P) ≤ ENNReal.ofReal (B * CM) := by
      rw [h1, ENNReal.ofReal_mul hBpos.le]; exact hE1
    have hnn : 0 ≤ ∫ ω, fro (K ω) ^ 2 ∂P := integral_nonneg (fun ω => sq_nonneg (fro (K ω)))
    rcases (ENNReal.ofReal_le_ofReal_iff' ).mp h2 with h | h
    · rw [Real.sq_sqrt (hnn.trans h)]; exact h
    · exact h.trans (sq_nonneg _)
  set s := Real.sqrt (B * CM) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have key : ∀ t : ℝ, 0 < t → ∫ ω, fro (K ω) ∂P ≤ s ^ 2 / (2 * t) + t / 2 := by
    intro t ht
    have h1 : ∫ ω, fro (K ω) ∂P ≤ ∫ ω, (fro (K ω) ^ 2 / (2 * t) + t / 2) ∂P := by
      refine integral_mono hint1 ((hint2.div_const _).add (integrable_const _))
        (fun ω => ?_)
      simp only
      rw [← sub_nonneg]
      have : fro (K ω) ^ 2 / (2 * t) + t / 2 - fro (K ω) = (fro (K ω) - t) ^ 2 / (2 * t) := by
        field_simp; ring
      rw [this]; positivity
    refine h1.trans ?_
    rw [integral_add (hint2.div_const _) (integrable_const _), integral_div]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    gcongr
  by_cases hs' : s = 0
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have := key (2 * ε) (by linarith)
    rw [hs'] at this ⊢
    simp at this
    linarith
  · have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs')
    have := key s hspos
    refine this.trans (le_of_eq ?_)
    field_simp
    ring

private lemma lin_int_P7 {k l : ℕ} (T : ℝ) (p : Fin k → Fin l → ℝ) (u : ℝ → Fin k → Fin l → ℝ)
    (hu : ∀ i j, Continuous fun x => u x i j) :
    ∑ i, ∑ j, p i j * ∫ x in (0 : ℝ)..T, u x i j =
      ∫ x in (0 : ℝ)..T, ∑ i, ∑ j, p i j * u x i j := by
  have hI : ∀ i j, IntervalIntegrable (fun x => p i j * u x i j) MeasureTheory.volume 0 T :=
    fun i j => (continuous_const.mul (hu i j)).intervalIntegrable _ _
  calc ∑ i, ∑ j, p i j * ∫ x in (0 : ℝ)..T, u x i j
      = ∑ i, ∑ j, ∫ x in (0 : ℝ)..T, p i j * u x i j := by
        simp_rw [intervalIntegral.integral_const_mul]
    _ = ∑ i, ∫ x in (0 : ℝ)..T, ∑ j, p i j * u x i j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [intervalIntegral.integral_finset_sum (fun j _ => hI i j)]
    _ = ∫ x in (0 : ℝ)..T, ∑ i, ∑ j, p i j * u x i j := by
        rw [intervalIntegral.integral_finset_sum]
        intro i _
        exact (continuous_finset_sum _ fun j _ => continuous_const.mul (hu i j)).intervalIntegrable _ _

private lemma trace_left_P7 {m n : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (A : Mat m n)
    (X : Matrix (Fin n) (Fin m) ℝ) :
    Matrix.trace (F * A * X) = ∑ i, ∑ j, (X * F) j i * A i j := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  rw [Finset.sum_comm]

private lemma trace_right_P7 {m n : ℕ} (X C : Mat m n) :
    Matrix.trace (X * Cᵀ) = ∑ i, ∑ j, X i j * C i j := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

private lemma bilinear_int_P7 {m n : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (T : ℝ) (a c : ℝ → Mat m n) (ha : ∀ i j, Continuous fun x => a x i j)
    (hc : ∀ i j, Continuous fun x => c x i j) :
    Matrix.trace (F * (Matrix.of fun i j => ∫ x in (0 : ℝ)..T, a x i j) * G *
        (Matrix.of fun i j => ∫ x in (0 : ℝ)..T, c x i j)ᵀ) =
      ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, Matrix.trace (F * a x * G * (c y)ᵀ) := by
  set Cb : Mat m n := Matrix.of fun i j => ∫ x in (0 : ℝ)..T, c x i j with hCb
  have step1 : Matrix.trace (F * (Matrix.of fun i j => ∫ x in (0 : ℝ)..T, a x i j) * G * Cbᵀ) =
      ∫ x in (0 : ℝ)..T, Matrix.trace (F * a x * G * Cbᵀ) := by
    have e : ∀ A : Mat m n, Matrix.trace (F * A * G * Cbᵀ) =
        ∑ i, ∑ j, (G * Cbᵀ * F) j i * A i j := fun A => by
      rw [Matrix.mul_assoc _ G, trace_left_P7]
    simp_rw [e]
    simp only [Matrix.of_apply]
    exact lin_int_P7 T _ a ha
  have step2 : ∀ x, Matrix.trace (F * a x * G * Cbᵀ) =
      ∫ y in (0 : ℝ)..T, Matrix.trace (F * a x * G * (c y)ᵀ) := by
    intro x
    simp_rw [trace_right_P7]
    simp only [hCb, Matrix.of_apply]
    exact lin_int_P7 T _ c hc
  rw [step1]
  exact intervalIntegral.integral_congr (fun x _ => step2 x)

private lemma iota_entry_cont_P7 {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    Continuous fun y : ℝ => oddSharp (iotaF (ϱ + y ^ 2)) K i j := by
  obtain ⟨w, lam, h⟩ := entries_spectral_P7 K
  simp_rw [h]
  refine continuous_finset_sum _ fun l _ => continuous_const.mul ?_
  exact (iota_cont_P7 hϱ).comp (continuous_id.prodMk continuous_const)

private lemma omegaT_entry_P7 {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (T : ℝ) (K : Mat m n)
    (i : Fin m) (j : Fin n) :
    oddSharp (omegaT ϱ T) K i j =
      ∫ y in (0 : ℝ)..T, (2 / Real.pi) * oddSharp (iotaF (ϱ + y ^ 2)) K i j := by
  obtain ⟨w, lam, h⟩ := entries_spectral_P7 K
  simp_rw [h]
  have hI : ∀ l ∈ Finset.univ, IntervalIntegrable
      (fun y : ℝ => w i j l * iotaF (ϱ + y ^ 2) (lam l)) MeasureTheory.volume 0 T := fun l _ =>
    (continuous_const.mul
      ((iota_cont_P7 hϱ).comp (continuous_id.prodMk continuous_const))).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finset_sum hI, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul]
  unfold omegaT
  ring

private lemma stepB_P7 {m n B : ℕ} (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    {ϱ ϱ' : ℝ} (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (T : ℝ) (K H : Mat m n) :
    contraction B F G (omegaT ϱ T) (omegaT ϱ' T) K H =
      (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
        contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) K H := by
  have hK : oddSharp (omegaT ϱ T) K = Matrix.of fun i j => ∫ x in (0 : ℝ)..T,
      ((2 / Real.pi) • oddSharp (iotaF (ϱ + x ^ 2)) K) i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact omegaT_entry_P7 hϱ T K i j
  have hH : oddSharp (omegaT ϱ' T) H = Matrix.of fun i j => ∫ x in (0 : ℝ)..T,
      ((2 / Real.pi) • oddSharp (iotaF (ϱ' + x ^ 2)) H) i j := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    exact omegaT_entry_P7 hϱ' T H i j
  have hc1 : ∀ i j, Continuous fun x : ℝ => ((2 / Real.pi) • oddSharp (iotaF (ϱ + x ^ 2)) K) i j :=
    fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact continuous_const.mul (iota_entry_cont_P7 hϱ K i j)
  have hc2 : ∀ i j, Continuous fun x : ℝ => ((2 / Real.pi) • oddSharp (iotaF (ϱ' + x ^ 2)) H) i j :=
    fun i j => by
      simp only [Matrix.smul_apply, smul_eq_mul]
      exact continuous_const.mul (iota_entry_cont_P7 hϱ' H i j)
  unfold contraction
  rw [hK, hH, bilinear_int_P7 F G T _ _ hc1 hc2]
  have e : ∀ x y : ℝ, Matrix.trace (F * ((2 / Real.pi) • oddSharp (iotaF (ϱ + x ^ 2)) K) * G *
      ((2 / Real.pi) • oddSharp (iotaF (ϱ' + y ^ 2)) H)ᵀ) =
      (4 / Real.pi ^ 2) * Matrix.trace (F * oddSharp (iotaF (ϱ + x ^ 2)) K * G *
        (oddSharp (iotaF (ϱ' + y ^ 2)) H)ᵀ) := fun x y => by
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.trace_smul,
      smul_eq_mul]
    ring
  simp_rw [e, intervalIntegral.integral_const_mul]
  simp_rw [← intervalIntegral.integral_const_mul]
  ring

private lemma fro_cont_P7 {m n : ℕ} : Continuous (fun K : Mat m n => fro K) := by
  unfold fro
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  have : Continuous fun K : Mat m n => K i j :=
    (continuous_apply j).comp (continuous_apply i)
  exact (continuous_norm.comp this).pow 2

private lemma contraction_cont_P7 {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Continuous (fun p : Mat m n × Mat m n => contraction B F G f g p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  have hb : Continuous fun q : Mat m n × Mat m n =>
      Real.sqrt (γstar / B) * (lipConst f * supNorm g * fro (q.1 - p.1) +
        supNorm f * lipConst g * fro (q.2 - p.2)) := by
    have h1 : Continuous fun q : Mat m n × Mat m n => fro (q.1 - p.1) :=
      fro_cont_P7.comp (continuous_fst.sub continuous_const)
    have h2 : Continuous fun q : Mat m n × Mat m n => fro (q.2 - p.2) :=
      fro_cont_P7.comp (continuous_snd.sub continuous_const)
    exact continuous_const.mul ((continuous_const.mul h1).add (continuous_const.mul h2))
  have h0 := hb.tendsto p
  have hz : fro (p.1 - p.1) = 0 ∧ fro (p.2 - p.2) = 0 := by simp [fro]
  rw [hz.1, hz.2] at h0
  simp only [mul_zero, add_zero, zero_add] at h0
  refine squeeze_zero (fun q => dist_nonneg) (fun q => ?_) h0
  rw [Real.dist_eq]
  exact lem_app_vol_finite_ii hB γstar hdim F G hF hG f g hf hg q.1 p.1 q.2 p.2

private lemma fubini_P7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ) (hT : 0 < T) (h : ℝ → ℝ → Ω → ℝ)
    (hm : Measurable (fun p : (ℝ × ℝ) × Ω => h p.1.1 p.1.2 p.2)) (M0 : ℝ)
    (hb : ∀ x y ω, |h x y ω| ≤ M0) :
    ∫ ω, (∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, h x y ω) ∂P =
      ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, ∫ ω, h x y ω ∂P := by
  simp only [intervalIntegral.integral_of_le hT.le]
  set μ : Measure ℝ := volume.restrict (Set.Ioc 0 T) with hμ
  have : IsFiniteMeasure μ := ⟨by rw [hμ, Measure.restrict_apply_univ]; simp⟩
  have hbd : ∀ x ω, ‖∫ y, h x y ω ∂μ‖ ≤ M0 * μ.real Set.univ := fun x ω =>
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hb x y ω)
  have hmeas_f : Measurable (fun q : Ω × ℝ => ∫ y, h q.2 y q.1 ∂μ) := by
    have h1 : StronglyMeasurable (fun q : (Ω × ℝ) × ℝ => h q.1.2 q.2 q.1.1) :=
      (hm.comp (by fun_prop : Measurable fun q : (Ω × ℝ) × ℝ => ((q.1.2, q.2), q.1.1))).stronglyMeasurable
    exact (StronglyMeasurable.integral_prod_right (f := fun (q : Ω × ℝ) (y : ℝ) => h q.2 y q.1)
      h1).measurable
  have hi1 : Integrable (Function.uncurry fun (ω : Ω) (x : ℝ) => ∫ y, h x y ω ∂μ) (P.prod μ) :=
    Integrable.of_bound hmeas_f.aestronglyMeasurable (M0 * μ.real Set.univ)
      (Filter.Eventually.of_forall fun q => hbd q.2 q.1)
  have step1 := integral_integral_swap hi1
  have step2 : ∀ x, ∫ ω, ∫ y, h x y ω ∂μ ∂P = ∫ y, ∫ ω, h x y ω ∂P ∂μ := by
    intro x
    have hm2 : Measurable (fun q : Ω × ℝ => h x q.2 q.1) :=
      hm.comp (by fun_prop : Measurable fun q : Ω × ℝ => ((x, q.2), q.1))
    have hi2 : Integrable (Function.uncurry fun (ω : Ω) (y : ℝ) => h x y ω) (P.prod μ) :=
      Integrable.of_bound hm2.aestronglyMeasurable M0
        (Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hb x q.2 q.1)
    exact integral_integral_swap hi2
  rw [step1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => step2 x)

private lemma meas_contraction_P7 {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} (hB : 0 < B) (γstar : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (K H : Ω → Mat m n)
    (hK : ∀ i j, Measurable fun ω => K ω i j) (hH : ∀ i j, Measurable fun ω => H ω i j)
    (f g : ℝ → ℝ) (hf : IsOddBddLip f) (hg : IsOddBddLip g) :
    Measurable fun ω => contraction B F G f g (K ω) (H ω) := by
  have hc := contraction_cont_P7 hB γstar hdim F G hF hG f g hf hg
  have hKmeas : Measurable (fun ω => (K ω : Fin m → Fin n → ℝ)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hK i)
  have hHmeas : Measurable (fun ω => (H ω : Fin m → Fin n → ℝ)) :=
    measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hH i)
  have hKH := hKmeas.prodMk hHmeas
  have hc' : Continuous (fun p : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) =>
      contraction B F G f g p.1 p.2) := hc
  have hm' : Measurable (fun p : (Fin m → Fin n → ℝ) × (Fin m → Fin n → ℝ) =>
      contraction B F G f g p.1 p.2) := hc'.measurable
  have hcomp := hm'.comp hKH
  exact hcomp

/-- `lem:app-vol-square`, part (ii): the matrix truncation bound `eqn:app-vol-square`, snapshot
`cr-2026-10-23`. Declaration of record `Muon.Volatility.lem_app_vol_square_ii`.
Hypotheses: a probability space `P`; the random matrices `K`, `H` are entrywise measurable with
`B⁻¹ E‖K‖_F² ≤ C_M` and `B⁻¹ E‖H‖_F² ≤ C_M` (`lintegral` form); `‖F‖, ‖G‖ ≤ 1`; `hdim` as in
`lem:app-vol-finite`. The expectation of the truncated and untruncated contraction is `integral`.
The full environment, verbatim from `section.tex`:
```latex
\begin{lemma}[Square truncation]\label{lem:app-vol-square}
For $\ridge>0$, $T>0$ and $x\in\R$,
\begin{equation}\label{eqn:app-vol-QT-scalar}
0\le\frac{\omega_{\ridge,T}(x)}{\omega_\ridge(x)}\le1\quad(x\ne0),\qquad
\abs{\omega_\ridge(x)-\omega_{\ridge,T}(x)}\le\frac{2\abs x}{\pi T}.
\end{equation}
Consequently, for random $K,H\in\R^{\Nout\times\Nin}$ with
$B^{-1}\EE\norm K_\F^2\le C_M$ and $B^{-1}\EE\norm H_\F^2\le C_M$, and for
$\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-square}
\Big|\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](K,H)
-\frac4{\pi^2}\int_0^T\!\!\int_0^T\EE\,\mathcal K^{F,G}_{\ridge+x^2,\ridge'+y^2}(K,H)\,dx\,dy\Big|
\le\frac{4\sqrt{\gamma_\star C_M}}{\pi T}.
\end{equation}
In the frozen-state model, $B^{-1}\EE\norm{\Mt}_\F^2\le C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\end{lemma}
```
-/
theorem lem_app_vol_square_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m n B : ℕ} (hB : 0 < B) (γstar CM : ℝ)
    (hdim : ((min m n : ℕ) : ℝ) ≤ γstar * B)
    (F : Matrix (Fin m) (Fin m) ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hF : opNorm F ≤ 1) (hG : opNorm G ≤ 1)
    (K H : Ω → Mat m n)
    (hK : ∀ i j, Measurable fun ω => K ω i j) (hH : ∀ i j, Measurable fun ω => H ω i j)
    (hKm : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (K ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM)
    (hHm : ENNReal.ofReal ((B : ℝ)⁻¹) * ∫⁻ ω, ENNReal.ofReal (fro (H ω) ^ 2) ∂P ≤
      ENNReal.ofReal CM)
    (ϱ ϱ' T : ℝ) (hϱ : 0 < ϱ) (hϱ' : 0 < ϱ') (hT : 0 < T) :
    |(∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) ∂P) -
        (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T,
          ∫ ω, contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K ω) (H ω) ∂P|
      ≤ 4 * Real.sqrt (γstar * CM) / (Real.pi * T) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hγ : 0 ≤ γstar := by
    by_contra hneg
    push Not at hneg
    have : γstar * B < 0 := mul_neg_of_neg_of_pos hneg hBpos
    have h0 : (0 : ℝ) ≤ ((min m n : ℕ) : ℝ) := Nat.cast_nonneg _
    linarith
  have meas : ∀ f g : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g →
      Measurable fun ω => contraction B F G f g (K ω) (H ω) := fun f g hf hg =>
    meas_contraction_P7 hB γstar hdim F G hF hG K H hK hH f g hf hg
  have integ : ∀ f g : ℝ → ℝ, IsOddBddLip f → IsOddBddLip g →
      Integrable (fun ω => contraction B F G f g (K ω) (H ω)) P := fun f g hf hg =>
    Integrable.of_bound (meas f g hf hg).aestronglyMeasurable (γstar * supNorm f * supNorm g)
      (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs]
        exact lem_app_vol_finite_i hB γstar hdim F G hF hG f g hf hg (K ω) (H ω))
  have hωF := omega_odd_bdd_lip_P2 hϱ
  have hωF' := omega_odd_bdd_lip_P2 hϱ'
  have hωT := omegaT_odd_bdd_lip_P7 hϱ hT
  have hωT' := omegaT_odd_bdd_lip_P7 hϱ' hT
  -- the integrand of the double integral
  set h : ℝ → ℝ → Ω → ℝ := fun x y ω =>
    contraction B F G (iotaF (ϱ + x ^ 2)) (iotaF (ϱ' + y ^ 2)) (K ω) (H ω) with hh
  have hpos : ∀ x : ℝ, 0 < ϱ + x ^ 2 := fun x => by positivity
  have hpos' : ∀ x : ℝ, 0 < ϱ' + x ^ 2 := fun x => by positivity
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => h p.1.1 p.1.2 p.2) := by
    refine measurable_uncurry_of_continuous_of_measurable
      (u := fun (xy : ℝ × ℝ) (ω : Ω) => h xy.1 xy.2 ω) (fun ω => ?_) (fun xy => ?_)
    · have hA : Continuous fun x : ℝ => oddSharp (iotaF (ϱ + x ^ 2)) (K ω) :=
        continuous_pi fun i => continuous_pi fun j => iota_entry_cont_P7 hϱ (K ω) i j
      have hC : Continuous fun y : ℝ => oddSharp (iotaF (ϱ' + y ^ 2)) (H ω) :=
        continuous_pi fun i => continuous_pi fun j => iota_entry_cont_P7 hϱ' (H ω) i j
      have h1 : Continuous fun xy : ℝ × ℝ => F * oddSharp (iotaF (ϱ + xy.1 ^ 2)) (K ω) :=
        continuous_const.matrix_mul (hA.comp continuous_fst)
      have h2 : Continuous fun xy : ℝ × ℝ => F * oddSharp (iotaF (ϱ + xy.1 ^ 2)) (K ω) * G :=
        h1.matrix_mul continuous_const
      have h3 : Continuous fun xy : ℝ × ℝ => (oddSharp (iotaF (ϱ' + xy.2 ^ 2)) (H ω))ᵀ :=
        (hC.comp continuous_snd).matrix_transpose
      have := (h2.matrix_mul h3).matrix_trace
      exact continuous_const.mul this
    · exact meas _ _ (iota_odd_bdd_lip_P2 (hpos _)) (iota_odd_bdd_lip_P2 (hpos' _))
  have hM0 : ∀ x y ω, |h x y ω| ≤ γstar * (1 / (2 * Real.sqrt ϱ)) * (1 / (2 * Real.sqrt ϱ')) := by
    intro x y ω
    have h1 := lem_app_vol_finite_i hB γstar hdim F G hF hG _ _
      (iota_odd_bdd_lip_P2 (hpos x)) (iota_odd_bdd_lip_P2 (hpos' y)) (K ω) (H ω)
    rw [supNorm_iota_P2 (hpos x), supNorm_iota_P2 (hpos' y)] at h1
    have hs1 : Real.sqrt ϱ ≤ Real.sqrt (ϱ + x ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
    have hs2 : Real.sqrt ϱ' ≤ Real.sqrt (ϱ' + y ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
    have hp1 : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
    have hp2 : 0 < Real.sqrt ϱ' := Real.sqrt_pos.mpr hϱ'
    have e1 : 1 / (2 * Real.sqrt (ϱ + x ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have e2 : 1 / (2 * Real.sqrt (ϱ' + y ^ 2)) ≤ 1 / (2 * Real.sqrt ϱ') :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    have e1' : 0 ≤ 1 / (2 * Real.sqrt (ϱ + x ^ 2)) := by positivity
    have e2' : 0 ≤ 1 / (2 * Real.sqrt (ϱ' + y ^ 2)) := by positivity
    exact h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left e1 hγ) e2 e2' (by positivity))
  have hFub := fubini_P7 P T hT h hm _ hM0
  have hcT : ∀ ω, contraction B F G (omegaT ϱ T) (omegaT ϱ' T) (K ω) (H ω) =
      (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, h x y ω := fun ω =>
    stepB_P7 F G hϱ hϱ' T (K ω) (H ω)
  have hE2 : ∫ ω, contraction B F G (omegaT ϱ T) (omegaT ϱ' T) (K ω) (H ω) ∂P =
      (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, ∫ ω, h x y ω ∂P := by
    rw [← hFub, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => hcT ω)
  change abs ((∫ ω, contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) ∂P) -
      (4 / Real.pi ^ 2) * ∫ x in (0 : ℝ)..T, ∫ y in (0 : ℝ)..T, ∫ ω, h x y ω ∂P) ≤ _
  rw [← hE2, ← integral_sub (integ _ _ hωF hωF') (integ _ _ hωT hωT')]
  obtain ⟨hiK, hIK⟩ := integral_fro_le_P7 P hB CM K hK hKm
  obtain ⟨hiH, hIH⟩ := integral_fro_le_P7 P hB CM H hH hHm
  set c : ℝ := Real.sqrt (γstar / B) * (2 / (Real.pi * T)) with hc
  have hc0 : 0 ≤ c := by positivity
  have hbint : Integrable (fun ω => c * (fro (K ω) + fro (H ω))) P :=
    (hiK.add hiH).const_mul c
  have h1 : ‖∫ ω, (contraction B F G (omegaF ϱ) (omegaF ϱ') (K ω) (H ω) -
      contraction B F G (omegaT ϱ T) (omegaT ϱ' T) (K ω) (H ω)) ∂P‖ ≤
      ∫ ω, c * (fro (K ω) + fro (H ω)) ∂P :=
    norm_integral_le_of_norm_le hbint (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]
      have := pointwise_trunc_P7 hB γstar hdim F G hF hG ϱ ϱ' T hϱ hϱ' hT (K ω) (H ω)
      rw [hc]; linarith)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [integral_const_mul, integral_add hiK hiH]
  calc c * (∫ ω, fro (K ω) ∂P + ∫ ω, fro (H ω) ∂P)
      ≤ c * (Real.sqrt (B * CM) + Real.sqrt (B * CM)) :=
        mul_le_mul_of_nonneg_left (add_le_add hIK hIH) hc0
    _ = 4 * Real.sqrt (γstar * CM) / (Real.pi * T) := by
        have hsq : Real.sqrt (γstar / B) * Real.sqrt (B * CM) = Real.sqrt (γstar * CM) := by
          rw [← Real.sqrt_mul (by positivity)]
          congr 1
          field_simp
        rw [hc]
        calc Real.sqrt (γstar / B) * (2 / (Real.pi * T)) * (Real.sqrt (B * CM) + Real.sqrt (B * CM))
            = 4 * (Real.sqrt (γstar / B) * Real.sqrt (B * CM)) / (Real.pi * T) := by ring
          _ = _ := by rw [hsq]

/-! ### Helpers for part (iii) (task P-D.1.P8) -/

section P8helpers
open Muon.Setup

private lemma abs_entry_le_fro_P8 {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma fro_sq_eq_P8 {m n : ℕ} (K : Mat m n) : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma continuous_fro_sq_P8 {m n : ℕ} : Continuous (fun K : Mat m n => fro K ^ 2) := by
  simp_rw [fro_sq_eq_P8]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (Continuous.matrix_elem continuous_id i j).pow 2

private lemma young_fro_P8 {m n : ℕ} (K L : Mat m n) :
    fro K ^ 2 ≤ 2 * fro L ^ 2 + 2 * fro (K - L) ^ 2 := by
  simp_rw [fro_sq_eq_P8]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun j _ => ?_
  simp only [Matrix.sub_apply]
  nlinarith [sq_nonneg (L i j - (K i j - L i j))]

private lemma summable_mat_of_fro_P8 {m n : ℕ} {ι : Type*} (f : ι → Mat m n)
    (hf : Summable fun j => fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun k => ?_
  refine Summable.of_norm_bounded hf (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact abs_entry_le_fro_P8 (f j) i k

private lemma summand_cont_P8 {m n B : ℕ} (F : FrozenParams m n B) :
    Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
  fun_prop

private lemma frozenBatchG_sm_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (summand_cont_P8 F).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private instance instPseudoMetrizableMat_P8 {m n : ℕ} :
    TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))

private instance instSecondCountableMat_P8 {m n : ℕ} : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma frozenBuf_aesm_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    AEStronglyMeasurable (frozenBuf F S t) P := by
  have hae := (lem_app_setup_ema_law_i F S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (frozenBatchG_sm_P8 F S (t + 1 - (j : ℤ))).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      summable_mat_of_fro_P8 _ (hω t)
    exact hs.hasSum.tendsto_sum_nat

private lemma memLp_of_covT_ne_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    {X : Ω → Mat m n} [IsProbabilityMeasure P]
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i : Fin m) (j : Fin n)
    (h : covT P X i j i j ≠ 0) : MemLp (fun ω => X ω i j) 2 P := by
  by_contra hn
  apply h
  unfold covT
  rw [covariance_self (hX i j).aemeasurable]
  exact variance_of_not_memLp (hX i j).aestronglyMeasurable hn

private lemma sampleTensor_diag_pos_P8 {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    sampleTensor A i j i j ≠ 0 := by
  unfold sampleTensor
  have h1 : 0 ≤ (A * Aᵀ) i i := by
    rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => by simp [mul_self_nonneg]
  have h2 : 0 ≤ (Aᵀ * A) j j := by
    rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => by simp [mul_self_nonneg]
  simp only [if_true, mul_one, one_mul]
  have h3 : 0 ≤ A i j * A i j := mul_self_nonneg _
  have h4 : 0 ≤ A i j * A i j := mul_self_nonneg _
  nlinarith

private lemma sampleX_entry_memLp_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n : ℕ}
    [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZ : Measurable Z) (hW : Measurable W)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => sampleX A (Z ω) (W ω) i j) 2 P := by
  refine memLp_of_covT_ne_P8 (X := fun ω => sampleX A (Z ω) (W ω)) ?_ i j ?_
  · intro i j
    unfold sampleX
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, dotProduct, Matrix.mulVec]
    fun_prop
  · rw [lem_app_setup_gaussian_moments_ii hZW A hA]
    exact sampleTensor_diag_pos_P8 A i j

private lemma frozenBatchG_entry_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
    (ω : Ω) (i : Fin m) (j : Fin n) :
    frozenBatchG F S s ω i j = (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ p : Fin m, ∑ q : Fin n,
      (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q := by
  unfold frozenBatchG sampleX
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.vecMulVec_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

private lemma frozenBatchG_entry_memLp_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => frozenBatchG F S s ω i j) 2 P := by
  have : (fun ω => frozenBatchG F S s ω i j) = fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ p : Fin m,
      ∑ q : Fin n, (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q := by
    funext ω; exact frozenBatchG_entry_P8 F S s ω i j
  rw [this]
  have h1 : ∀ a : Fin B, ∀ p : Fin m, ∀ q : Fin n, MemLp (fun ω => (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P := fun a p q =>
    MemLp.const_mul (sampleX_entry_memLp_P8 (Z := fun ω => (S.zw s a ω).1)
      (W := fun ω => (S.zw s a ω).2)
      (measurable_fst.comp (S.meas s a)) (measurable_snd.comp (S.meas s a)) (S.law s a)
      F.A F.hA p q) _
  have h4 : MemLp (fun ω => ∑ a : Fin B, ∑ p : Fin m, ∑ q : Fin n,
      (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P :=
    memLp_finset_sum _ fun a _ => memLp_finset_sum _ fun p _ => memLp_finset_sum _ fun q _ =>
      h1 a p q
  exact h4.const_mul _

/-- `fro (frozenBuf)²` is integrable. -/
private lemma buf_fro_int_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) :
    Integrable (fun ω => fro (frozenBuf F S t ω) ^ 2) P := by
  have h1 := (lem_app_setup_truncation_i 1 one_pos F S t 0).1
  have htr : ∀ i j, MemLp (fun ω => truncBuf F S t 0 ω i j) 2 P := by
    intro i j
    have : (fun ω => truncBuf F S t 0 ω i j) = fun ω => ∑ r ∈ Finset.range (0 + 1),
        emaW F.β r * frozenBatchG F S (t + 1 - (r : ℤ)) ω i j := by
      funext ω; simp [truncBuf, Matrix.sum_apply, Matrix.smul_apply]
    rw [this]
    exact memLp_finset_sum _ fun r _ => (frozenBatchG_entry_memLp_P8 F S _ i j).const_mul _
  have h2 : Integrable (fun ω => fro (truncBuf F S t 0 ω) ^ 2) P := by
    simp_rw [fro_sq_eq_P8]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ =>
      (htr i j).integrable_sq
  have hm : AEStronglyMeasurable (fun ω => fro (frozenBuf F S t ω) ^ 2) P :=
    (continuous_fro_sq_P8.comp_aestronglyMeasurable (frozenBuf_aesm_P8 F S t))
  refine Integrable.mono' ((h2.const_mul 2).add (h1.const_mul 2)) hm
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have := young_fro_P8 (frozenBuf F S t ω) (truncBuf F S t 0 ω)
  simp only [Pi.add_apply]
  linarith

/-- Uncentered second moment of the frozen buffer. -/
private lemma buf_second_moment_P8 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) :
    ∫ ω, fro (frozenBuf F S t ω) ^ 2 ∂P
      = fro (mean P (frozenBatchG F S (t + 1))) ^ 2 + sPow F.β 2 * frozenVB S F := by
  obtain ⟨hmean, -, hcen⟩ := lem_app_setup_ema_law_iii F S t
  set μ := mean P (frozenBatchG F S (t + 1)) with hμ
  have hint := buf_fro_int_P8 F S t
  have hent : ∀ i j, Integrable (fun ω => frozenBuf F S t ω i j) P := by
    intro i j
    have hae : AEStronglyMeasurable (fun ω => frozenBuf F S t ω i j) P :=
      (Continuous.matrix_elem (continuous_id : Continuous (fun K : Mat m n => K)) i j).comp_aestronglyMeasurable
        (frozenBuf_aesm_P8 F S t)
    refine (hint.add (integrable_const (1 : ℝ))).mono' hae
      (Filter.Eventually.of_forall fun ω => ?_)
    have h := abs_entry_le_fro_P8 (frozenBuf F S t ω) i j
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [abs_nonneg (frozenBuf F S t ω i j), sq_nonneg (fro (frozenBuf F S t ω) - 1)]
  have hmu : ∀ i j, ∫ ω, frozenBuf F S t ω i j ∂P = μ i j := by
    intro i j
    have := congrFun (congrFun hmean i) j
    simpa [mean] using this
  have hpt : ∀ ω, fro (frozenBuf F S t ω - μ) ^ 2 = fro (frozenBuf F S t ω) ^ 2
      - 2 * ∑ i, ∑ j, μ i j * frozenBuf F S t ω i j + fro μ ^ 2 := by
    intro ω
    rw [fro_sq_eq_P8, fro_sq_eq_P8, fro_sq_eq_P8, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.sub_apply]
    ring
  have hI : ∀ i j, Integrable (fun ω => μ i j * frozenBuf F S t ω i j) P :=
    fun i j => (hent i j).const_mul (μ i j)
  have hcrossI : Integrable (fun ω => ∑ i, ∑ j, μ i j * frozenBuf F S t ω i j) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j
  have hcross : ∫ ω, ∑ i, ∑ j, μ i j * frozenBuf F S t ω i j ∂P = fro μ ^ 2 := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j)]
    rw [fro_sq_eq_P8]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => hI i j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul, hmu]; ring
  have h := hcen
  simp_rw [hpt] at h
  have e1 : Integrable (fun ω => 2 * ∑ i, ∑ j, μ i j * frozenBuf F S t ω i j) P :=
    hcrossI.const_mul 2
  have e2 : Integrable (fun ω => fro (frozenBuf F S t ω) ^ 2
      - 2 * ∑ i, ∑ j, μ i j * frozenBuf F S t ω i j) P := hint.sub e1
  rw [integral_add e2 (integrable_const _), integral_sub hint e1, integral_const_mul, hcross,
    integral_const] at h
  simp only [probReal_univ, smul_eq_mul, one_mul] at h
  linarith

end P8helpers

/-- `lem:app-vol-square`, part (iii): the frozen-state second moment
`B⁻¹ E‖M_t‖_F² ≤ C_M := C_Σ²(γ⋆+2)²`, snapshot `cr-2026-10-23`. Declaration of record
`Muon.Volatility.lem_app_vol_square_iii`. Hypotheses: the frozen-state model
(`Muon.Setup.FrozenParams`, `Muon.Setup.FrozenSamples`) with `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ` and
`N_out, N_in ≤ γ⋆ B` (the regime data of `assum:app-setup-regime`). The full environment, verbatim
from `section.tex`:
```latex
\begin{lemma}[Square truncation]\label{lem:app-vol-square}
For $\ridge>0$, $T>0$ and $x\in\R$,
\begin{equation}\label{eqn:app-vol-QT-scalar}
0\le\frac{\omega_{\ridge,T}(x)}{\omega_\ridge(x)}\le1\quad(x\ne0),\qquad
\abs{\omega_\ridge(x)-\omega_{\ridge,T}(x)}\le\frac{2\abs x}{\pi T}.
\end{equation}
Consequently, for random $K,H\in\R^{\Nout\times\Nin}$ with
$B^{-1}\EE\norm K_\F^2\le C_M$ and $B^{-1}\EE\norm H_\F^2\le C_M$, and for
$\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-square}
\Big|\EE\,\mathcal K^{F,G}[\omega_\ridge,\omega_{\ridge'}](K,H)
-\frac4{\pi^2}\int_0^T\!\!\int_0^T\EE\,\mathcal K^{F,G}_{\ridge+x^2,\ridge'+y^2}(K,H)\,dx\,dy\Big|
\le\frac{4\sqrt{\gamma_\star C_M}}{\pi T}.
\end{equation}
In the frozen-state model, $B^{-1}\EE\norm{\Mt}_\F^2\le C_M\defeq C_\Sigma^2(\gamma_\star+2)^2$.
\end{lemma}
```
-/
theorem lem_app_vol_square_iii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ}
    (Fp : Muon.Setup.FrozenParams m n B) (S : Muon.Setup.FrozenSamples P m n B)
    (CSig γstar : ℝ) (hCout : opNorm Fp.C.Sout ≤ CSig) (hCin : opNorm Fp.C.Sin ≤ CSig)
    (hm : (m : ℝ) ≤ γstar * B) (hn : (n : ℝ) ≤ γstar * B) (t : ℤ) :
    ENNReal.ofReal ((B : ℝ)⁻¹) *
        ∫⁻ ω, ENNReal.ofReal (fro (Muon.Setup.frozenBuf Fp S t ω) ^ 2) ∂P ≤
      ENNReal.ofReal (CSig ^ 2 * (γstar + 2) ^ 2) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast Fp.hB
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast Fp.hB
  have hint := buf_fro_int_P8 Fp S t
  have hmom := buf_second_moment_P8 Fp S t
  obtain ⟨hμ, hV⟩ := Muon.Setup.lem_app_setup_truncation_iv 1 one_pos Fp S t CSig hCout hCin
  have hC0 : 0 ≤ CSig := le_trans (opNorm_nonneg_P4 _) hCout
  have hβ0 := Fp.hβ.1
  have hβ1 := Fp.hβ.2
  have hs2 : sPow Fp.β 2 = (1 - Fp.β) / (1 + Fp.β) := sPow_two hβ0 hβ1
  have hsp0 : 0 ≤ sPow Fp.β 2 := by rw [hs2]; apply div_nonneg <;> linarith
  have hsp1 : sPow Fp.β 2 ≤ 1 := by
    rw [hs2, div_le_one (by linarith)]; linarith
  have hV0 : 0 ≤ Muon.Setup.frozenVB S Fp := integral_nonneg fun ω => sq_nonneg _
  have hγ : 0 ≤ γstar := by
    by_contra hneg
    push Not at hneg
    have : γstar * B < 0 := mul_neg_of_neg_of_pos hneg hBpos
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
    linarith
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hmu2 : fro (mean P (Muon.Setup.frozenBatchG Fp S (t + 1))) ^ 2 ≤ CSig ^ 2 :=
    pow_le_pow_left₀ (by unfold fro; exact Real.sqrt_nonneg _) hμ 2
  have hVle : sPow Fp.β 2 * Muon.Setup.frozenVB S Fp
      ≤ CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / B :=
    calc _ ≤ 1 * Muon.Setup.frozenVB S Fp := mul_le_mul_of_nonneg_right hsp1 hV0
      _ ≤ _ := by rw [one_mul]; exact hV
  have hnum : (B : ℝ)⁻¹ * ∫ ω, fro (Muon.Setup.frozenBuf Fp S t ω) ^ 2 ∂P
      ≤ CSig ^ 2 * (γstar + 2) ^ 2 := by
    rw [hmom]
    have hmn : (m : ℝ) * n ≤ γstar ^ 2 * B ^ 2 := by
      calc (m : ℝ) * n ≤ (γstar * B) * (γstar * B) := mul_le_mul hm hn hn0 (by positivity)
        _ = _ := by ring
    have hk : ((m : ℝ) * n + 2 * m + 2 * n + 3) ≤
        (γstar ^ 2 + 4 * γstar + 3) * B ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hB1 hγ, mul_nonneg hγ hBpos.le]
    have h1 : (B : ℝ)⁻¹ * (CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / B)
        ≤ CSig ^ 2 * (γstar ^ 2 + 4 * γstar + 3) := by
      rw [← mul_div_assoc, inv_mul_eq_div, div_div, div_le_iff₀ (by positivity)]
      calc CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3)
          ≤ CSig ^ 2 * ((γstar ^ 2 + 4 * γstar + 3) * B ^ 2) :=
            mul_le_mul_of_nonneg_left hk (sq_nonneg _)
        _ = _ := by ring
    have h2 : (B : ℝ)⁻¹ * CSig ^ 2 ≤ CSig ^ 2 := by
      calc (B : ℝ)⁻¹ * CSig ^ 2 ≤ 1 * CSig ^ 2 :=
            mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hB1) (sq_nonneg _)
        _ = _ := one_mul _
    calc (B : ℝ)⁻¹ * (fro (mean P (Muon.Setup.frozenBatchG Fp S (t + 1))) ^ 2
          + sPow Fp.β 2 * Muon.Setup.frozenVB S Fp)
        ≤ (B : ℝ)⁻¹ * (CSig ^ 2 + CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / B) :=
          mul_le_mul_of_nonneg_left (add_le_add hmu2 hVle) (inv_nonneg.2 hBpos.le)
      _ = (B : ℝ)⁻¹ * CSig ^ 2 + (B : ℝ)⁻¹ * (CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / B) := by
          ring
      _ ≤ CSig ^ 2 + CSig ^ 2 * (γstar ^ 2 + 4 * γstar + 3) := add_le_add h2 h1
      _ ≤ CSig ^ 2 * (γstar + 2) ^ 2 := by nlinarith [sq_nonneg CSig]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _),
    ← ENNReal.ofReal_mul (inv_nonneg.2 hBpos.le)]
  exact ENNReal.ofReal_le_ofReal hnum

end Muon.Volatility

end
