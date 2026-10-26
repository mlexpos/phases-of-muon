import Muon.Foundations.SVD
import SpectralFoundations.OperatorLipschitz

/-!
# Frobenius divided-difference bound and the Hermitian dilation

Foundations helper package for work package L-A.F2 (`sections/01-setup/CARD.md` §2, §4, §5).
No paper label: these are the standard facts the card lists as absent from Mathlib
(`CARD.md` §4, rows "Frobenius divided-difference bound" and "Hermitian dilation").

Snapshot `cr-2026-10-23`.

* `fro_cfc_sub_cfc_le`: for symmetric `A, B` and `f` Lipschitz with constant `L` on an interval
  `I` containing both spectra, `fro (cfc f A - cfc f B) ≤ L * fro (A - B)`.
* Hermitian dilation `hermDilation K = [[0, K], [Kᵀ, 0]]` of a rectangular `K`, indexed by
  `Fin (m + n)` (so that the Conventions `fro` and `cfc` apply to it unchanged). Its upper-right
  block is `upperRight`. The odd filter `x ↦ x (x² + ϱ)^{-1/2}` applied to the dilation has
  upper-right block `Q ϱ K` (`upperRight_cfc_hermDilation`).
* `fro_Q_sub_Q_le`: for `ϱ > 0`, `fro (Q ϱ K - Q ϱ L) ≤ ϱ^{-1/2} * fro (K - L)`. This is the
  helper for `lem_app_setup_filter_iii` in `Muon.Setup.RegularizedMap`.

Shared objects (`Mat`, `Q`, `fro`, `cfc`, `svd_rect_exists`, `cfc_intertwine_rect`) are reused
from `Muon.Foundations.Conventions` and `Muon.Foundations.SVD`; nothing is redefined there.
-/

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace Muon.Foundations

/-- Hermitian dilation `𝒟(K) = [[0, K], [Kᵀ, 0]]` of a real `m × n` matrix, as a matrix indexed
by `Fin (m + n)` (the sum `Fin m ⊕ Fin n` reindexed by `finSumFinEquiv`). Indexing by `Fin (m+n)`
keeps `fro`, `cfc` and `Mat` of Conventions applicable. Helper; no paper label. Snapshot
`cr-2026-10-23`. -/
def hermDilation {m n : ℕ} (K : Mat m n) : Mat (m + n) (m + n) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 K Kᵀ 0)

theorem hermDilation_eq_foundations {m n : ℕ} (K : Mat m n) :
    hermDilation K = SpectralFoundations.hermDilation K := rfl

/-- Upper-right `m × n` block of a `(m+n) × (m+n)` matrix. Helper; no paper label. Snapshot
`cr-2026-10-23`. -/
def upperRight {m n : ℕ} (X : Mat (m + n) (m + n)) : Mat m n :=
  Matrix.of fun i j => X (Fin.castAdd n i) (Fin.natAdd m j)

theorem upperRight_eq_foundations {m n : ℕ} (X : Mat (m + n) (m + n)) :
    upperRight X = SpectralFoundations.upperRight X := rfl

/-- The dilation of a real matrix is symmetric (`𝒟(K)ᵀ = 𝒟(K)`), so the Hermitian functional
calculus applies to it. Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem hermDilation_isHermitian {m n : ℕ} (K : Mat m n) :
    (hermDilation K).IsHermitian :=
  SpectralFoundations.hermDilation_isHermitian K

/-- Frobenius norm of the dilation: `‖𝒟(E)‖_F² = 2 ‖E‖_F²` for every rectangular `E`
(`CARD.md` §4, "Hermitian dilation"). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem fro_hermDilation {m n : ℕ} (E : Mat m n) :
    fro (hermDilation E) ^ 2 = 2 * fro E ^ 2 :=
  SpectralFoundations.fro_hermDilation E

/-- For a symmetric `(m+n) × (m+n)` matrix `X`, the upper-right block carries half of the
squared Frobenius mass: `2 ‖X_{12}‖_F² ≤ ‖X‖_F²`, because the lower-left block is `X_{12}ᵀ`.
Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem fro_upperRight_sq_le {m n : ℕ} (X : Mat (m + n) (m + n)) (hX : X.IsHermitian) :
    2 * fro (upperRight X) ^ 2 ≤ fro X ^ 2 :=
  SpectralFoundations.fro_upperRight_sq_le X hX

/-- The odd filter `x ↦ x (x² + ϱ)^{-1/2}` applied to the dilation has upper-right block
`Q_ϱ(K)`, for `ϱ > 0` (`eqn:app-setup-Q` written through the dilation; `CARD.md` §4,
"Hermitian dilation" and filter(iii)). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem upperRight_cfc_hermDilation {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) :
    upperRight (cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation K)) = Q ϱ K :=
  SpectralFoundations.upperRight_cfc_hermDilation hϱ K

/-- The filter `x ↦ x (x² + ϱ)^{-1/2}` is globally Lipschitz on `ℝ` with constant
`ϱ^{-1/2}` for `ϱ > 0` (its derivative `ϱ (x² + ϱ)^{-3/2}` is bounded by `ϱ^{-1/2}`; mean value
theorem). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem lipschitz_filter_fun {ϱ : ℝ} (hϱ : 0 < ϱ) :
    LipschitzWith (Real.toNNReal (ϱ ^ (-(1 / 2 : ℝ))))
      (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) :=
  SpectralFoundations.lipschitz_filter_fun hϱ

/-- Frobenius divided-difference bound for Hermitian functional calculus: for symmetric `A`, `B`
and `f` Lipschitz with constant `L` on an interval `I` containing both spectra,
`‖f(A) − f(B)‖_F ≤ L ‖A − B‖_F` (`CARD.md` §4, "Frobenius divided-difference bound"; used by
filter(iii)). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem fro_cfc_sub_cfc_le {k : ℕ} (A B : Mat k k) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (f : ℝ → ℝ) (I : Set ℝ) (hI : I.OrdConnected) (L : NNReal) (hf : LipschitzOnWith L f I)
    (hAI : spectrum ℝ A ⊆ I) (hBI : spectrum ℝ B ⊆ I) :
    fro (cfc f A - cfc f B) ≤ (L : ℝ) * fro (A - B) :=
  SpectralFoundations.fro_cfc_sub_cfc_le A B hA hB f I hI L hf hAI hBI

/-- Frobenius norm is nonnegative. Private helper. -/
private lemma fro_nonneg_aux {k l : ℕ} (A : Mat k l) : 0 ≤ fro A :=
  SpectralFoundations.fro_nonneg A

/-- Dilation is additive in the difference. Private helper. -/
private lemma hermDilation_sub_aux {m n : ℕ} (K L : Mat m n) :
    hermDilation K - hermDilation L = hermDilation (K - L) :=
  SpectralFoundations.hermDilation_sub K L

/-- Upper-right block is additive. Private helper. -/
private lemma upperRight_sub_aux {m n : ℕ} (X Y : Mat (m + n) (m + n)) :
    upperRight (X - Y) = upperRight X - upperRight Y :=
  SpectralFoundations.upperRight_sub X Y

/-- Functional calculus of a real symmetric matrix is symmetric. Private helper. -/
private lemma herm_cfc_isHerm_aux {k : ℕ} {A : Mat k k} (hA : A.IsHermitian) (g : ℝ → ℝ) :
    (cfc g A).IsHermitian :=
  SpectralFoundations.isHermitian_cfc hA g

/-- Frobenius Lipschitz bound for the regularized map: for `ϱ > 0`,
`‖Q_ϱ(K) − Q_ϱ(L)‖_F ≤ ϱ^{-1/2} ‖K − L‖_F` (`eqn:app-setup-lipschitz`, Frobenius form). This is
the helper for `lem_app_setup_filter_iii` in `Muon.Setup.RegularizedMap`. Helper; no paper label
of its own. Snapshot `cr-2026-10-23`. -/
theorem fro_Q_sub_Q_le {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K L : Mat m n) :
    fro (Q ϱ K - Q ϱ L) ≤ ϱ ^ (-(1 / 2 : ℝ)) * fro (K - L) := by
  have hK := hermDilation_isHermitian K
  have hL := hermDilation_isHermitian L
  have hY1 := fro_cfc_sub_cfc_le (hermDilation K) (hermDilation L) hK hL
    (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) Set.univ Set.ordConnected_univ
    (Real.toNNReal (ϱ ^ (-(1 / 2 : ℝ)))) (lipschitz_filter_fun hϱ).lipschitzOnWith
    (fun _ _ => Set.mem_univ _) (fun _ _ => Set.mem_univ _)
  rw [hermDilation_sub_aux] at hY1
  have hfro := fro_hermDilation (K - L)
  have hY : (cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation K)
      - cfc (fun x : ℝ => x * (x ^ 2 + ϱ) ^ (-(1 / 2 : ℝ))) (hermDilation L)).IsHermitian :=
    (herm_cfc_isHerm_aux hK _).sub (herm_cfc_isHerm_aux hL _)
  have hU := fro_upperRight_sq_le _ hY
  rw [upperRight_sub_aux, upperRight_cfc_hermDilation hϱ K,
    upperRight_cfc_hermDilation hϱ L] at hU
  have hc : ((Real.toNNReal (ϱ ^ (-(1 / 2 : ℝ))) : NNReal) : ℝ) = ϱ ^ (-(1 / 2 : ℝ)) :=
    Real.coe_toNNReal _ (Real.rpow_nonneg hϱ.le _)
  rw [hc] at hY1
  have hY2 := pow_le_pow_left₀ (fro_nonneg_aux _) hY1 2
  rw [mul_pow, hfro] at hY2
  have hB : fro (Q ϱ K - Q ϱ L) ^ 2 ≤ (ϱ ^ (-(1 / 2 : ℝ))) ^ 2 * fro (K - L) ^ 2 := by
    nlinarith [hU, hY2]
  have hp : 0 ≤ ϱ ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hϱ.le _
  exact (pow_le_pow_iff_left₀ (fro_nonneg_aux _) (mul_nonneg hp (fro_nonneg_aux _))
    two_ne_zero).mp (by rw [mul_pow]; exact hB)

end Muon.Foundations

end
