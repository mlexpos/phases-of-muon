import Muon.Foundations.Conventions
import SpectralFoundations.SVD

/-!
# Rectangular SVD and intertwining of the functional calculus

Foundations helper package for work package L-A.F1 (`sections/01-setup/CARD.md` §2, §5).
No paper label: these are the standard facts the card lists as absent from Mathlib
(`CARD.md` §4, "Standard facts used without citation").

Snapshot `cr-2026-10-23`.

* Rectangular SVD `K = ∑_{k<rank K} s_k p_k ⊗ r_k` with orthonormal families, `s_k > 0`, and
  `s_k` the Mathlib singular values `LinearMap.singularValues` of `Matrix.toEuclideanLin K`.
* Intertwining `K f(KᵀK) = f(KKᵀ) K`. This is already proved in
  `Muon.Foundations.Conventions` as `Muon.cfc_mul_transpose_mul_intertwine`; it is re-exported
  here under the card's name, not restated.

Shared objects (`Mat`, `Vec`, `outer`) are reused from `Muon.Foundations.Conventions`
(namespace `Muon`); nothing is redefined.
-/

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace Muon.Foundations

/-- Bridge: the Mathlib rank of a real matrix is the dimension of the range of its Euclidean
linear map. Needed to read the positive singular values as `0 ≤ k < K.rank`. Helper; no paper
label (`CARD.md` §2, rank bridge row). Snapshot `cr-2026-10-23`. -/
theorem rank_eq_finrank_range_toEuclideanLin {m n : ℕ} (K : Mat m n) :
    Module.finrank ℝ (Matrix.toEuclideanLin K).range = K.rank :=
  SpectralFoundations.rank_eq_finrank_range_toEuclideanLin K

/-- Positivity of the first `rank K` singular values: `s_k > 0` for `k < rank K`
(`CARD.md` §4, "Rectangular SVD"). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem singularValues_pos_of_lt_rank {m n : ℕ} (K : Mat m n) {k : ℕ} (hk : k < K.rank) :
    0 < (Matrix.toEuclideanLin K).singularValues k :=
  SpectralFoundations.singularValues_pos_of_lt_rank K hk

/-- Rectangular SVD (`CARD.md` §4, "Rectangular SVD: `K = ∑_{k<rank} s_k p_k⊗r_k` with
orthonormal families and s_k > 0, the s_k equal to `singularValues`"). The singular values are
Mathlib's `LinearMap.singularValues` of `Matrix.toEuclideanLin K`, so the `s_k` are fixed by
`K`; the existential supplies the left and right singular families `p`, `r` (orthonormal in
`Vec m` and `Vec n`). Helper; no paper label. Snapshot `cr-2026-10-23`. -/
theorem svd_rect_exists {m n : ℕ} (K : Mat m n) :
    ∃ (p : Fin K.rank → Vec m) (r : Fin K.rank → Vec n),
      (∀ k l : Fin K.rank, p k ⬝ᵥ p l = if k = l then 1 else 0) ∧
      (∀ k l : Fin K.rank, r k ⬝ᵥ r l = if k = l then 1 else 0) ∧
      K = ∑ k : Fin K.rank,
        (Matrix.toEuclideanLin K).singularValues (k : ℕ) • outer (p k) (r k) :=
  SpectralFoundations.svd_rect_exists K

/-- Intertwining of the functional calculus, `K f(KᵀK) = f(KKᵀ) K` for every real `f`
(`CARD.md` §4, "Intertwining of functional calculus"; used by `Q_eq_inv_sqrt_mul`).
Re-export of `Muon.cfc_mul_transpose_mul_intertwine`, which carries the proof; the one-line
proof here is the reuse, not a second argument. Snapshot `cr-2026-10-23`. -/
theorem cfc_intertwine_rect {m n : ℕ} (f : ℝ → ℝ) (K : Mat m n) :
    K * cfc f (Kᵀ * K) = cfc f (K * Kᵀ) * K :=
  SpectralFoundations.cfc_intertwine_rect f K

end Muon.Foundations

end
