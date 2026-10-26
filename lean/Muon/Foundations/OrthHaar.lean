import GaussianFoundations.OrthHaar
import Mathlib
import Muon.Foundations.GaussianExtra

/-!
# Foundations: Haar probability measures on `O(n)` (task L-I.0b)

Ruling (coordinator, 2026-10-24, Q1 option (b)): downstream statements take a probability
measure `ν` on `O(n)` together with the hypothesis `IsOrthHaar ν`, which says that `ν` is a
probability measure invariant under left and right translation. Existence of such a measure is
stated separately (`orthHaar_exists`), and the constructed instance `haarO` from
`Muon.Foundations.GaussianExtra` is shown to satisfy the predicate (`haarO_isOrthHaar`), so the
hypothesis is not vacuous.

Statement only (`sorry`) except for the definition. Proof routes are in
`muon/phases-of-muon/appendix-nodes/results/L-I.0b-interface.json`.

Reused, not restated: `Matrix.orthogonalGroup`, its compactness instance
`orthogonalGroup_compactSpace_inst` and the constructed Haar probability `haarO`, all from
`Muon.Foundations.GaussianExtra`.
-/

open MeasureTheory

namespace Muon.Foundations

/-- `IsOrthHaar ν`: `ν` is a probability measure on `O(n)` that is invariant under left and
right translation by every orthogonal matrix. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: Appendix I, `def:app-sgd-state-law` (the Haar state law, l. 605–618),
through the sphere and sign lemmas of `Muon.Foundations.SphereGaussian`. -/
def IsOrthHaar {n : ℕ} (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) : Prop :=
  IsProbabilityMeasure ν ∧
    (∀ g : Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun h => g * h) = ν) ∧
    (∀ g : Matrix.orthogonalGroup (Fin n) ℝ, ν.map (fun h => h * g) = ν)

lemma IsOrthHaar_eq_foundations {n : ℕ} (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) :
    IsOrthHaar ν = GaussianFoundations.IsOrthHaar ν := rfl

/-- Existence of a Haar probability measure on `O(n)`: some probability measure on `O(n)` is
left and right invariant. (task L-I.0b; no paper label; snapshot cr-2026-10-23). Consumer:
non-vacuity of the hypothesis `IsOrthHaar ν` in Appendix I, `def:app-sgd-state-law`. Proof to
come (the witness `haarO n` from `GaussianExtra` is available; see `haarO_isOrthHaar`). -/
theorem orthHaar_exists (n : ℕ) :
    ∃ ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ), IsOrthHaar ν :=
  GaussianFoundations.orthHaar_exists (n := n)

/-- Uniqueness of the Haar probability measure on `O(n)`: two left- and right-invariant
probability measures on `O(n)` coincide. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: `orthHaar_map_mulVec_eq_sphereGauss` and the Haar sign lemmas of
Appendix I (l. 614, 718–719, 1130), which are stated for an arbitrary `ν` with `IsOrthHaar ν`. -/
theorem isOrthHaar_unique {n : ℕ} {ν ν' : Measure (Matrix.orthogonalGroup (Fin n) ℝ)}
    (hν : IsOrthHaar ν) (hν' : IsOrthHaar ν') : ν = ν' :=
  GaussianFoundations.isOrthHaar_unique (n := n) (ν := ν) (ν' := ν') (hν := hν) (hν' := hν')

/-- The constructed Haar probability `haarO n` of `GaussianExtra` satisfies `IsOrthHaar`. Shows
that the hypothesis of `IsOrthHaar` is satisfiable. (task L-I.0b; no paper label; snapshot
cr-2026-10-23). Consumer: as for `orthHaar_exists`. -/
theorem haarO_isOrthHaar (n : ℕ) : IsOrthHaar (haarO n) :=
  GaussianFoundations.haarO_isOrthHaar (n := n)

end Muon.Foundations
