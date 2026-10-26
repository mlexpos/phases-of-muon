import GaussianFoundations.Rotation
import Mathlib
import Muon.Foundations.Gaussian

/-!
# Foundations: rotation, sphere and Haar facts for the standard Gaussian (task L-0.5d)

Uncited standard facts used by Appendix A (`L-A.F4`: rotation invariance and the
`stdGaussianPi` ↔ `stdGaussian` bridge; 4-point Wick) and Appendix I (`L-I.0b`: Haar probability
on `O(n)`, the law of `Uv`, radius–direction independence). Source of record: snapshot
`cr-2026-10-23`.

Reused from `Muon.Foundations.Gaussian`, not restated: `stdGaussianPi`, the scalar moments,
`stdGaussianPi_map_coord`, `stdGaussianPi_sq_norm_moment` (`E‖g‖^{2q} = d_q(n)`),
`stdGaussian_conditional_linear`.

Declarations without a proof body carry `sorry`; proof routes are in the interface JSON.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace Muon.Foundations

/-- Euclidean norm on `ℝⁿ = Fin n → ℝ`, written out so that it is not the sup norm. -/
noncomputable def euclidNorm (n : ℕ) (z : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, z i ^ 2)

lemma euclidNorm_eq_foundations (n : ℕ) (z : Fin n → ℝ) :
    euclidNorm n z = GaussianFoundations.euclidNorm n z := rfl

/-- Uniform law on the unit sphere of `ℝⁿ`, realized as the law of `g / ‖g‖` for
`g ~ stdGaussianPi n`. The value at `g = 0` is `0`, a null event for `n ≥ 1`. -/
noncomputable def sphereGauss (n : ℕ) : Measure (Fin n → ℝ) :=
  (stdGaussianPi n).map (fun z => (euclidNorm n z)⁻¹ • z)

lemma sphereGauss_eq_foundations (n : ℕ) : sphereGauss n = GaussianFoundations.sphereGauss n := rfl

/-! ## Standard Gaussian vector: rotation invariance and bridge to `stdGaussian` -/

/-- Bridge to Mathlib's standard Gaussian on the Euclidean space: the coordinatewise
`stdGaussianPi n`, pushed forward by `WithLp.toLp 2`, is
`stdGaussian (EuclideanSpace ℝ (Fin n))`. -/
theorem stdGaussianPi_map_toLp (n : ℕ) :
    (stdGaussianPi n).map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      = stdGaussian (EuclideanSpace ℝ (Fin n)) :=
  GaussianFoundations.stdGaussianPi_map_toLp (n := n)

/-- Rotation invariance: for `O ∈ O(n)`, `O g` has the same law as `g`. -/
theorem stdGaussianPi_map_orthogonal (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = stdGaussianPi n :=
  GaussianFoundations.stdGaussianPi_map_orthogonal (n := n) (O := O)

/-- 4-point Wick formula for iid `N(0,1)` coordinates:
`E[g_i g_j g_k g_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`. -/
theorem stdGaussianPi_wick_four (n : ℕ) (i j k l : Fin n) :
    ∫ z : Fin n → ℝ, z i * z j * z k * z l ∂(stdGaussianPi n)
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) :=
  GaussianFoundations.stdGaussianPi_wick_four (n := n) (i := i) (j := j) (k := k) (l := l)

/-- `sphereGauss n` is a probability measure. -/
instance sphereGauss_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (sphereGauss n) :=
  GaussianFoundations.sphereGauss_isProbabilityMeasure (n := n)

/-! ## Haar probability measure on `O(n)` -/

/-- The orthogonal group is compact: its entries are bounded by `1` and it is closed. -/
theorem orthogonalGroup_compactSpace (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  GaussianFoundations.orthogonalGroup_compactSpace (n := n)

instance orthogonalGroup_compactSpace_inst (n : ℕ) :
    CompactSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
  GaussianFoundations.orthogonalGroup_compactSpace_inst (n := n)

/-- Haar probability measure on `O(n)`: the Haar measure of the compact group, normalized by
`haarMeasure K₀ K₀ = 1` with `K₀ = ⊤`, so that the total mass is `1`. -/
noncomputable def haarO (n : ℕ) : Measure (Matrix.orthogonalGroup (Fin n) ℝ) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Matrix.orthogonalGroup (Fin n) ℝ))

lemma haarO_eq_foundations (n : ℕ) : haarO n = GaussianFoundations.haarO n := rfl

/-- `haarO n` is a probability measure. -/
instance haarO_isProbabilityMeasure (n : ℕ) : IsProbabilityMeasure (haarO n) :=
  GaussianFoundations.haarO_isProbabilityMeasure (n := n)

/-- `haarO n` is left invariant. -/
instance haarO_isMulLeftInvariant (n : ℕ) : (haarO n).IsMulLeftInvariant :=
  GaussianFoundations.haarO_isMulLeftInvariant (n := n)

/-- `haarO n` is right invariant (the group is compact, hence unimodular). -/
instance haarO_isMulRightInvariant (n : ℕ) : (haarO n).IsMulRightInvariant :=
  GaussianFoundations.haarO_isMulRightInvariant (n := n)

/-! ## Law of `Uv` and radius–direction independence -/

/-- For `U` Haar on `O(n)` and a fixed unit vector `v`, `Uv` is uniform on the sphere, i.e. its law
is the law of `g / ‖g‖`. -/
theorem haarO_map_mulVec (n : ℕ) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    (haarO n).map (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) = sphereGauss n :=
  GaussianFoundations.haarO_map_mulVec (n := n) (v := v) (hv := hv)

/-- For `U` Haar on `O(n)` and a fixed unit `v`, almost surely no coordinate of `Uv` vanishes. -/
theorem haarO_mulVec_coord_ne_zero (n : ℕ) (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∀ᵐ U : Matrix.orthogonalGroup (Fin n) ℝ ∂(haarO n),
      ∀ i : Fin n, ((U : Matrix (Fin n) (Fin n) ℝ) *ᵥ v) i ≠ 0 :=
  GaussianFoundations.haarO_mulVec_coord_ne_zero (n := n) (v := v) (hv := hv)

/-- Radius–direction independence of the standard Gaussian vector: the radius `‖g‖` and the
direction `g / ‖g‖` are independent, with the direction having law `sphereGauss n`. -/
theorem stdGaussianPi_radius_direction_indep (n : ℕ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => (euclidNorm n z, (euclidNorm n z)⁻¹ • z))
      = ((stdGaussianPi n).map (euclidNorm n)).prod (sphereGauss n) :=
  GaussianFoundations.stdGaussianPi_radius_direction_indep (n := n)

end Muon.Foundations
