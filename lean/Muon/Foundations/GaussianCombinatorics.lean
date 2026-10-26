import GaussianFoundations.Combinatorics
import Mathlib
import Muon.Foundations.Gaussian

/-!
# Foundations: Gaussian combinatorics and cited Gaussian facts (task L-0.6b)

Statements of three cited results, with their proofs left to the proof workers (proof routes in
`phases-of-muon/appendix-nodes/results/L-0.6b-interface.json`):

* `isserlis_wick`: Isserlis / Wick moment formula for products of i.i.d. standard Gaussian
  coordinates, in the perfect-matching form; the instances `gaussian_coord_moment_*`,
  `gaussian_trilinear_moment`, `gaussian_quartic_covariance`,
  `gaussian_weighted_square_moment`, `gaussian_weighted_linear_moment` that the sign-SGD card
  (#7, #23) and the volatility card (tree closure) use.
* `sheppard_arcsine`: `P(sign g ≠ sign h) = arccos ρ / π` for a centered unit-variance jointly
  Gaussian pair with correlation `ρ`.
* `poly_zero_set_null`: the zero set of a nonzero real multivariate polynomial is Lebesgue-null,
  hence null for the product Gaussian `stdGaussianPi`.

Certificates in `Muon.External` are not used here: these are proved statements (EXTERNAL-RESULTS
rows `IsserlisWick`, `SheppardArcsine`, `PolyZeroSetNull`, plan **prove**).
Snapshot `cr-2026-10-23`.
The standard Gaussian vector `stdGaussianPi n` and the one-dimensional moments are reused from
`Muon.Foundations.Gaussian`.
-/

namespace Muon.Foundations

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Matrix

/-! ## Perfect matchings -/

/-- A perfect matching of `Fin k`, encoded as a fixed-point-free involution `σ`: the pairs of the
matching are `{i, σ i}`. For `k` odd there are none; the empty type `Fin 0` has exactly one. -/
def IsPerfectMatchingInv {k : ℕ} (σ : Equiv.Perm (Fin k)) : Prop :=
  (∀ i, σ (σ i) = i) ∧ ∀ i, σ i ≠ i

lemma IsPerfectMatchingInv_eq_foundations {k : ℕ} (σ : Equiv.Perm (Fin k)) :
    IsPerfectMatchingInv σ = GaussianFoundations.IsPerfectMatchingInv σ := rfl

/-! ## Isserlis / Wick -/

/-- Isserlis / Wick formula, coordinate form (cited result `IsserlisWick`, L-0.6b).

For `g ~ N(0, I_d)` (`stdGaussianPi d`), indices `c : Fin k → Fin d` (the labelling of the
factors) and `k ≥ 0`:
`E ∏_{r=1}^{k} g_{c(r)} = #{π perfect matching of [k] : c is constant on each pair of π}`.
The perfect matching `π` is encoded as the fixed-point-free involution `σ` of `Fin k`, which is a
bijection between perfect matchings and such involutions. -/
theorem isserlis_wick (d k : ℕ) (c : Fin k → Fin d) :
    ∫ z, (∏ r : Fin k, z (c r)) ∂(stdGaussianPi d)
      = (Nat.card {σ : Equiv.Perm (Fin k) // IsPerfectMatchingInv σ ∧ ∀ i, c (σ i) = c i} : ℝ) :=
  GaussianFoundations.isserlis_wick_fin (d := d) (k := k) (c := c)

/-- Instance of `isserlis_wick`: `E g_i² = 1` for a standard Gaussian coordinate. -/
theorem gaussian_coord_moment_two (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 2 ∂(stdGaussianPi d) = 1 :=
  GaussianFoundations.gaussian_coord_moment_two (d := d) (i := i)

/-- Instance of `isserlis_wick`: `E g_i⁴ = 3`. -/
theorem gaussian_coord_moment_four (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 4 ∂(stdGaussianPi d) = 3 :=
  GaussianFoundations.gaussian_coord_moment_four (d := d) (i := i)

/-- Instance of `isserlis_wick`: `E g_i⁶ = 15`. -/
theorem gaussian_coord_moment_six (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 6 ∂(stdGaussianPi d) = 15 :=
  GaussianFoundations.gaussian_coord_moment_six (d := d) (i := i)

/-- Instance of `isserlis_wick`: `E g_i⁸ = 105`. -/
theorem gaussian_coord_moment_eight (d : ℕ) (i : Fin d) :
    ∫ z, z i ^ 8 ∂(stdGaussianPi d) = 105 :=
  GaussianFoundations.gaussian_coord_moment_eight (d := d) (i := i)

/-- Instance of `isserlis_wick` (sign-SGD #7, #23): for `Δ ∈ ℝ^{n×n}`, `r, q ∈ ℝⁿ` and
independent standard Gaussian vectors `w, z ~ N(0, I_n)`,
`E[(rᵀw)(qᵀz)(zᵀΔw)] = qᵀΔr`. The expectation is over the product law of `(w, z)`. -/
theorem gaussian_trilinear_moment (n : ℕ) (Δ : Matrix (Fin n) (Fin n) ℝ) (r q : Fin n → ℝ) :
    ∫ p : (Fin n → ℝ) × (Fin n → ℝ),
        (r ⬝ᵥ p.1) * (q ⬝ᵥ p.2) * (p.2 ⬝ᵥ (Δ *ᵥ p.1))
      ∂((stdGaussianPi n).prod (stdGaussianPi n))
      = q ⬝ᵥ (Δ *ᵥ r) :=
  GaussianFoundations.gaussian_trilinear_moment (n := n) (Δ := Δ) (r := r) (q := q)

/-- Instance of `isserlis_wick` (sign-SGD #23, Gaussian pairing): let `A ∈ ℝ^{n×n}`,
`Λ = A Aᵀ`, and let `y` have the law of `A g` with `g ~ N(0, I_n)`, i.e. `y ~ N(0, Λ)`. For a
symmetric `M`, `E[y ⊗ y (yᵀ M y)] = Tr(Λ M) Λ + 2 Λ M Λ`, written entrywise. -/
theorem gaussian_quartic_covariance (n : ℕ) (A M Λ : Matrix (Fin n) (Fin n) ℝ)
    (hΛ : Λ = A * Aᵀ) (hM : Mᵀ = M)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (y : Ω → Fin n → ℝ)
    (hy : P.map y = (stdGaussianPi n).map (fun g => A *ᵥ g)) (hyM : AEMeasurable y P)
    (i j : Fin n) :
    ∫ ω, y ω i * y ω j * (y ω ⬝ᵥ (M *ᵥ y ω)) ∂P
      = Matrix.trace (Λ * M) * Λ i j + 2 * (Λ * M * Λ) i j :=
  GaussianFoundations.gaussian_quartic_covariance (n := n) (A := A) (M := M) (Λ := Λ) (hΛ := hΛ)
    (hM := hM) (Ω := Ω) (P := P) (y := y) (hy := hy) (hyM := hyM) (i := i) (j := j)

/-- Instance of `isserlis_wick` (sign-SGD #23, #24): for `u ∈ ℝⁿ`, `w ~ N(0, I_n)` and a
coordinate `j`, `E[(uᵀw)² w_j²] = ‖u‖² + 2 u_j²`. -/
theorem gaussian_weighted_square_moment (n : ℕ) (u : Fin n → ℝ) (j : Fin n) :
    ∫ w, (u ⬝ᵥ w) ^ 2 * w j ^ 2 ∂(stdGaussianPi n)
      = (∑ a, u a ^ 2) + 2 * u j ^ 2 :=
  GaussianFoundations.gaussian_weighted_square_moment (n := n) (u := u) (j := j)

/-- Instance of `isserlis_wick` (sign-SGD #23): for `u ∈ ℝⁿ`, `w ~ N(0, I_n)` and a coordinate
`j`, `E[(uᵀw) w_j] = u_j`. -/
theorem gaussian_weighted_linear_moment (n : ℕ) (u : Fin n → ℝ) (j : Fin n) :
    ∫ w, (u ⬝ᵥ w) * w j ∂(stdGaussianPi n) = u j :=
  GaussianFoundations.gaussian_weighted_linear_moment (n := n) (u := u) (j := j)

/-! ## Sheppard's arcsine law -/

/-- Sheppard's formula (cited result `SheppardArcsine`, L-0.6b).

Let `(g, h)` be a jointly Gaussian pair of real random variables on a probability space, with
`E g = E h = 0`, `E g² = E h² = 1`, `E[g h] = ρ` and `ρ ∈ [-1, 1]`. Then
`P(sign g ≠ sign h) = arccos ρ / π`. The law of `(g, h)` is `N(0, [[1, ρ], [ρ, 1]])`, so the
statement depends only on `ρ`. -/
theorem sheppard_arcsine {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g h : Ω → ℝ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (-1 : ℝ) 1)
    (hlaw : HasGaussianLaw (fun ω => (g ω, h ω)) P)
    (hmean_g : ∫ ω, g ω ∂P = 0) (hmean_h : ∫ ω, h ω ∂P = 0)
    (hvar_g : ∫ ω, g ω ^ 2 ∂P = 1) (hvar_h : ∫ ω, h ω ^ 2 ∂P = 1)
    (hcov : ∫ ω, g ω * h ω ∂P = ρ) :
    P.real {ω | SignType.sign (g ω) ≠ SignType.sign (h ω)} = Real.arccos ρ / Real.pi :=
  GaussianFoundations.sheppard_arcsine (Ω := Ω) (P := P) (g := g) (h := h) (ρ := ρ) (hρ := hρ)
    (hlaw := hlaw) (hmean_g := hmean_g) (hmean_h := hmean_h) (hvar_g := hvar_g) (hvar_h := hvar_h)
    (hcov := hcov)

/-! ## Null zero sets of polynomials -/

/-- The zero set of a nonzero real multivariate polynomial is Lebesgue-null (cited result
`PolyZeroSetNull`, L-0.6b).

If `p ∈ ℝ[x₁, …, x_d]` is not the zero polynomial, then `{x | p(x) = 0}` has Lebesgue measure
zero on `Fin d → ℝ`; hence it is null for every measure `μ ≪ volume` and in particular for the
product Gaussian `stdGaussianPi d`. -/
theorem poly_zero_set_null (d : ℕ) (p : MvPolynomial (Fin d) ℝ) (hp : p ≠ 0) :
    volume {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0 ∧
    (∀ μ : Measure (Fin d → ℝ), μ ≪ volume →
        μ {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0) ∧
    stdGaussianPi d {x : Fin d → ℝ | MvPolynomial.eval x p = 0} = 0 :=
  GaussianFoundations.poly_zero_set_null (d := d) (p := p) (hp := hp)

end Muon.Foundations
