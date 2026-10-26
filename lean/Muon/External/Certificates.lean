import Mathlib

/-!
# Certificates for cited results (L-0.4)

Each structure below states one cited result exactly as a consuming card needs it. The structures
are taken as explicit arguments by their consumers (CAMPAIGN section 5); no axioms. Registered in
`phases-of-muon/appendix-nodes/EXTERNAL-RESULTS.md`.

Conventions shared by the certificates:
* Gaussian laws are Mathlib's `gaussianReal 0 1`, `Measure.pi`, and `stdGaussian`.
* The operator norm of a real rectangular matrix is the operator norm of the induced linear map
  between Euclidean spaces (`matOpNorm`); no matrix norm instance is used.
* The matrix exponential is Mathlib's `NormedSpace.exp`, which needs only the topological
  `ℚ`-algebra structure of `Matrix`; no norm instance and no local instance is used.
* Constants are existentially quantified before the dimension.
-/

namespace Muon.External

open MeasureTheory ProbabilityTheory
open scoped ENNReal ComplexOrder

/-- Operator norm of a real `p × q` matrix, as the operator norm of the induced linear map
`EuclideanSpace ℝ (Fin q) → EuclideanSpace ℝ (Fin p)`. -/
noncomputable def matOpNorm {p q : ℕ} (Y : Matrix (Fin p) (Fin q) ℝ) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y)‖

/-- Frobenius norm `‖F‖_F = (∑ᵢⱼ |Fᵢⱼ|²)^{1/2}` of a real square matrix. -/
noncomputable def frobNorm {n : ℕ} (F : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ j, F i j ^ 2)

/-- `Y` is an i.i.d. `N(0,1)` matrix under `μ`: the law of its entries, vectorised, is the
product of `p * q` copies of `gaussianReal 0 1`. -/
def IsIIDGaussianMatrix {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {p q : ℕ}
    (Y : Ω → Matrix (Fin p) (Fin q) ℝ) : Prop :=
  μ.map (fun ω (ij : Fin p × Fin q) => Y ω ij.1 ij.2) =
    Measure.pi (fun _ : Fin p × Fin q => gaussianReal 0 1)

/-- `z` is a standard Gaussian vector `N(0, Id_n)` under `μ`: its law is the product of `n`
copies of `gaussianReal 0 1`. -/
def IsStdGaussianVector {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {n : ℕ}
    (z : Ω → Fin n → ℝ) : Prop :=
  μ.map z = Measure.pi (fun _ : Fin n => gaussianReal 0 1)

/-- Gaussian operator-norm tail bound, Gaussian case.

Source: Vershynin, *High-Dimensional Probability* (2018), Thm 4.4.5 (Gaussian case).
Consumers (volatility card, §4): `lem:app-vol-inner` (l.1004), `lem:app-vol-product-kernel`
(l.1241), `lem:app-vol-norm` (l.1975) and, through `lem:app-vol-norm`, G. Dynamics card:
`lem:app-dyn-batch`(ii) in its tail form. The statement is the tail form; the `L^6` form is
`GaussianOpNormL6`.

There is an absolute constant `C₀ > 0` such that for all `p q : ℕ`, every `t ≥ 0` and every
i.i.d. `N(0,1)` matrix `Y ∈ ℝ^{p×q}`, `P(‖Y‖_op > C₀(√p + √q + t)) ≤ 2 e^{-t²}`. -/
structure GaussianOpNorm : Prop where
  holds : ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ p q : ℕ, ∀ t : ℝ, 0 ≤ t →
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → Matrix (Fin p) (Fin q) ℝ),
      IsIIDGaussianMatrix μ Y →
        μ {ω | C₀ * (Real.sqrt p + Real.sqrt q + t) < matOpNorm (Y ω)}
          ≤ ENNReal.ofReal (2 * Real.exp (-(t ^ 2)))

/-- Gaussian operator-norm `L^6` bound, Gaussian case.

Source: Vershynin, *High-Dimensional Probability* (2018), Thm 4.4.5 (Gaussian case), integrated
in the `L^6` form.
Consumer (dynamics card, §4): `lem:app-dyn-batch`(ii), where it is consumed as
`‖ ‖G‖ ‖_{L^6} ≤ C(√N + √B)`.

There is an absolute constant `C > 0` such that for all `p q : ℕ` and every i.i.d. `N(0,1)`
matrix `Y ∈ ℝ^{p×q}`, `‖ ‖Y‖_op ‖_{L^6} ≤ C(√p + √q)`. -/
structure GaussianOpNormL6 : Prop where
  holds : ∃ C : ℝ, 0 < C ∧ ∀ p q : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (Y : Ω → Matrix (Fin p) (Fin q) ℝ),
      IsIIDGaussianMatrix μ Y →
        eLpNorm (fun ω => matOpNorm (Y ω)) 6 μ
          ≤ ENNReal.ofReal (C * (Real.sqrt p + Real.sqrt q))

/-- Gaussian Hanson–Wright moment bound, Gaussian case.

Source: Vershynin, *High-Dimensional Probability* (2018), Thm 6.2.1 (Hanson–Wright), Gaussian case.
Consumer (dynamics card, §4): `lem:app-dyn-coefficients`.

For every `p ≥ 1` there is a constant `C_p` such that for every `n`, every standard Gaussian vector
`z ~ N(0, Id_n)` and every deterministic `F ∈ ℝ^{n×n}`,
`‖zᵀ F z − Tr F‖_{L^p} ≤ C_p ‖F‖_F`. The constant `C_p` depends only on `p`. -/
structure GaussianQuadFormLp : Prop where
  holds : ∀ p : ℝ, 1 ≤ p → ∃ Cp : ℝ, ∀ n : ℕ,
    ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (z : Ω → Fin n → ℝ),
      IsStdGaussianVector μ z →
      ∀ F : Matrix (Fin n) (Fin n) ℝ,
        eLpNorm (fun ω => dotProduct (z ω) (Matrix.mulVec F (z ω)) - Matrix.trace F)
            (ENNReal.ofReal p) μ
          ≤ ENNReal.ofReal (Cp * frobNorm F)

/-- Gaussian Poincaré inequality.

Source: Boucheron, Lugosi, Massart, *Concentration Inequalities* (2013), Thm 3.20.
Consumer (dynamics card, §4): `lem:app-dyn-poincare`.

For every `n`, every `f ∈ C¹(ℝⁿ)` and standard Gaussian `g` on `ℝⁿ` with
`E‖∇f(g)‖² < ∞`, `Var f(g) ≤ E‖∇f(g)‖²`. The gradient norm is `‖fderiv ℝ f x‖`, which equals
the Euclidean norm of `∇f(x)` on `EuclideanSpace ℝ (Fin n)`. The variance is the extended-valued
`evariance`, so no junk value enters. -/
structure GaussianPoincare : Prop where
  holds : ∀ n : ℕ, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
    ContDiff ℝ 1 f →
    ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin n))) < ⊤ →
      evariance f (stdGaussian (EuclideanSpace ℝ (Fin n)))
        ≤ ∫⁻ x, ‖fderiv ℝ f x‖ₑ ^ 2 ∂(stdGaussian (EuclideanSpace ℝ (Fin n)))

end Muon.External
