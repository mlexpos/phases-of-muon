import GaussianFoundations.Moments
import Mathlib

/-!
# Foundations: standard Gaussian facts (task L-0.5a)

Uncited standard facts about the standard Gaussian law `gaussianReal 0 1` on `ℝ` and about the
standard Gaussian vector `stdGaussianPi n` on `Fin n → ℝ`, used by the appendix sections
(B `eqn:app-de-erfc`, G `L-G.1`, H `L-H.0`, I `L-I.0a`). Source of record: snapshot `cr-2026-10-22`.

Stein's lemma (`GaussianIBP`) is proved here, not certified (`EXTERNAL-RESULTS.md`).

Every theorem below is a statement only (`sorry`); proof routes are in the interface JSON.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Muon.Foundations

/-- Standard Gaussian vector in `ℝⁿ`: coordinates i.i.d. `N(0,1)`. -/
noncomputable def stdGaussianPi (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => gaussianReal 0 1

lemma stdGaussianPi_eq_foundations (n : ℕ) :
    stdGaussianPi n = GaussianFoundations.stdGaussianPi n := rfl

instance (n : ℕ) : IsProbabilityMeasure (stdGaussianPi n) := by
  unfold stdGaussianPi
  infer_instance

/-- Complementary error function, as used in Appendix B:
`erfc x = (2/√π) ∫_x^∞ exp(-t²) dt`. Mathlib has no `erfc`. -/
noncomputable def erfc (x : ℝ) : ℝ :=
  (2 / Real.sqrt Real.pi) * ∫ t in Set.Ioi x, Real.exp (-t ^ 2)

lemma erfc_eq_foundations (x : ℝ) : erfc x = GaussianFoundations.erfc x := rfl

/-! ## Scalar moments of `gaussianReal 0 1` -/

/-- Card P1. Even moments: `E g^{2k} = (2k-1)!!`. -/
theorem gaussian_moment_even (k : ℕ) :
    ∫ x, x ^ (2 * k) ∂(gaussianReal 0 1) = (((2 * k - 1).doubleFactorial : ℕ) : ℝ) :=
  GaussianFoundations.gaussian_moment_even (k := k)

/-- Card P1. Odd moments vanish: `E g^{2k+1} = 0`. -/
theorem gaussian_moment_odd (k : ℕ) :
    ∫ x, x ^ (2 * k + 1) ∂(gaussianReal 0 1) = 0 :=
  GaussianFoundations.gaussian_moment_odd (k := k)

/-- Card P1. Every monomial is integrable against `gaussianReal 0 1`. -/
theorem gaussian_integrable_pow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 1) :=
  GaussianFoundations.gaussian_integrable_pow (n := n)

/-- Card P1. Every monomial lies in `L^p` for every finite `p`. -/
theorem gaussian_memLp_pow (n : ℕ) (p : ℝ≥0∞) (hp : p ≠ ∞) :
    MemLp (fun x : ℝ => x ^ n) p (gaussianReal 0 1) :=
  GaussianFoundations.gaussian_memLp_pow (n := n) (p := p) (hp := hp)

/-- Card P2. `E g² = 1`. -/
theorem gaussian_moment_two : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 :=
  GaussianFoundations.gaussian_moment_two

/-- Card P2. `E g⁴ = 3`. -/
theorem gaussian_moment_four : ∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3 :=
  GaussianFoundations.gaussian_moment_four

/-- Card P2. `E g⁶ = 15`. -/
theorem gaussian_moment_six : ∫ x, x ^ 6 ∂(gaussianReal 0 1) = 15 :=
  GaussianFoundations.gaussian_moment_six

/-- Card P2. `E g⁸ = 105`. -/
theorem gaussian_moment_eight : ∫ x, x ^ 8 ∂(gaussianReal 0 1) = 105 :=
  GaussianFoundations.gaussian_moment_eight

/-- Card P3. `E (g² - 1)² = 2`. -/
theorem gaussian_sq_sub_one_moment_two :
    ∫ x, (x ^ 2 - 1) ^ 2 ∂(gaussianReal 0 1) = 2 :=
  GaussianFoundations.gaussian_sq_sub_one_moment_two

/-- Card P3. `E (g² - 1)⁴ = 60`. -/
theorem gaussian_sq_sub_one_moment_four :
    ∫ x, (x ^ 2 - 1) ^ 4 ∂(gaussianReal 0 1) = 60 :=
  GaussianFoundations.gaussian_sq_sub_one_moment_four

/-- Card P3. First absolute moment: `E|g| = √(2/π)`. -/
theorem gaussian_abs_moment :
    ∫ x, |x| ∂(gaussianReal 0 1) = Real.sqrt (2 / Real.pi) :=
  GaussianFoundations.gaussian_abs_moment

/-- Card P4. `E|g|^{-1/2} = 2^{-1/4} Γ(1/4) / √π`, with real power `|x| ^ (-(1/2))`. -/
theorem gaussian_neg_half_abs_moment :
    ∫ x, |x| ^ (-(1 / 2 : ℝ)) ∂(gaussianReal 0 1)
      = (2 : ℝ) ^ (-(1 / 4 : ℝ)) * Real.Gamma (1 / 4 : ℝ) / Real.sqrt Real.pi :=
  GaussianFoundations.gaussian_neg_half_abs_moment

/-- Card P4. Laplace transform of `g²`: for `t ≥ 0`, `E e^{-t g²} = (1 + 2t)^{-1/2}`. -/
theorem gaussian_laplace (t : ℝ) (ht : 0 ≤ t) :
    ∫ x, Real.exp (-t * x ^ 2) ∂(gaussianReal 0 1) = (1 + 2 * t) ^ (-(1 / 2 : ℝ)) :=
  GaussianFoundations.gaussian_laplace (t := t) (ht := ht)

/-- Card P4. Completed-square MGF: for `λ ≥ 0`, `σ, c ∈ ℝ`,
`E exp(-λ(σg + c)²/2) = (1 + λσ²)^{-1/2} exp(-λc² / (2(1 + λσ²)))`. -/
theorem gaussian_completed_square (lam σ c : ℝ) (hlam : 0 ≤ lam) :
    ∫ x, Real.exp (-lam * (σ * x + c) ^ 2 / 2) ∂(gaussianReal 0 1)
      = (1 + lam * σ ^ 2) ^ (-(1 / 2 : ℝ))
        * Real.exp (-lam * c ^ 2 / (2 * (1 + lam * σ ^ 2))) :=
  GaussianFoundations.gaussian_completed_square (lam := lam) (σ := σ) (c := c) (hlam := hlam)

/-- Card P4. Density bound: `φ(x) ≤ 1/√(2π)` for the standard normal density. -/
theorem gaussian_pdf_le (x : ℝ) :
    gaussianPDFReal 0 1 x ≤ 1 / Real.sqrt (2 * Real.pi) :=
  GaussianFoundations.gaussian_pdf_le (x := x)

/-! ## Stein's lemma (proved here; `GaussianIBP`) -/

/-- Stein's lemma for `g ~ N(0,1)`: for `φ ∈ C¹(ℝ)` with `φ` and `φ'` bounded by
polynomials, `E[g φ(g)] = E[φ'(g)]`. -/
theorem gaussian_stein (φ : ℝ → ℝ) (hφ : ContDiff ℝ 1 φ)
    (hφb : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |φ x| ≤ C * (1 + |x| ^ k))
    (hdb : ∃ C : ℝ, ∃ k : ℕ, ∀ x : ℝ, |deriv φ x| ≤ C * (1 + |x| ^ k)) :
    ∫ x, x * φ x ∂(gaussianReal 0 1) = ∫ x, deriv φ x ∂(gaussianReal 0 1) :=
  GaussianFoundations.gaussian_stein (φ := φ) (hφ := hφ) (hφb := hφb) (hdb := hdb)

/-! ## The identity of Appendix B, `eqn:app-de-erfc` -/

/-- Card P6. Appendix B `eqn:app-de-erfc`, first equality (`q J(q) = E[qg²/(1+qg²)]`,
`J(x) = E g²/(1+xg²)`): for `q > 0` and `ξ = (2q)^{-1/2}`,
`E[qg²/(1+qg²)] = E[g²/(g²+2ξ²)]`. -/
theorem app_de_nomomentum_ratio (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    ∫ g, q * g ^ 2 / (1 + q * g ^ 2) ∂(gaussianReal 0 1)
      = ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1) :=
  GaussianFoundations.gaussian_ratio_eq_erfc_integrand (q := q) (ξ := ξ) (hq := hq) (hξ := hξ)

/-- Card P6. Appendix B `eqn:app-de-erfc`, second equality: for `q > 0` and `ξ = (2q)^{-1/2}`,
`E[g²/(g²+2ξ²)] = 1 - √π ξ e^{ξ²} erfc(ξ)`. -/
theorem app_de_nomomentum_erfc (q ξ : ℝ) (hq : 0 < q) (hξ : ξ = (2 * q) ^ (-(1 / 2 : ℝ))) :
    ∫ g, g ^ 2 / (g ^ 2 + 2 * ξ ^ 2) ∂(gaussianReal 0 1)
      = 1 - Real.sqrt Real.pi * ξ * Real.exp (ξ ^ 2) * erfc ξ :=
  GaussianFoundations.gaussian_erfc_integrand_eq (q := q) (ξ := ξ) (hq := hq) (hξ := hξ)

/-! ## Standard Gaussian vector `g ~ stdGaussianPi n` -/

/-- Card P7. Each coordinate of `g` is `N(0,1)`. -/
theorem stdGaussianPi_map_coord (n : ℕ) (i : Fin n) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => z i) = gaussianReal 0 1 :=
  GaussianFoundations.stdGaussianPi_map_coord (n := n) (i := i)

/-- Card P7. `E‖g‖^{2q} = d_q(n) = n(n+2)⋯(n+2q-2)` for `q ≥ 1`, where `‖g‖² = ∑ g_i²`. -/
theorem stdGaussianPi_sq_norm_moment (n q : ℕ) (hq : 1 ≤ q) :
    ∫ z : Fin n → ℝ, (∑ i, z i ^ 2) ^ q ∂(stdGaussianPi n)
      = ∏ j ∈ Finset.range q, ((n : ℝ) + 2 * (j : ℝ)) :=
  GaussianFoundations.stdGaussianPi_sq_norm_moment (n := n) (q := q) (hq := hq)

/-- Card P7. For `i ≠ j`, `E|g_i g_j| = 2/π`. -/
theorem stdGaussianPi_abs_mul_coord (n : ℕ) (i j : Fin n) (hij : i ≠ j) :
    ∫ z : Fin n → ℝ, |z i * z j| ∂(stdGaussianPi n) = 2 / Real.pi :=
  GaussianFoundations.stdGaussianPi_abs_mul_coord (n := n) (i := i) (j := j) (hij := hij)

/-- Card P7. Linear functionals: `∑_i g_i u_i ~ N(0, ‖u‖²)`. -/
theorem stdGaussianPi_linear_map (n : ℕ) (u : Fin n → ℝ) :
    (stdGaussianPi n).map (fun z : Fin n → ℝ => ∑ i, z i * u i)
      = gaussianReal 0 (Real.toNNReal (∑ i, u i ^ 2)) :=
  GaussianFoundations.stdGaussianPi_linear_map (n := n) (u := u)

/-- Card P8. Conditional Gaussian lemma. For `Δ ∈ ℝ^{n×m}`, measurable `f : ℝ → ℝ`, and
`g ~ N(0,I_n)`, `h ~ N(0,I_m)`: integrating over `z` first for fixed `w` gives a
`N(0, ‖Δw‖²)` law, i.e. `E_w E_z f(zᵀΔw) = E_w E_{x~N(0,‖Δw‖²)} f(x)`. -/
theorem stdGaussian_conditional_linear (n m : ℕ) (Δ : Matrix (Fin n) (Fin m) ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ w : Fin m → ℝ, (∫ z : Fin n → ℝ, f (∑ i, z i * (Δ.mulVec w) i) ∂(stdGaussianPi n))
        ∂(stdGaussianPi m)
      = ∫ w : Fin m → ℝ,
          (∫ x, f x ∂(gaussianReal 0 (Real.toNNReal (∑ i, (Δ.mulVec w) i ^ 2))))
          ∂(stdGaussianPi m) :=
  GaussianFoundations.stdGaussian_conditional_linear (n := n) (m := m) (Δ := Δ) (f := f) (hf := hf)

/-- Card P8. Quadratic form mean: `E[gᵀMg] = tr M` for any real matrix `M`. -/
theorem stdGaussianPi_quadratic_mean (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) :
    ∫ z : Fin n → ℝ, ∑ i, ∑ j, z i * M i j * z j ∂(stdGaussianPi n) = M.trace :=
  GaussianFoundations.stdGaussianPi_quadratic_mean (n := n) (M := M)

/-- Card P8. Quadratic form variance: for symmetric `M`,
`Var(gᵀMg) = 2 tr(M²)`. -/
theorem stdGaussianPi_quadratic_variance (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.transpose = M) :
    ∫ z : Fin n → ℝ, (∑ i, ∑ j, z i * M i j * z j - M.trace) ^ 2 ∂(stdGaussianPi n)
      = 2 * (M * M).trace :=
  GaussianFoundations.stdGaussianPi_quadratic_variance (n := n) (M := M) (hM := hM)

end Muon.Foundations
