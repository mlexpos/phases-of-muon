import Mathlib
import Muon.SignSGD.Defs
import Muon.SignSGD.ShiftArcsine
import Muon.Foundations.GaussianExtra
import Muon.Foundations.OrthHaar

/-!
# Appendix I (SignSGD): Haar tools (task L-I.8)

Interface for `lem:app-sgd-sphere` (theorems `_i`–`_v`: the four conjuncts of the paper plus its
"in particular" bound), `lem:app-sgd-haar-sign` (`_i` fixed `a`, `_ii` conditional on a random
`a`) and `prop:app-sgd-one-sample` (one theorem, two conjuncts). Source of record: snapshot
`cr-2026-10-23`, `sections/08-signsgd/section.tex` l. 663–678, 708–715, 742–751. Docstrings carry
the LaTeX statement verbatim (copied by script).

Choices (recorded in the result JSON `open_questions`):
* Haar measure: a probability `ν` on `O(n)` with `Muon.Foundations.IsOrthHaar ν` (Q1, option (b)).
* Uniform law on the sphere: `Muon.Foundations.sphereGauss n` (law of `g/‖g‖`).
* Standard Gaussian vector: `Muon.Foundations.stdGaussianPi n`.
* `lem:app-sgd-sphere`(v) takes `0 ≤ c` in addition to the paper's hypotheses. Without it the
  bound `≤ 60 L⁴/n²` is false (eigenvalues `-3` and `1` in equal numbers, `L = 1`, `n = 100`).
* `lem:app-sgd-haar-sign` is stated entrywise (`Y ⊗ Y` has no `Matrix`-valued integral here).
* In `lem:app-sgd-haar-sign`(ii) and `prop:app-sgd-one-sample`, the fresh whitened batch is
  `(Z, W)` with the product Gaussian law, independent of `U` (`IndepFun`); `Xout = U Λ^{1/2} z`,
  `Xin = w` (`oneSampleBatch`). The state is `Δ = Δfun (U)` with `Δfun` measurable.
* `u_i := U e_i`, written as the `i`-th column `(U ω) k i`.
-/

open MeasureTheory ProbabilityTheory
open Muon.Foundations

namespace Muon.SignSGD

/-- `d_q(n) = n(n+2)⋯(n+2q-2)` (the paper's `d_q(n)`, l. 661), as a product over `range q`. -/
noncomputable def dq (n q : ℕ) : ℝ := ∏ r ∈ Finset.range q, ((n : ℝ) + 2 * (r : ℝ))

/-- Entrywise arcsine matrix `Σ^{sign}_{kl} = (2/π) arcsin(Σ_{kl}/√(Σ_{kk}Σ_{ll}))`
(`lem:app-sgd-haar-sign`/`prop:app-sgd-one-sample`, l. 749). -/
noncomputable def sigmaSignMat {n : ℕ} (Sg : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun k l => (2 / Real.pi) * Real.arcsin (Sg k l / Real.sqrt (Sg k k * Sg l l))

/-- The Haar sign row `Y = Uᵀ sign(U a)` of `lem:app-sgd-haar-sign` (l. 709–711). -/
noncomputable def haarSignY {n : ℕ} (a : Fin n → ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    Fin n → ℝ :=
  Matrix.mulVec (Matrix.transpose (U : Matrix (Fin n) (Fin n) ℝ))
    (fun k => Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k))

/-- One-sample batch of `prop:app-sgd-one-sample`: `Xin = w`, `Xout = U Λ^{1/2} z` with
`Λ^{1/2} = diag(√μ)`. -/
noncomputable def oneSampleBatch {n m : ℕ} (μ : Fin n → ℝ) (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (z : Fin n → ℝ) (w : Fin m → ℝ) : Batch n m 1 :=
  { xin := fun _ => w
    xout := fun _ => Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ)
      (fun k => Real.sqrt (μ k) * z k) }

/-- The one-step sign matrix `S = sign(G°)` of `def:app-sgd-update` for the one-sample batch. -/
noncomputable def oneSampleSign {n m : ℕ} (Δ : Matrix (Fin n) (Fin m) ℝ) (β : Batch n m 1) :
    Matrix (Fin n) (Fin m) ℝ :=
  (physGrad Δ β).map Real.sign

/-! ## `lem:app-sgd-sphere` -/

/-- Radius–direction split: for a measurable `h` vanishing at `0` and `k`-homogeneous on
`(0, ∞)`, `E h(g) = E‖g‖^k · E h(g/‖g‖)` for the standard Gaussian `g`. -/
private lemma app_sphere_split (n k : ℕ) (h : (Fin n → ℝ) → ℝ) (hm : Measurable h)
    (hh0 : h 0 = 0) (hhom : ∀ c : ℝ, 0 < c → ∀ z, h (c • z) = c ^ k * h z) :
    ∫ z, h z ∂(stdGaussianPi n)
      = (∫ z, euclidNorm n z ^ k ∂(stdGaussianPi n)) * ∫ v, h v ∂(sphereGauss n) := by
  have hR : Measurable (euclidNorm n) := by unfold euclidNorm; fun_prop
  have hΨ : Measurable (fun z : Fin n → ℝ => (euclidNorm n z, (euclidNorm n z)⁻¹ • z)) :=
    hR.prodMk (hR.inv.smul measurable_id)
  have hpt : ∀ z : Fin n → ℝ, euclidNorm n z ^ k * h ((euclidNorm n z)⁻¹ • z) = h z := by
    intro z
    by_cases hz : euclidNorm n z = 0
    · have hz0 : z = 0 := by
        have hs : ∑ i, z i ^ 2 = 0 := by
          unfold euclidNorm at hz
          rwa [Real.sqrt_eq_zero (Finset.sum_nonneg fun i _ => sq_nonneg _)] at hz
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).1 hs i
          (Finset.mem_univ i)
        exact (pow_eq_zero_iff two_ne_zero).1 this
      subst hz0
      simp [hz, hh0]
    · have hc : 0 < euclidNorm n z :=
        lt_of_le_of_ne (by unfold euclidNorm; exact Real.sqrt_nonneg _) (Ne.symm hz)
      rw [hhom _ (inv_pos.2 hc), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow,
        one_mul]
  have hF : Measurable (fun p : ℝ × (Fin n → ℝ) => p.1 ^ k * h p.2) :=
    (measurable_fst.pow_const k).mul (hm.comp measurable_snd)
  calc ∫ z, h z ∂(stdGaussianPi n)
      = ∫ z, euclidNorm n z ^ k * h ((euclidNorm n z)⁻¹ • z) ∂(stdGaussianPi n) := by
        congr 1; funext z; exact (hpt z).symm
    _ = ∫ p, p.1 ^ k * h p.2 ∂((stdGaussianPi n).map
          (fun z : Fin n → ℝ => (euclidNorm n z, (euclidNorm n z)⁻¹ • z))) := by
        rw [integral_map hΨ.aemeasurable hF.aestronglyMeasurable]
    _ = ∫ p, p.1 ^ k * h p.2 ∂(((stdGaussianPi n).map (euclidNorm n)).prod (sphereGauss n)) := by
        rw [stdGaussianPi_radius_direction_indep n]
    _ = (∫ r, r ^ k ∂((stdGaussianPi n).map (euclidNorm n))) * ∫ v, h v ∂(sphereGauss n) :=
        integral_prod_mul (fun r : ℝ => r ^ k) h
    _ = _ := by
        rw [integral_map hR.aemeasurable (by fun_prop : Measurable fun r : ℝ => r ^ k).aestronglyMeasurable]

/-- Part (i) of `lem:app-sgd-sphere` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Spherical moments]\label{lem:app-sgd-sphere}
Let $v$ be uniform on the unit sphere of $\R^n$, $n\ge2$. Then
\begin{equation}\label{eqn:app-sgd-l1}
\EE\norm v_1^2=1+\frac{2(n-1)}\pi .
\end{equation}
For a vector $a$, a positive semidefinite $T$ and an integer $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-sphere}
\EE\abs{v^\T a}^{2q}=\frac{(2q-1)!!\,\norm a^{2q}}{d_q(n)},\qquad \EE\big(v^\T Tv\big)^q\le\frac{(2q-1)!!\,(\Tr T)^q}{d_q(n)}.
\end{equation}
For symmetric $H$ with $\Tr H=0$,
\begin{equation}\label{eqn:app-sgd-sphere-four}
\EE\big(v^\T Hv\big)^4=\frac{12(\Tr H^2)^2+48\Tr H^4}{d_4(n)} .
\end{equation}
In particular, if $c\Id\preceq\Lambda\preceq L\Id$ in dimension $n$ and
$\bar\mu=\Tr\Lambda/n$, then $\EE(v^\T\Lambda v-\bar\mu)^4\le60L^4/n^2$.
\end{lemma}
```
-/
theorem lem_app_sgd_sphere_i (n : ℕ) (hn : 2 ≤ n) :
    ∫ v, (∑ i, |v i|) ^ 2 ∂(sphereGauss n) = 1 + 2 * ((n : ℝ) - 1) / Real.pi := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have hm : Measurable (fun z : Fin n → ℝ => (∑ i, |z i|) ^ 2) := by fun_prop
  have hsplit : ∫ z, (∑ i, |z i|) ^ 2 ∂(stdGaussianPi n)
      = (∫ z, euclidNorm n z ^ 2 ∂(stdGaussianPi n)) *
        ∫ v, (∑ i, |v i|) ^ 2 ∂(sphereGauss n) :=
    app_sphere_split n 2 _ hm (by simp) (by
      intro c hc z
      simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum]
      ring)
  have hR2 : ∫ z, euclidNorm n z ^ 2 ∂(stdGaussianPi n) = n := by
    have e : ∀ z : Fin n → ℝ, euclidNorm n z ^ 2 = ∑ i, z i ^ 2 := fun z => by
      unfold euclidNorm
      exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
    simp only [e]
    have := stdGaussianPi_sq_norm_moment n 1 le_rfl
    simpa using this
  have hcoord2 : ∀ i : Fin n, ∫ z, z i ^ 2 ∂(stdGaussianPi n) = 1 := by
    intro i
    calc ∫ z, z i ^ 2 ∂(stdGaussianPi n)
        = ∫ x, x ^ 2 ∂((stdGaussianPi n).map (fun z : Fin n → ℝ => z i)) := by
          rw [integral_map (measurable_pi_apply i).aemeasurable
            (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable]
      _ = ∫ x, x ^ 2 ∂(gaussianReal 0 1) := by rw [stdGaussianPi_map_coord]
      _ = 1 := gaussian_moment_two
  have hint2 : ∀ i : Fin n, Integrable (fun z : Fin n → ℝ => z i ^ 2) (stdGaussianPi n) := by
    intro i
    have h1 : Integrable (fun x : ℝ => x ^ 2)
        ((stdGaussianPi n).map (fun z : Fin n → ℝ => z i)) := by
      rw [stdGaussianPi_map_coord]
      exact gaussian_integrable_pow 2
    exact (integrable_map_measure (by fun_prop : Measurable fun x : ℝ => x ^ 2).aestronglyMeasurable
      (measurable_pi_apply i).aemeasurable).1 h1
  have hterm : ∀ i j : Fin n,
      ∫ z, |z i| * |z j| ∂(stdGaussianPi n) = if i = j then 1 else 2 / Real.pi := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl]
      simp_rw [abs_mul_abs_self, ← sq]
      exact hcoord2 i
    · rw [if_neg hij, ← stdGaussianPi_abs_mul_coord n i j hij]
      simp only [abs_mul]
  have hintT : ∀ i j : Fin n, Integrable (fun z : Fin n → ℝ => |z i| * |z j|) (stdGaussianPi n) := by
    intro i j
    refine Integrable.mono' (((hint2 i).add (hint2 j)).div_const 2)
      (by fun_prop : Measurable fun z : Fin n → ℝ => |z i| * |z j|).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (z i), sq_abs (z j), sq_nonneg (|z i| - |z j|)]
  have hsum : ∫ z, (∑ i, |z i|) ^ 2 ∂(stdGaussianPi n)
      = ∑ i, ∑ j, ∫ z, |z i| * |z j| ∂(stdGaussianPi n) := by
    have hpt : (fun z : Fin n → ℝ => (∑ i, |z i|) ^ 2)
        = fun z => ∑ i, ∑ j, |z i| * |z j| := by
      funext z
      rw [sq, Finset.sum_mul_sum]
    rw [hpt, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hintT i j))]
    congr 1
    funext i
    rw [integral_finset_sum _ (fun j _ => hintT i j)]
  have hval : ∫ z, (∑ i, |z i|) ^ 2 ∂(stdGaussianPi n)
      = n * (n * (2 / Real.pi) + (1 - 2 / Real.pi)) := by
    rw [hsum]
    simp_rw [hterm]
    have key : ∀ i j : Fin n, (if i = j then (1 : ℝ) else 2 / Real.pi)
        = 2 / Real.pi + (if i = j then 1 - 2 / Real.pi else 0) := by
      intro i j
      split_ifs <;> ring
    simp [key, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    ring
  rw [hR2, hval] at hsplit
  apply mul_left_cancel₀ hn0
  rw [← hsplit]
  ring

/-- Part (ii) of `lem:app-sgd-sphere` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Spherical moments]\label{lem:app-sgd-sphere}
Let $v$ be uniform on the unit sphere of $\R^n$, $n\ge2$. Then
\begin{equation}\label{eqn:app-sgd-l1}
\EE\norm v_1^2=1+\frac{2(n-1)}\pi .
\end{equation}
For a vector $a$, a positive semidefinite $T$ and an integer $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-sphere}
\EE\abs{v^\T a}^{2q}=\frac{(2q-1)!!\,\norm a^{2q}}{d_q(n)},\qquad \EE\big(v^\T Tv\big)^q\le\frac{(2q-1)!!\,(\Tr T)^q}{d_q(n)}.
\end{equation}
For symmetric $H$ with $\Tr H=0$,
\begin{equation}\label{eqn:app-sgd-sphere-four}
\EE\big(v^\T Hv\big)^4=\frac{12(\Tr H^2)^2+48\Tr H^4}{d_4(n)} .
\end{equation}
In particular, if $c\Id\preceq\Lambda\preceq L\Id$ in dimension $n$ and
$\bar\mu=\Tr\Lambda/n$, then $\EE(v^\T\Lambda v-\bar\mu)^4\le60L^4/n^2$.
\end{lemma}
```
-/
theorem lem_app_sgd_sphere_ii (n q : ℕ) (hn : 2 ≤ n) (hq : 1 ≤ q ∧ q ≤ 4)
    (a : Fin n → ℝ) :
    ∫ v, |dotProduct v a| ^ (2 * q) ∂(sphereGauss n)
      = ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * euclidNorm n a ^ (2 * q) / dq n q := by
  obtain ⟨hq1, _⟩ := hq
  have hS : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have heu : ∀ z : Fin n → ℝ, euclidNorm n z ^ (2 * q) = (∑ i, z i ^ 2) ^ q := by
    intro z
    unfold euclidNorm
    rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  have hnorm : euclidNorm n a ^ (2 * q) = (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * q) := rfl
  have hm : Measurable (fun z : Fin n → ℝ => |dotProduct z a| ^ (2 * q)) := by
    unfold dotProduct; fun_prop
  have h0 : (fun z : Fin n → ℝ => |dotProduct z a| ^ (2 * q)) 0 = 0 := by
    simp [zero_pow (show 2 * q ≠ 0 by omega)]
  have hhom : ∀ c : ℝ, 0 < c → ∀ z : Fin n → ℝ,
      |dotProduct (c • z) a| ^ (2 * q) = c ^ (2 * q) * |dotProduct z a| ^ (2 * q) := by
    intro c hc z
    rw [smul_dotProduct, smul_eq_mul, abs_mul, abs_of_pos hc, mul_pow]
  have hsplit : ∫ z, |dotProduct z a| ^ (2 * q) ∂(stdGaussianPi n)
      = (∫ z, euclidNorm n z ^ (2 * q) ∂(stdGaussianPi n)) *
        ∫ v, |dotProduct v a| ^ (2 * q) ∂(sphereGauss n) :=
    app_sphere_split n (2 * q) _ hm h0 hhom
  have hRmom : ∫ z, euclidNorm n z ^ (2 * q) ∂(stdGaussianPi n) = dq n q := by
    simp_rw [heu]
    unfold dq
    exact stdGaussianPi_sq_norm_moment n q hq1
  have hL : ∫ z, |dotProduct z a| ^ (2 * q) ∂(stdGaussianPi n)
      = ∫ x, |x| ^ (2 * q) ∂(gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2))) := by
    rw [← stdGaussianPi_linear_map n a,
      integral_map (by fun_prop : Measurable fun z : Fin n → ℝ => ∑ i, z i * a i).aemeasurable
        (by fun_prop : Measurable fun x : ℝ => |x| ^ (2 * q)).aestronglyMeasurable]
    rfl
  have hscale : gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2))
      = (gaussianReal 0 1).map (fun y : ℝ => Real.sqrt (∑ i, a i ^ 2) * y) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.coe_toNNReal _ hS, Real.sq_sqrt hS]
  have hmom : ∫ x, |x| ^ (2 * q) ∂(gaussianReal 0 (Real.toNNReal (∑ i, a i ^ 2)))
      = (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * q) * ∫ y, y ^ (2 * q) ∂(gaussianReal 0 1) := by
    rw [hscale, integral_map (measurable_const_mul _).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => |x| ^ (2 * q)).aestronglyMeasurable,
      ← integral_const_mul]
    congr 1
    funext y
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      (even_two_mul q).pow_abs]
  have hI : ∫ z, |dotProduct z a| ^ (2 * q) ∂(stdGaussianPi n)
      = (Real.sqrt (∑ i, a i ^ 2)) ^ (2 * q) * (((2 * q - 1).doubleFactorial : ℕ) : ℝ) := by
    rw [hL, hmom, gaussian_moment_even q]
  have hdq : 0 < dq n q := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold dq
    apply Finset.prod_pos
    intro r _
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  rw [hRmom, hI] at hsplit
  rw [eq_div_iff hdq.ne', hnorm]
  linear_combination (-1 : ℝ) * hsplit

/-- Spectral split of a positive semidefinite `T`: `vᵀTv = ∑_l d_l (u_l·v)²` with eigenvalues
`d_l ≥ 0` and unit eigenvector columns `u_l`, and `Tr T = ∑_l d_l`. -/
private lemma sphere_quad_decomp (n : ℕ) (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosSemidef) :
    ∃ (d : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ), (∀ l, 0 ≤ d l) ∧
      (∀ l, ∑ i, U i l * U i l = 1) ∧
      (∀ v : Fin n → ℝ, dotProduct v (T.mulVec v) = ∑ l, d l * (dotProduct v (fun i => U i l)) ^ 2) ∧
      Matrix.trace T = ∑ l, d l := by
  classical
  have key : ∀ f : Fin n → Fin n → Fin n → ℝ,
      ∑ a, ∑ b, ∑ l, f a b l = ∑ l, ∑ a, ∑ b, f a b l := fun f =>
    calc ∑ a, ∑ b, ∑ l, f a b l = ∑ a, ∑ l, ∑ b, f a b l :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ l, ∑ a, ∑ b, f a b l := Finset.sum_comm
  obtain ⟨d, U, hd0, hUU, hspec⟩ : ∃ (d : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ),
      (∀ l, 0 ≤ d l) ∧ (∀ l, ∑ i, U i l * U i l = 1) ∧
      (∀ i j, T i j = ∑ l, U i l * d l * U j l) := by
    refine ⟨hT.1.eigenvalues, (hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ),
      fun l => hT.eigenvalues_nonneg l, ?_, ?_⟩
    · intro l
      have h1 := Unitary.coe_star_mul_self (hT.1.eigenvectorUnitary)
      have := congrFun (congrFun h1 l) l
      simpa [Matrix.mul_apply, Matrix.star_apply] using this
    · have hMat : T = (hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
          * Matrix.diagonal (RCLike.ofReal ∘ hT.1.eigenvalues)
          * star (hT.1.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) := by
        conv_lhs => rw [hT.1.spectral_theorem]
        rfl
      intro i j
      conv_lhs => rw [hMat]
      rw [Matrix.mul_assoc, Matrix.mul_apply]
      simp only [Matrix.diagonal_mul, Matrix.star_apply, star_trivial, Function.comp_apply,
        RCLike.ofReal_real_eq_id, id]
      exact Finset.sum_congr rfl fun l _ => by ring
  refine ⟨d, U, hd0, hUU, ?_, ?_⟩
  · intro v
    simp only [dotProduct, Matrix.mulVec, hspec, Finset.mul_sum, Finset.sum_mul, pow_two]
    rw [key]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_comm.trans (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_)
    ring
  · simp only [Matrix.trace, Matrix.diag, hspec]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    have h2 : ∑ i, U i l * d l * U i l = (∑ i, U i l * U i l) * d l := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, hUU l, one_mul]

/-- Part (iii) of `lem:app-sgd-sphere` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Spherical moments]\label{lem:app-sgd-sphere}
Let $v$ be uniform on the unit sphere of $\R^n$, $n\ge2$. Then
\begin{equation}\label{eqn:app-sgd-l1}
\EE\norm v_1^2=1+\frac{2(n-1)}\pi .
\end{equation}
For a vector $a$, a positive semidefinite $T$ and an integer $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-sphere}
\EE\abs{v^\T a}^{2q}=\frac{(2q-1)!!\,\norm a^{2q}}{d_q(n)},\qquad \EE\big(v^\T Tv\big)^q\le\frac{(2q-1)!!\,(\Tr T)^q}{d_q(n)}.
\end{equation}
For symmetric $H$ with $\Tr H=0$,
\begin{equation}\label{eqn:app-sgd-sphere-four}
\EE\big(v^\T Hv\big)^4=\frac{12(\Tr H^2)^2+48\Tr H^4}{d_4(n)} .
\end{equation}
In particular, if $c\Id\preceq\Lambda\preceq L\Id$ in dimension $n$ and
$\bar\mu=\Tr\Lambda/n$, then $\EE(v^\T\Lambda v-\bar\mu)^4\le60L^4/n^2$.
\end{lemma}
```
-/
theorem lem_app_sgd_sphere_iii (n q : ℕ) (hn : 2 ≤ n) (hq : 1 ≤ q ∧ q ≤ 4)
    (T : Matrix (Fin n) (Fin n) ℝ) (hT : T.PosSemidef) :
    ∫ v, (dotProduct v (T.mulVec v)) ^ q ∂(sphereGauss n)
      ≤ ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * (Matrix.trace T) ^ q / dq n q := by
  have hq' : 1 ≤ q ∧ q ≤ 4 := hq
  obtain ⟨d, U, hd0, hUU, hquad, htr⟩ := sphere_quad_decomp n T hT
  have hdq : 0 < dq n q := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold dq
    apply Finset.prod_pos
    intro r _
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hfac : (0 : ℝ) < ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.doubleFactorial_pos _
  have hmom : ∀ l, ∫ v, ((dotProduct v (fun i => U i l)) ^ 2) ^ q ∂(sphereGauss n)
      = ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) / dq n q := by
    intro l
    have hnorm : euclidNorm n (fun i => U i l) = 1 := by
      unfold euclidNorm
      rw [show ∑ i, (fun i => U i l) i ^ 2 = 1 by simpa [sq] using hUU l, Real.sqrt_one]
    have hii := lem_app_sgd_sphere_ii n q hn hq' (fun i => U i l)
    rw [hnorm, one_pow, mul_one] at hii
    have heq : ∀ v : Fin n → ℝ, ((dotProduct v (fun i => U i l)) ^ 2) ^ q
        = |dotProduct v (fun i => U i l)| ^ (2 * q) := fun v => by
      rw [pow_mul, sq_abs]
    simp_rw [heq]
    exact hii
  have hint : ∀ l, Integrable (fun v : Fin n → ℝ => ((dotProduct v (fun i => U i l)) ^ 2) ^ q)
      (sphereGauss n) := by
    intro l
    by_contra hnot
    have h0 := hmom l
    rw [integral_undef hnot] at h0
    exact (div_ne_zero hfac.ne' hdq.ne') h0.symm
  have hS : ∀ v : Fin n → ℝ, 0 ≤ dotProduct v (T.mulVec v) := by
    intro v
    rw [hquad]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hd0 l) (sq_nonneg _)
  have htr0 : 0 ≤ Matrix.trace T := by
    rw [htr]
    exact Finset.sum_nonneg fun l _ => hd0 l
  rcases htr0.eq_or_lt with ht0 | htpos
  · have hd_zero : ∀ l, d l = 0 := by
      intro l
      have hs : ∑ l, d l = 0 := by rw [← htr, ← ht0]
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => hd0 l)).1 hs l (Finset.mem_univ l)
    have hzero : ∀ v : Fin n → ℝ, (dotProduct v (T.mulVec v)) ^ q = 0 := by
      intro v
      rw [hquad]
      simp [hd_zero, zero_pow (by omega : q ≠ 0)]
    simp only [hzero, integral_zero]
    rw [← ht0, zero_pow (by omega : q ≠ 0), mul_zero, zero_div]
  · have hwsum : ∑ l, d l / Matrix.trace T = 1 := by
      rw [← Finset.sum_div, ← htr, div_self htpos.ne']
    have hpt : ∀ v : Fin n → ℝ, (dotProduct v (T.mulVec v)) ^ q
        ≤ (Matrix.trace T) ^ q * ∑ l, (d l / Matrix.trace T) * ((dotProduct v (fun i => U i l)) ^ 2) ^ q := by
      intro v
      have hsum : dotProduct v (T.mulVec v)
          = Matrix.trace T * ∑ l, (d l / Matrix.trace T) * (dotProduct v (fun i => U i l)) ^ 2 := by
        rw [hquad, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        field_simp
      rw [hsum, mul_pow]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg htpos.le q)
      exact Real.pow_arith_mean_le_arith_mean_pow Finset.univ (fun l => d l / Matrix.trace T)
        (fun l => (dotProduct v (fun i => U i l)) ^ 2)
        (fun l _ => div_nonneg (hd0 l) htpos.le) hwsum (fun l _ => sq_nonneg _) q
    have hG : Integrable (fun v : Fin n → ℝ => (Matrix.trace T) ^ q *
        ∑ l, (d l / Matrix.trace T) * ((dotProduct v (fun i => U i l)) ^ 2) ^ q) (sphereGauss n) :=
      Integrable.const_mul (integrable_finsetSum _ fun l _ => (hint l).const_mul _) _
    have hSint : Integrable (fun v : Fin n → ℝ => (dotProduct v (T.mulVec v)) ^ q)
        (sphereGauss n) := by
      refine Integrable.mono' hG ?_ (ae_of_all _ fun v => ?_)
      · exact (by fun_prop : Measurable fun v : Fin n → ℝ =>
          (dotProduct v (T.mulVec v)) ^ q).aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hS v) q)]
        exact hpt v
    calc ∫ v, (dotProduct v (T.mulVec v)) ^ q ∂(sphereGauss n)
        ≤ ∫ v, (Matrix.trace T) ^ q * ∑ l, (d l / Matrix.trace T) *
            ((dotProduct v (fun i => U i l)) ^ 2) ^ q ∂(sphereGauss n) :=
          integral_mono hSint hG (fun v => hpt v)
      _ = (Matrix.trace T) ^ q * ∑ l, (d l / Matrix.trace T) *
            ∫ v, ((dotProduct v (fun i => U i l)) ^ 2) ^ q ∂(sphereGauss n) := by
          rw [integral_const_mul, integral_finsetSum _ fun l _ => (hint l).const_mul _]
          congr 1
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [integral_const_mul]
      _ = ((Nat.doubleFactorial (2 * q - 1) : ℕ) : ℝ) * (Matrix.trace T) ^ q / dq n q := by
          simp only [hmom]
          rw [← Finset.sum_mul, hwsum]
          ring

private lemma gd_indep {n : ℕ} (d : Fin n → ℝ) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s) :
    IndepFun (fun z : Fin n → ℝ => ∑ l ∈ s, d l * z l ^ 2) (fun z : Fin n → ℝ => d a * z a ^ 2)
      (stdGaussianPi n) := by
  have hind : iIndepFun (fun (i : Fin n) (z : Fin n → ℝ) => z i) (stdGaussianPi n) := by
    unfold stdGaussianPi
    exact iIndepFun_pi (X := fun _ x => x) (fun _ => aemeasurable_id)
  have h := hind.indepFun_finset s {a} (by simpa using ha) (fun i => measurable_pi_apply i)
  have h2 := h.comp (φ := fun w : s → ℝ => ∑ i : s, d i * w i ^ 2)
    (ψ := fun w : ({a} : Finset (Fin n)) → ℝ => d a * w ⟨a, Finset.mem_singleton_self a⟩ ^ 2)
    (by fun_prop) (by fun_prop)
  convert h2 using 1
  · funext z
    simp only [Function.comp]
    exact (Finset.sum_coe_sort s (fun i => d i * z i ^ 2)).symm
  · rfl

private lemma gd_indep_pow {n : ℕ} (d : Fin n → ℝ) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s)
    (m k : ℕ) :
    IndepFun (fun z : Fin n → ℝ => (∑ l ∈ s, d l * z l ^ 2) ^ m)
      (fun z : Fin n → ℝ => (d a * z a ^ 2) ^ k) (stdGaussianPi n) :=
  (gd_indep d s a ha).comp (measurable_id.pow_const m) (measurable_id.pow_const k)

private lemma gd_coord_int {n : ℕ} (a : Fin n) (m : ℕ) :
    Integrable (fun z : Fin n → ℝ => z a ^ m) (stdGaussianPi n) := by
  have h := gaussian_integrable_pow m
  rw [← stdGaussianPi_map_coord n a] at h
  exact (integrable_map_measure (measurable_id.pow_const m).aestronglyMeasurable (measurable_pi_apply a).aemeasurable).1 h

private lemma gd_coord_moment {n : ℕ} (a : Fin n) (k : ℕ) :
    ∫ z : Fin n → ℝ, z a ^ (2 * k) ∂(stdGaussianPi n) = (((2 * k - 1).doubleFactorial : ℕ) : ℝ) := by
  rw [← gaussian_moment_even k, ← stdGaussianPi_map_coord n a]
  exact (integral_map (μ := stdGaussianPi n) (φ := fun z : Fin n → ℝ => z a)
    (f := fun x : ℝ => x ^ (2 * k)) (measurable_pi_apply a).aemeasurable
      (measurable_id.pow_const _).aestronglyMeasurable).symm

private lemma gd_c_pow {n : ℕ} (d : Fin n → ℝ) (a : Fin n) (k : ℕ) (z : Fin n → ℝ) :
    (d a * z a ^ 2) ^ k = d a ^ k * z a ^ (2 * k) := by
  rw [mul_pow, pow_mul]

private lemma gd_c_int {n : ℕ} (d : Fin n → ℝ) (a : Fin n) (k : ℕ) :
    Integrable (fun z : Fin n → ℝ => (d a * z a ^ 2) ^ k) (stdGaussianPi n) := by
  simp_rw [gd_c_pow]
  exact (gd_coord_int a _).const_mul _

private lemma gd_c_moment {n : ℕ} (d : Fin n → ℝ) (a : Fin n) (k : ℕ) :
    ∫ z : Fin n → ℝ, (d a * z a ^ 2) ^ k ∂(stdGaussianPi n)
      = d a ^ k * (((2 * k - 1).doubleFactorial : ℕ) : ℝ) := by
  simp_rw [gd_c_pow]
  rw [integral_const_mul, gd_coord_moment]

private lemma gd_A_int {n : ℕ} (d : Fin n → ℝ) (s : Finset (Fin n)) (i : ℕ) :
    Integrable (fun z : Fin n → ℝ => (∑ l ∈ s, d l * z l ^ 2) ^ i) (stdGaussianPi n) := by
  induction s using Finset.induction_on generalizing i with
  | empty =>
    simp only [Finset.sum_empty]
    cases i <;> simp
  | insert a s ha ih =>
    have e : ∀ z : Fin n → ℝ, (∑ l ∈ insert a s, d l * z l ^ 2) ^ i
        = ∑ m ∈ Finset.range (i + 1), ((∑ l ∈ s, d l * z l ^ 2) ^ m * (d a * z a ^ 2) ^ (i - m)
            * (i.choose m : ℝ)) := by
      intro z
      rw [Finset.sum_insert ha, add_comm, add_pow]
    simp_rw [e]
    refine integrable_finsetSum _ fun m _ => Integrable.mul_const ?_ _
    exact ((gd_indep_pow d s a ha m (i - m)).integrable_mul (ih m) (gd_c_int d a _))


private lemma gd_expand {n : ℕ} (d : Fin n → ℝ) (s : Finset (Fin n)) (a : Fin n) (ha : a ∉ s)
    (i : ℕ) :
    ∫ z : Fin n → ℝ, (∑ l ∈ insert a s, d l * z l ^ 2) ^ i ∂(stdGaussianPi n)
      = ∑ m ∈ Finset.range (i + 1),
        (∫ z : Fin n → ℝ, (∑ l ∈ s, d l * z l ^ 2) ^ m ∂(stdGaussianPi n)) *
          (d a ^ (i - m) * (((2 * (i - m) - 1).doubleFactorial : ℕ) : ℝ)) * (i.choose m : ℝ) := by
  have e : ∀ z : Fin n → ℝ, (∑ l ∈ insert a s, d l * z l ^ 2) ^ i
      = ∑ m ∈ Finset.range (i + 1), ((∑ l ∈ s, d l * z l ^ 2) ^ m * (d a * z a ^ 2) ^ (i - m)
          * (i.choose m : ℝ)) := by
    intro z
    rw [Finset.sum_insert ha, add_comm, add_pow]
  simp_rw [e]
  have hint : ∀ m ∈ Finset.range (i + 1), Integrable (fun z : Fin n → ℝ =>
      (∑ l ∈ s, d l * z l ^ 2) ^ m * (d a * z a ^ 2) ^ (i - m) * (i.choose m : ℝ))
      (stdGaussianPi n) := fun m _ => Integrable.mul_const
    ((gd_indep_pow d s a ha m (i - m)).integrable_mul (gd_A_int d s m) (gd_c_int d a _)) _
  rw [integral_finsetSum _ hint]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [integral_mul_const]
  congr 1
  rw [← gd_c_moment d a (i - m)]
  exact (gd_indep_pow d s a ha m (i - m)).integral_mul_eq_mul_integral
    (gd_A_int d s m).aestronglyMeasurable (gd_c_int d a _).aestronglyMeasurable

private lemma gd_moments {n : ℕ} (d : Fin n → ℝ) (s : Finset (Fin n)) :
    (∫ z : Fin n → ℝ, (∑ l ∈ s, d l * z l ^ 2) ^ 1 ∂(stdGaussianPi n) = ∑ l ∈ s, d l) ∧
    (∫ z : Fin n → ℝ, (∑ l ∈ s, d l * z l ^ 2) ^ 2 ∂(stdGaussianPi n)
      = (∑ l ∈ s, d l) ^ 2 + 2 * ∑ l ∈ s, d l ^ 2) ∧
    (∫ z : Fin n → ℝ, (∑ l ∈ s, d l * z l ^ 2) ^ 3 ∂(stdGaussianPi n)
      = (∑ l ∈ s, d l) ^ 3 + 6 * (∑ l ∈ s, d l) * (∑ l ∈ s, d l ^ 2) + 8 * ∑ l ∈ s, d l ^ 3) ∧
    (∫ z : Fin n → ℝ, (∑ l ∈ s, d l * z l ^ 2) ^ 4 ∂(stdGaussianPi n)
      = (∑ l ∈ s, d l) ^ 4 + 12 * (∑ l ∈ s, d l) ^ 2 * (∑ l ∈ s, d l ^ 2)
        + 32 * (∑ l ∈ s, d l) * (∑ l ∈ s, d l ^ 3) + 12 * (∑ l ∈ s, d l ^ 2) ^ 2
        + 48 * ∑ l ∈ s, d l ^ 4) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    simp only [pow_one] at h1
    simp only [Finset.sum_insert ha]
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := gd_expand d s a ha 1
      simp only [Finset.sum_insert ha, Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.doubleFactorial] at this
      simp only [pow_one] at this ⊢
      rw [this, h1]
    · have := gd_expand d s a ha 2
      simp only [Finset.sum_insert ha, Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.doubleFactorial, Nat.choose] at this
      rw [this, h1, h2]; ring
    · have := gd_expand d s a ha 3
      simp only [Finset.sum_insert ha, Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.doubleFactorial, Nat.choose] at this
      rw [this, h1, h2, h3]; ring
    · have := gd_expand d s a ha 4
      simp only [Finset.sum_insert ha, Finset.sum_range_succ, Finset.sum_range_zero] at this
      norm_num [Nat.doubleFactorial, Nat.choose] at this
      rw [this, h1, h2, h3, h4]; ring


private lemma gd_diag {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ∃ U : Matrix.orthogonalGroup (Fin m) ℝ, ∃ d : Fin m → ℝ,
      (U : Matrix (Fin m) (Fin m) ℝ).transpose * A * (U : Matrix (Fin m) (Fin m) ℝ)
        = Matrix.diagonal d := by
  refine ⟨hA.eigenvectorUnitary, RCLike.ofReal ∘ hA.eigenvalues, ?_⟩
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  have h1 : (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = 1 :=
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2
  have h2 : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      (star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ)) = 1 :=
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h1 h2 h
  generalize (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = U at h h1 h2 ⊢
  generalize (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) : Matrix (Fin m) (Fin m) ℝ) = D at h ⊢
  rw [h]
  calc U.transpose * (U * D * U.transpose) * U
        = (U.transpose * U) * D * (U.transpose * U) := by simp only [Matrix.mul_assoc]
    _ = D := by rw [h1]; simp

private lemma gd_trace_pow {m : ℕ} (H : Matrix (Fin m) (Fin m) ℝ) (U : Matrix.orthogonalGroup (Fin m) ℝ)
    (d : Fin m → ℝ)
    (hd : (U : Matrix (Fin m) (Fin m) ℝ).transpose * H * (U : Matrix (Fin m) (Fin m) ℝ)
        = Matrix.diagonal d) (k : ℕ) :
    Matrix.trace (H ^ k) = ∑ l, d l ^ k := by
  have h1 : (U : Matrix (Fin m) (Fin m) ℝ).transpose * (U : Matrix (Fin m) (Fin m) ℝ) = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin m) ℝ).1 U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have h2 : (U : Matrix (Fin m) (Fin m) ℝ) * (U : Matrix (Fin m) (Fin m) ℝ).transpose = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff (Fin m) ℝ).1 U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have hH : H = (U : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal d
      * (U : Matrix (Fin m) (Fin m) ℝ).transpose := by
    rw [← hd]
    calc H = ((U : Matrix (Fin m) (Fin m) ℝ) * (U : Matrix (Fin m) (Fin m) ℝ).transpose) * H *
          ((U : Matrix (Fin m) (Fin m) ℝ) * (U : Matrix (Fin m) (Fin m) ℝ).transpose) := by
          rw [h2]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hpow : ∀ k : ℕ, H ^ k = (U : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal d ^ k
      * (U : Matrix (Fin m) (Fin m) ℝ).transpose := by
    intro k
    induction k with
    | zero => simp [h2]
    | succ k ih =>
      rw [pow_succ, ih, hH]
      calc (U : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal d ^ k * (U : Matrix (Fin m) (Fin m) ℝ).transpose
            * ((U : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal d * (U : Matrix (Fin m) (Fin m) ℝ).transpose)
          = (U : Matrix (Fin m) (Fin m) ℝ) * Matrix.diagonal d ^ k
            * ((U : Matrix (Fin m) (Fin m) ℝ).transpose * (U : Matrix (Fin m) (Fin m) ℝ))
            * Matrix.diagonal d * (U : Matrix (Fin m) (Fin m) ℝ).transpose := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, pow_succ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
  rw [hpow k, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h1, Matrix.one_mul,
    Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp [Pi.pow_apply]


private lemma gd_gauss_quartic (n : ℕ) (H : Matrix (Fin n) (Fin n) ℝ) (hH : H.IsHermitian)
    (htr : Matrix.trace H = 0) :
    ∫ z : Fin n → ℝ, (dotProduct z (H.mulVec z)) ^ 4 ∂(stdGaussianPi n)
      = 12 * (Matrix.trace (H ^ 2)) ^ 2 + 48 * Matrix.trace (H ^ 4) := by
  obtain ⟨U, d, hd⟩ := gd_diag H hH
  have hq : ∀ z : Fin n → ℝ,
      dotProduct (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z) (Matrix.mulVec H (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z))
        = ∑ l, d l * z l ^ 2 := by
    intro z
    have e1 : dotProduct (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z) (Matrix.mulVec H (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z))
        = dotProduct z (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ).transpose
            (Matrix.mulVec H (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z))) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
      exact dotProduct_comm _ _
    rw [e1, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hd]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hmap := stdGaussianPi_map_orthogonal n U
  have hmeas : Measurable (fun z : Fin n → ℝ => (dotProduct z (H.mulVec z)) ^ 4) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  have hrot : ∫ z : Fin n → ℝ, (dotProduct z (H.mulVec z)) ^ 4 ∂(stdGaussianPi n)
      = ∫ z : Fin n → ℝ, (dotProduct (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z)
          (Matrix.mulVec H (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) z))) ^ 4 ∂(stdGaussianPi n) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) hmeas.aestronglyMeasurable]
  rw [hrot]
  simp_rw [hq]
  have hm := (gd_moments d Finset.univ).2.2.2
  rw [hm, gd_trace_pow H U d hd 2, gd_trace_pow H U d hd 4]
  have h1 : ∑ l, d l = 0 := by
    have := gd_trace_pow H U d hd 1
    simpa [htr] using this.symm
  rw [h1]; ring


/-- Part (iv) of `lem:app-sgd-sphere` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Spherical moments]\label{lem:app-sgd-sphere}
Let $v$ be uniform on the unit sphere of $\R^n$, $n\ge2$. Then
\begin{equation}\label{eqn:app-sgd-l1}
\EE\norm v_1^2=1+\frac{2(n-1)}\pi .
\end{equation}
For a vector $a$, a positive semidefinite $T$ and an integer $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-sphere}
\EE\abs{v^\T a}^{2q}=\frac{(2q-1)!!\,\norm a^{2q}}{d_q(n)},\qquad \EE\big(v^\T Tv\big)^q\le\frac{(2q-1)!!\,(\Tr T)^q}{d_q(n)}.
\end{equation}
For symmetric $H$ with $\Tr H=0$,
\begin{equation}\label{eqn:app-sgd-sphere-four}
\EE\big(v^\T Hv\big)^4=\frac{12(\Tr H^2)^2+48\Tr H^4}{d_4(n)} .
\end{equation}
In particular, if $c\Id\preceq\Lambda\preceq L\Id$ in dimension $n$ and
$\bar\mu=\Tr\Lambda/n$, then $\EE(v^\T\Lambda v-\bar\mu)^4\le60L^4/n^2$.
\end{lemma}
```
-/
theorem lem_app_sgd_sphere_iv (n : ℕ) (hn : 2 ≤ n) (H : Matrix (Fin n) (Fin n) ℝ)
    (hH : H.IsHermitian) (htr : Matrix.trace H = 0) :
    ∫ v, (dotProduct v (H.mulVec v)) ^ 4 ∂(sphereGauss n)
      = (12 * (Matrix.trace (H ^ 2)) ^ 2 + 48 * Matrix.trace (H ^ 4)) / dq n 4 := by
  have hn0 : (0 : ℝ) < dq n 4 := by
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    unfold dq
    apply Finset.prod_pos
    intro r _
    have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    linarith
  have hm : Measurable (fun z : Fin n → ℝ => (dotProduct z (H.mulVec z)) ^ 4) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  have h0 : (fun z : Fin n → ℝ => (dotProduct z (H.mulVec z)) ^ 4) 0 = 0 := by simp
  have hhom : ∀ c : ℝ, 0 < c → ∀ z : Fin n → ℝ,
      (dotProduct (c • z) (H.mulVec (c • z))) ^ 4 = c ^ 8 * (dotProduct z (H.mulVec z)) ^ 4 := by
    intro c hc z
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc, ← sq, mul_pow, ← pow_mul]
  have hsplit := app_sphere_split n 8 _ hm h0 hhom
  have hRmom : ∫ z, euclidNorm n z ^ 8 ∂(stdGaussianPi n) = dq n 4 := by
    have heu : ∀ z : Fin n → ℝ, euclidNorm n z ^ 8 = (∑ i, z i ^ 2) ^ 4 := by
      intro z
      unfold euclidNorm
      rw [show (8 : ℕ) = 2 * 4 from rfl, pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp_rw [heu]
    unfold dq
    exact stdGaussianPi_sq_norm_moment n 4 (by norm_num)
  rw [hRmom, gd_gauss_quartic n H hH htr] at hsplit
  rw [eq_div_iff hn0.ne']
  linear_combination (-1 : ℝ) * hsplit

/-- Private helper: a fixed coordinate of the standard Gaussian vanishes with probability `0`. -/
private lemma stdG_coord_zero_null_v (n : ℕ) (i : Fin n) :
    (stdGaussianPi n) {z : Fin n → ℝ | z i = 0} = 0 := by
  have hm : Measurable (fun z : Fin n → ℝ => z i) := measurable_pi_apply i
  have h1 : (stdGaussianPi n) ((fun z : Fin n → ℝ => z i) ⁻¹' {0}) = 0 := by
    rw [← Measure.map_apply hm (measurableSet_singleton 0), stdGaussianPi_map_coord]
    exact gaussianReal_absolutelyContinuous (0 : ℝ) (v := 1) one_ne_zero Real.volume_singleton
  simpa [Set.preimage] using h1

/-- Private helper: under the uniform sphere law, `∑ vᵢ² = 1` almost surely (`n ≥ 1`). -/
private lemma sphere_ae_norm_one_v (n : ℕ) (hn : 1 ≤ n) :
    ∀ᵐ v ∂(sphereGauss n), ∑ i, v i ^ 2 = 1 := by
  have hc : Continuous (euclidNorm n) := by
    unfold euclidNorm; fun_prop
  have hm : Measurable (fun z : Fin n → ℝ => (euclidNorm n z)⁻¹ • z) :=
    (hc.measurable.inv).smul measurable_id
  have hS : MeasurableSet {v : Fin n → ℝ | ∑ j, v j ^ 2 = 1} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  unfold sphereGauss
  rw [ae_map_iff hm.aemeasurable hS, ae_iff]
  refine measure_mono_null ?_ (stdG_coord_zero_null_v n ⟨0, by omega⟩)
  intro z hz
  simp only [Set.mem_setOf_eq] at hz
  show z ⟨0, by omega⟩ = 0
  by_contra hne
  have hpos : 0 < ∑ j, z j ^ 2 :=
    lt_of_lt_of_le (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hne)))
      (Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ _))
  apply hz
  have hsq : euclidNorm n z ^ 2 = ∑ j, z j ^ 2 := by
    unfold euclidNorm; exact Real.sq_sqrt hpos.le
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, inv_pow, hsq, inv_mul_cancel₀ hpos.ne']

/-- Private helper: diagonal entries of a congruence `Uᵀ M U = diag D` of a PSD `M` are `≥ 0`. -/
private lemma diag_nonneg_cong_v {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.PosSemidef)
    (U : Matrix (Fin n) (Fin n) ℝ) (D : Fin n → ℝ)
    (hD : U.transpose * M * U = Matrix.diagonal D) (l : Fin n) : 0 ≤ D l := by
  have h := hM.conjTranspose_mul_mul_same U
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, hD] at h
  have := h.diag_nonneg (i := l)
  simpa [Matrix.diagonal_apply_eq] using this

/-- Part (v), the bound stated in its final sentence of `lem:app-sgd-sphere` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Spherical moments]\label{lem:app-sgd-sphere}
Let $v$ be uniform on the unit sphere of $\R^n$, $n\ge2$. Then
\begin{equation}\label{eqn:app-sgd-l1}
\EE\norm v_1^2=1+\frac{2(n-1)}\pi .
\end{equation}
For a vector $a$, a positive semidefinite $T$ and an integer $1\le q\le4$,
\begin{equation}\label{eqn:app-sgd-sphere}
\EE\abs{v^\T a}^{2q}=\frac{(2q-1)!!\,\norm a^{2q}}{d_q(n)},\qquad \EE\big(v^\T Tv\big)^q\le\frac{(2q-1)!!\,(\Tr T)^q}{d_q(n)}.
\end{equation}
For symmetric $H$ with $\Tr H=0$,
\begin{equation}\label{eqn:app-sgd-sphere-four}
\EE\big(v^\T Hv\big)^4=\frac{12(\Tr H^2)^2+48\Tr H^4}{d_4(n)} .
\end{equation}
In particular, if $c\Id\preceq\Lambda\preceq L\Id$ in dimension $n$ and
$\bar\mu=\Tr\Lambda/n$, then $\EE(v^\T\Lambda v-\bar\mu)^4\le60L^4/n^2$.
\end{lemma}
```
-/
theorem lem_app_sgd_sphere_v (n : ℕ) (hn : 2 ≤ n) (c L : ℝ) (hc : 0 ≤ c)
    (Λ : Matrix (Fin n) (Fin n) ℝ)
    (hlo : (Λ - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef)
    (hhi : (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Λ).PosSemidef) :
    ∫ v, (dotProduct v (Λ.mulVec v) - Matrix.trace Λ / (n : ℝ)) ^ 4 ∂(sphereGauss n)
      ≤ 60 * L ^ 4 / (n : ℝ) ^ 2 := by
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = Matrix.trace Λ / (n : ℝ) := ⟨_, rfl⟩
  rw [← hμ]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hnpos : (0 : ℝ) < n := by linarith
  have hnne : (n : ℝ) ≠ 0 := hnpos.ne'
  obtain ⟨H, hHdef⟩ : ∃ H : Matrix (Fin n) (Fin n) ℝ,
      H = Λ - μ • (1 : Matrix (Fin n) (Fin n) ℝ) := ⟨_, rfl⟩
  have hΛh : Λ.IsHermitian := by
    have h2 : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      unfold Matrix.IsHermitian; simp
    have h3 := hlo.1.add h2
    rwa [sub_add_cancel] at h3
  have hH : H.IsHermitian := by
    have h1 : (μ • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
      unfold Matrix.IsHermitian; simp
    rw [hHdef]
    exact hΛh.sub h1
  have htr : Matrix.trace H = 0 := by
    rw [hHdef, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, hμ, smul_eq_mul,
      Fintype.card_fin, div_mul_cancel₀ _ hnne, sub_self]
  obtain ⟨U, d, hd⟩ := gd_diag H hH
  have hU1 : (U : Matrix (Fin n) (Fin n) ℝ).transpose * (U : Matrix (Fin n) (Fin n) ℝ) = 1 := by
    have := (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
    simpa [Matrix.star_eq_conjTranspose] using this
  have hsumd : ∑ l, d l = 0 := by
    have h1 := gd_trace_pow H U d hd 1
    simp only [pow_one] at h1
    rw [htr] at h1
    exact h1.symm
  -- congruences of the two PSD matrices
  have hΛeq : Λ - c • (1 : Matrix (Fin n) (Fin n) ℝ) = H + (μ - c) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hHdef, sub_smul]; abel
  have hBeq : L • (1 : Matrix (Fin n) (Fin n) ℝ) - Λ
      = ((L - μ) • (1 : Matrix (Fin n) (Fin n) ℝ)) - H := by
    rw [hHdef, sub_smul]; abel
  have hA : (U : Matrix (Fin n) (Fin n) ℝ).transpose * (Λ - c • (1 : Matrix (Fin n) (Fin n) ℝ))
      * (U : Matrix (Fin n) (Fin n) ℝ)
      = Matrix.diagonal (fun l => d l + (μ - c)) := by
    rw [hΛeq, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hU1, hd]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  have hB : (U : Matrix (Fin n) (Fin n) ℝ).transpose * (L • (1 : Matrix (Fin n) (Fin n) ℝ) - Λ)
      * (U : Matrix (Fin n) (Fin n) ℝ)
      = Matrix.diagonal (fun l => L - μ - d l) := by
    rw [hBeq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hU1, hd]
    ext i j
    by_cases h : i = j <;> simp [h, Matrix.one_apply, Matrix.diagonal_apply]
  have hAl : ∀ l, 0 ≤ d l + (μ - c) := fun l =>
    diag_nonneg_cong_v _ hlo (U : Matrix (Fin n) (Fin n) ℝ) _ hA l
  have hBl : ∀ l, 0 ≤ L - μ - d l := fun l =>
    diag_nonneg_cong_v _ hhi (U : Matrix (Fin n) (Fin n) ℝ) _ hB l
  -- μ ∈ [c, L]
  have hμc : c ≤ μ := by
    have hs : 0 ≤ ∑ l, (d l + (μ - c)) := Finset.sum_nonneg fun l _ => hAl l
    simp only [Finset.sum_add_distrib, hsumd, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith
  have hμL : μ ≤ L := by
    have hs : 0 ≤ ∑ l, (L - μ - d l) := Finset.sum_nonneg fun l _ => hBl l
    simp only [Finset.sum_sub_distrib, hsumd, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hs
    nlinarith
  have hL0 : 0 ≤ L := le_trans (le_trans hc hμc) hμL
  have hdl1 : ∀ l, -L ≤ d l := fun l => by linarith [hAl l]
  have hdl2 : ∀ l, d l ≤ L := fun l => by linarith [hBl l]
  have hd2 : ∀ l, d l ^ 2 ≤ L ^ 2 := fun l => by
    nlinarith [hdl1 l, hdl2 l]
  have hd4 : ∀ l, d l ^ 4 ≤ L ^ 4 := fun l => by
    have h := mul_le_mul (hd2 l) (hd2 l) (sq_nonneg _) (by positivity : (0 : ℝ) ≤ L ^ 2)
    nlinarith [h]
  have hS2 : ∑ l, d l ^ 2 ≤ (n : ℝ) * L ^ 2 := by
    calc ∑ l, d l ^ 2 ≤ ∑ _l : Fin n, L ^ 2 := Finset.sum_le_sum fun l _ => hd2 l
      _ = (n : ℝ) * L ^ 2 := by simp
  have hS4 : ∑ l, d l ^ 4 ≤ (n : ℝ) * L ^ 4 := by
    calc ∑ l, d l ^ 4 ≤ ∑ _l : Fin n, L ^ 4 := Finset.sum_le_sum fun l _ => hd4 l
      _ = (n : ℝ) * L ^ 4 := by simp
  have hS2nn : 0 ≤ ∑ l, d l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  -- a.e. identity on the sphere
  have hae : (fun v : Fin n → ℝ => (dotProduct v (Λ.mulVec v) - μ) ^ 4)
      =ᵐ[sphereGauss n] (fun v : Fin n → ℝ => (dotProduct v (H.mulVec v)) ^ 4) := by
    filter_upwards [sphere_ae_norm_one_v n (by omega)] with v hv
    have hvv : dotProduct v v = 1 := by
      unfold dotProduct; simpa [sq] using hv
    have hHv : H.mulVec v = Λ.mulVec v - μ • v := by
      rw [hHdef, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hdot : dotProduct v (H.mulVec v) = dotProduct v (Λ.mulVec v) - μ := by
      rw [hHv, dotProduct_sub, dotProduct_smul, hvv, smul_eq_mul, mul_one]
    simp only [hdot]
  rw [integral_congr_ae hae, lem_app_sgd_sphere_iv n hn H hH htr, gd_trace_pow H U d hd 2,
    gd_trace_pow H U d hd 4]
  have hdq : (n : ℝ) ^ 4 ≤ dq n 4 := by
    unfold dq
    norm_num [Finset.prod_range_succ]
    nlinarith [pow_nonneg hnpos.le 3, mul_nonneg hnpos.le hnpos.le]
  have hdqpos : 0 < dq n 4 := lt_of_lt_of_le (by positivity) hdq
  have hS2sq := mul_le_mul hS2 hS2 hS2nn (by positivity : (0 : ℝ) ≤ n * L ^ 2)
  have hnum : 12 * (∑ l, d l ^ 2) ^ 2 + 48 * ∑ l, d l ^ 4 ≤ 60 * (n : ℝ) ^ 2 * L ^ 4 := by
    nlinarith [mul_nonneg (mul_nonneg hnpos.le (pow_nonneg hL0 4)) (sub_nonneg.2 hn1)]
  rw [div_le_div_iff₀ hdqpos (by positivity)]
  have h1 := mul_le_mul_of_nonneg_right hnum (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hdq (by positivity : (0 : ℝ) ≤ 60 * L ^ 4)
  nlinarith [h1, h2]

/-! ## `lem:app-sgd-haar-sign` -/

private lemma haarSignY_measurable (n : ℕ) (i : Fin n) :
    Measurable (fun p : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
      haarSignY p.1 p.2 i) := by
  have hs : Measurable Real.sign := by
    unfold Real.sign
    exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
      (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)
  change Measurable (fun p : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ => ∑ k, (p.2 : Matrix (Fin n) (Fin n) ℝ) k i *
    Real.sign (∑ l, (p.2 : Matrix (Fin n) (Fin n) ℝ) k l * p.1 l))
  have hentry : ∀ k l : Fin n, Measurable (fun p :
      (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
      (p.2 : Matrix (Fin n) (Fin n) ℝ) k l) := by
    intro k l
    have hc : Measurable (fun p : (Fin n → ℝ) × Matrix.orthogonalGroup (Fin n) ℝ =>
        (p.2 : Matrix (Fin n) (Fin n) ℝ)) := measurable_subtype_coe.comp measurable_snd
    exact (measurable_pi_apply l).comp ((measurable_pi_apply k).comp hc)
  apply Finset.measurable_sum
  intro k _
  apply (hentry k i).mul
  apply hs.comp
  apply Finset.measurable_sum
  intro l _
  exact (hentry k l).mul ((measurable_pi_apply l).comp measurable_fst)

private lemma orth_entry_abs_le_one {n : ℕ} (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (k i : Fin n) : |(U : Matrix (Fin n) (Fin n) ℝ) k i| ≤ 1 := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ).transpose *
      (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
    (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 U.2
  have hdiag := congrFun (congrFun hU i) i
  have hsum : ∑ l, (U : Matrix (Fin n) (Fin n) ℝ) l i ^ 2 = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using hdiag
  have hle := Finset.single_le_sum (f := fun l =>
    (U : Matrix (Fin n) (Fin n) ℝ) l i ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ k)
  rw [hsum] at hle
  nlinarith [sq_abs ((U : Matrix (Fin n) (Fin n) ℝ) k i), abs_nonneg ((U : Matrix (Fin n) (Fin n) ℝ) k i)]

private lemma haarSignY_abs_le (n : ℕ) (a : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) (i : Fin n) : |haarSignY a U i| ≤ n := by
  have hs : ∀ x : ℝ, |Real.sign x| ≤ 1 := by
    intro x
    rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
  unfold haarSignY Matrix.mulVec dotProduct
  calc |∑ k, (U : Matrix (Fin n) (Fin n) ℝ).transpose i k *
          Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k)|
      ≤ ∑ k, |(U : Matrix (Fin n) (Fin n) ℝ).transpose i k *
          Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin n, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      rw [abs_mul]
      exact (mul_le_mul (orth_entry_abs_le_one U k i) (hs _) (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)
    _ = n := by simp

private lemma haarSignY_product_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (n : ℕ)
    (A : Ω → Fin n → ℝ) (hA : Measurable A)
    (U : Ω → Matrix.orthogonalGroup (Fin n) ℝ) (hU : Measurable U) (i j : Fin n) :
    Integrable (fun ω => haarSignY (A ω) (U ω) i * haarSignY (A ω) (U ω) j) P := by
  refine Integrable.mono' (integrable_const ((n : ℝ) ^ 2))
    (((haarSignY_measurable n i).comp (hA.prodMk hU)).mul
      ((haarSignY_measurable n j).comp (hA.prodMk hU))).aestronglyMeasurable ?_
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_mul, sq]
  exact mul_le_mul (haarSignY_abs_le n (A ω) (U ω) i)
    (haarSignY_abs_le n (A ω) (U ω) j) (abs_nonneg _) (Nat.cast_nonneg n)


private lemma haarSignY_dot (n : ℕ) (a : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) :
    dotProduct a (haarSignY a U) = ∑ k, |Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k| := by
  unfold haarSignY
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  apply Finset.sum_congr rfl
  intro k _
  dsimp only
  rcases lt_trichotomy (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k) 0 with h | h | h
  · rw [Real.sign_of_neg h, abs_of_neg h, mul_neg_one]
  · rw [h, Real.sign_zero, abs_zero, mul_zero]
  · rw [Real.sign_of_pos h, abs_of_pos h, mul_one]

private lemma haarSignY_sq_norm (n : ℕ) (a : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ)
    (ha : ∀ k, Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k ≠ 0) :
    ∑ k, haarSignY a U k ^ 2 = n := by
  have hU : (U : Matrix (Fin n) (Fin n) ℝ) *
      (U : Matrix (Fin n) (Fin n) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 U.2
  have heq : dotProduct (haarSignY a U) (haarSignY a U) =
      dotProduct (fun k => Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k))
        (fun k => Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k)) := by
    unfold haarSignY
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      hU, Matrix.one_mulVec]
  have hs : ∀ k, Real.sign (Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a k) ^ 2 = 1 := by
    intro k
    rcases Real.sign_apply_eq_of_ne_zero _ (ha k) with h | h <;> simp [h]
  simpa only [dotProduct, ← sq, hs, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] using heq

private lemma haarSignY_ae_sq_norm_unit (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∀ᵐ U ∂ν, ∑ k, haarSignY v U k ^ 2 = n := by
  rw [isOrthHaar_unique hν (haarO_isOrthHaar n)]
  filter_upwards [haarO_mulVec_coord_ne_zero n v hv] with U hU
  exact haarSignY_sq_norm n v U hU

private lemma haarSignY_longitudinal_unit (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∫ U, dotProduct v (haarSignY v U) ^ 2 ∂ν =
      1 + 2 * ((n : ℝ) - 1) / Real.pi := by
  simp_rw [haarSignY_dot]
  rw [isOrthHaar_unique hν (haarO_isOrthHaar n)]
  have hm : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) v) := by fun_prop
  have hf : Measurable (fun w : Fin n → ℝ => (∑ k, |w k|) ^ 2) := by fun_prop
  rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, haarO_map_mulVec n v hv]
  exact lem_app_sgd_sphere_i n hn

private lemma haarSignY_right_stabilizer (n : ℕ) (a : Fin n → ℝ)
    (U Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hQ : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) a = a) :
    haarSignY a (U * Q) = Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ).transpose
      (haarSignY a U) := by
  change Matrix.mulVec ((U : Matrix (Fin n) (Fin n) ℝ) *
      (Q : Matrix (Fin n) (Fin n) ℝ)).transpose
      (fun k => Real.sign (Matrix.mulVec ((U : Matrix (Fin n) (Fin n) ℝ) *
        (Q : Matrix (Fin n) (Fin n) ℝ)) a k)) = _
  have hUa : Matrix.mulVec ((U : Matrix (Fin n) (Fin n) ℝ) *
      (Q : Matrix (Fin n) (Fin n) ℝ)) a =
      Matrix.mulVec (U : Matrix (Fin n) (Fin n) ℝ) a := by
    rw [← Matrix.mulVec_mulVec, hQ]
  rw [hUa, Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  rfl

private lemma haarSignY_second_stabilizer (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (a : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hQ : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) a = a) (i j : Fin n) :
    ∫ U, haarSignY a U i * haarSignY a U j ∂ν =
      ∫ U, Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ).transpose (haarSignY a U) i *
        Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ).transpose (haarSignY a U) j ∂ν := by
  have hm : Measurable (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      haarSignY a U i * haarSignY a U j) :=
    ((haarSignY_measurable n i).comp (measurable_const.prodMk measurable_id)).mul
      ((haarSignY_measurable n j).comp (measurable_const.prodMk measurable_id))
  calc ∫ U, haarSignY a U i * haarSignY a U j ∂ν
      = ∫ U, haarSignY a U i * haarSignY a U j ∂(ν.map (fun U => U * Q)) := by
        rw [hν.2.2 Q]
    _ = ∫ U, haarSignY a (U * Q) i * haarSignY a (U * Q) j ∂ν := by
        rw [integral_map (continuous_mul_const Q).measurable.aemeasurable
          hm.aestronglyMeasurable]
    _ = _ := by simp_rw [haarSignY_right_stabilizer n a _ Q hQ]

private lemma haarSignY_trace_unit (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (v : Fin n → ℝ) (hv : euclidNorm n v = 1) :
    ∑ k, ∫ U, haarSignY v U k ^ 2 ∂ν = n := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hi : ∀ k, Integrable (fun U => haarSignY v U k ^ 2) ν := by
    intro k
    simpa only [sq, id_eq] using haarSignY_product_integrable ν n (fun _ => v) measurable_const
      id measurable_id k k
  rw [← integral_finsetSum _ (fun k _ => hi k)]
  calc ∫ U, ∑ k, haarSignY v U k ^ 2 ∂ν = ∫ _U, (n : ℝ) ∂ν :=
      integral_congr_ae (haarSignY_ae_sq_norm_unit n ν hν v hv)
    _ = n := by simp

private lemma euclidNorm_pos_haar (n : ℕ) (a : Fin n → ℝ) (ha : a ≠ 0) :
    0 < euclidNorm n a := by
  unfold euclidNorm
  refine Real.sqrt_pos.2 ?_
  by_contra h
  apply ha
  have hsum : ∑ i, a i ^ 2 = 0 :=
    le_antisymm (not_lt.1 h) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  funext i
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).1 hsum i
    (Finset.mem_univ i)
  exact (pow_eq_zero_iff two_ne_zero).1 h2

private lemma haarSignY_pos_smul (n : ℕ) (a : Fin n → ℝ) (c : ℝ) (hc : 0 < c)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : haarSignY (c • a) U = haarSignY a U := by
  have hs : ∀ x : ℝ, Real.sign (c * x) = Real.sign x := by
    intro x
    rcases lt_trichotomy x 0 with hx | hx | hx
    · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hc hx)]
    · simp [hx]
    · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hc hx)]
  unfold haarSignY
  simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, hs]

private lemma haar_normalize_unit (n : ℕ) (a : Fin n → ℝ) (ha : a ≠ 0) :
    euclidNorm n ((euclidNorm n a)⁻¹ • a) = 1 := by
  have hpos := euclidNorm_pos_haar n a ha
  have he : ∀ z : Fin n → ℝ, euclidNorm n z ^ 2 = ∑ i, z i ^ 2 := by
    intro z
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hsq : euclidNorm n ((euclidNorm n a)⁻¹ • a) ^ 2 = 1 := by
    rw [he]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, ← he a, inv_pow]
    exact inv_mul_cancel₀ (pow_ne_zero 2 hpos.ne')
  exact (pow_eq_one_iff_of_nonneg (Real.sqrt_nonneg _) two_ne_zero).1 hsq

private lemma haarSignY_trace (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (a : Fin n → ℝ) (ha : a ≠ 0) :
    ∑ k, ∫ U, haarSignY a U k ^ 2 ∂ν = n := by
  have h := haarSignY_trace_unit n ν hν ((euclidNorm n a)⁻¹ • a)
    (haar_normalize_unit n a ha)
  simpa only [haarSignY_pos_smul n a _ (inv_pos.2 (euclidNorm_pos_haar n a ha))] using h

/-- Householder reflection, with its action written using the coordinate dot product. -/
private lemma haar_reflection (n : ℕ) (w : Fin n → ℝ) (hw : w ≠ 0) :
    ∃ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      (Q : Matrix (Fin n) (Fin n) ℝ).transpose = Q ∧
      ∀ z, Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) z =
        z - ((2 / dotProduct w w) * dotProduct w z) • w := by
  have hN : dotProduct w w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.mp h)
  set P := Matrix.vecMulVec w w with hP
  have hPP : P * P = dotProduct w w • P := by
    rw [hP, Matrix.vecMulVec_mul_vecMulVec]
    ext i j
    simp [Matrix.vecMulVec_apply]
    ring
  have hPT : P.transpose = P := by simp [P, Matrix.transpose_vecMulVec]
  set W : Matrix (Fin n) (Fin n) ℝ := 1 - (2 / dotProduct w w) • P with hW
  have hWT : W.transpose = W := by
    simp only [W, Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul, hPT]
  have hWW : W * W.transpose = 1 := by
    rw [hWT, hW, sub_mul, mul_sub, mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_smul, hPP]
    simp only [one_mul, mul_one, smul_smul]
    have h1 : (2 / dotProduct w w) * ((2 / dotProduct w w) * dotProduct w w) =
        2 * (2 / dotProduct w w) := by field_simp
    rw [h1, two_mul, add_smul]
    abel
  refine ⟨⟨W, (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).2 hWW⟩, hWT, ?_⟩
  intro z
  change W.mulVec z = _
  simp only [W, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, P,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

/-- A matrix commuting with the stabilizer of `v` preserves every transverse line. -/
private lemma haar_stabilizer_eigen (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ)
    (hM : ∀ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) v = v →
      (Q : Matrix (Fin n) (Fin n) ℝ) * M = M * Q)
    (w : Fin n → ℝ) (hwv : dotProduct w v = 0) :
    ∃ d : ℝ, M.mulVec w = d • w := by
  by_cases hw : w = 0
  · exact ⟨0, by simp [hw]⟩
  obtain ⟨Q, _, hQ⟩ := haar_reflection n w hw
  have hQv : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) v = v := by
    simp [hQ, hwv]
  have hQw : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) w = -w := by
    rw [hQ, div_mul_cancel₀ _ (fun h => hw (dotProduct_self_eq_zero.mp h))]
    module
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.mulVec w) (hM Q hQv)
  simp only [← Matrix.mulVec_mulVec, hQw, Matrix.mulVec_neg, hQ] at he
  refine ⟨((2 / dotProduct w w) * dotProduct w (M.mulVec w)) / 2, ?_⟩
  ext i
  have hi := congrFun he i
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul] at hi ⊢
  linarith

/-- The distinguished unit vector is also an eigenvector of a stabilizer-invariant matrix. -/
private lemma haar_stabilizer_longitudinal (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : dotProduct v v = 1)
    (hM : ∀ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) v = v →
      (Q : Matrix (Fin n) (Fin n) ℝ) * M = M * Q) :
    M.mulVec v = dotProduct v (M.mulVec v) • v := by
  let c := dotProduct v (M.mulVec v)
  let z := M.mulVec v - c • v
  have hzv : dotProduct z v = 0 := by
    simp only [z, sub_dotProduct, smul_dotProduct, hv, smul_eq_mul, mul_one]
    rw [dotProduct_comm]
    exact sub_self c
  by_cases hz : z = 0
  · exact sub_eq_zero.mp hz
  obtain ⟨Q, _, hQ⟩ := haar_reflection n z hz
  have hQv : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) v = v := by
    simp [hQ, hzv]
  have he := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A.mulVec v) (hM Q hQv)
  simp only [← Matrix.mulVec_mulVec, hQv, hQ] at he
  have hzero : ((2 / dotProduct z z) * dotProduct z (M.mulVec v)) • z = 0 :=
    sub_eq_self.mp he
  have hz2 : dotProduct z z ≠ 0 := fun h => hz (dotProduct_self_eq_zero.mp h)
  have hd : dotProduct z (M.mulVec v) = 0 :=
    (mul_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hz)).resolve_left
      (div_ne_zero two_ne_zero hz2)
  apply False.elim
  apply hz
  apply dotProduct_self_eq_zero.mp
  calc dotProduct z z = dotProduct z (M.mulVec v) - c * dotProduct z v := by
        simp only [z, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    _ = 0 := by rw [hd, hzv]; ring

/-- The commutant of the orthogonal stabilizer has one longitudinal and one transverse scalar. -/
private lemma haar_stabilizer_matrix_form (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → ℝ) (hv : dotProduct v v = 1)
    (hM : ∀ Q : Matrix.orthogonalGroup (Fin n) ℝ,
      Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) v = v →
      (Q : Matrix (Fin n) (Fin n) ℝ) * M = M * Q) :
    ∃ d : ℝ, M = d • 1 + (dotProduct v (M.mulVec v) - d) • Matrix.vecMulVec v v := by
  let K : Submodule ℝ (Fin n → ℝ) :=
    { carrier := {w | dotProduct v w = 0}
      zero_mem' := by simp
      add_mem' := by intro x y hx hy; simp only [Set.mem_setOf_eq, dotProduct_add] at *; linarith
      smul_mem' := by
        intro t w hw
        simp only [Set.mem_setOf_eq, dotProduct_smul, smul_eq_mul] at *
        rw [hw, mul_zero] }
  have heigen : ∀ w : K, ∃ t : ℝ, M.mulVec w = t • (w : Fin n → ℝ) := by
    intro w
    exact haar_stabilizer_eigen n M v hM w (by rw [dotProduct_comm]; exact w.property)
  let f : K →ₗ[ℝ] K :=
    { toFun := fun w => ⟨M.mulVec w, by
        obtain ⟨t, ht⟩ := heigen w
        change dotProduct v (M.mulVec w) = 0
        rw [ht, dotProduct_smul, w.property, smul_zero]⟩
      map_add' := by intro x y; apply Subtype.ext; exact Matrix.mulVec_add M x y
      map_smul' := by intro t w; apply Subtype.ext; exact Matrix.mulVec_smul M t w }
  obtain ⟨d, hd⟩ := LinearMap.exists_eq_smul_id_of_forall_notLinearIndependent (f := f) (by
    intro w hlin
    obtain ⟨t, ht⟩ := heigen w
    have hf : f w = t • w := Subtype.ext ht
    by_cases hw : w = 0
    · simpa [hw, linearIndependent_fin2] using hlin
    · exact ((LinearIndependent.pair_iff' hw).mp hlin t) hf.symm)
  refine ⟨d, ?_⟩
  have hMv := haar_stabilizer_longitudinal n M v hv hM
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  funext i
  change M.mulVec x i =
    (d • 1 + (dotProduct v (M.mulVec v) - d) • Matrix.vecMulVec v v).mulVec x i
  have hx : dotProduct v (x - dotProduct v x • v) = 0 := by
    rw [dotProduct_sub, dotProduct_smul, hv, smul_eq_mul, mul_one, sub_self]
  have he := congrArg Subtype.val (LinearMap.congr_fun hd ⟨x - dotProduct v x • v, hx⟩)
  change M.mulVec (x - dotProduct v x • v) = d • (x - dotProduct v x • v) at he
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hMv] at he
  have hi := congrFun he i
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul, Pi.add_apply, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul] at hi ⊢
  nlinarith

/-- Moving a finite bilinear form through the entrywise second-moment integral. -/
private lemma haarSignY_bilinear_moment (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) [IsFiniteMeasure ν]
    (a x y : Fin n → ℝ) :
    dotProduct x (Matrix.mulVec (fun k l => ∫ U, haarSignY a U k * haarSignY a U l ∂ν) y) =
      ∫ U, dotProduct x (haarSignY a U) * dotProduct y (haarSignY a U) ∂ν := by
  have hi : ∀ k l, Integrable (fun U =>
      (x k * y l) * (haarSignY a U k * haarSignY a U l)) ν := by
    intro k l
    exact (haarSignY_product_integrable ν n (fun _ => a) measurable_const
      id measurable_id k l).const_mul _
  have hpt : ∀ U, dotProduct x (haarSignY a U) * dotProduct y (haarSignY a U) =
      ∑ k, ∑ l, (x k * y l) * (haarSignY a U k * haarSignY a U l) := by
    intro U
    simp only [dotProduct, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hi k l))]
  simp_rw [integral_finsetSum _ (fun l _ => hi _ l), integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Haar right invariance makes the second-moment matrix commute with the stabilizer. -/
private lemma haarSignY_second_commute (n : ℕ)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (a : Fin n → ℝ) (Q : Matrix.orthogonalGroup (Fin n) ℝ)
    (hQ : Matrix.mulVec (Q : Matrix (Fin n) (Fin n) ℝ) a = a) :
    (Q : Matrix (Fin n) (Fin n) ℝ) *
        Matrix.of (fun k l => ∫ U, haarSignY a U k * haarSignY a U l ∂ν) =
      Matrix.of (fun k l => ∫ U, haarSignY a U k * haarSignY a U l ∂ν) * Q := by
  haveI : IsProbabilityMeasure ν := hν.1
  let M : Matrix (Fin n) (Fin n) ℝ :=
    fun k l => ∫ U, haarSignY a U k * haarSignY a U l ∂ν
  have hconj : (Q : Matrix (Fin n) (Fin n) ℝ).transpose * M * Q = M := by
    ext i j
    calc ((Q : Matrix (Fin n) (Fin n) ℝ).transpose * M * Q) i j
        = dotProduct (fun k => (Q : Matrix (Fin n) (Fin n) ℝ) k i)
            (M.mulVec (fun l => (Q : Matrix (Fin n) (Fin n) ℝ) l j)) := by
          simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
            Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          simp only [mul_assoc]
      _ = ∫ U, dotProduct (fun k => (Q : Matrix (Fin n) (Fin n) ℝ) k i) (haarSignY a U) *
          dotProduct (fun l => (Q : Matrix (Fin n) (Fin n) ℝ) l j) (haarSignY a U) ∂ν :=
        haarSignY_bilinear_moment n ν a _ _
      _ = M i j := (haarSignY_second_stabilizer n ν hν a Q hQ i j).symm
  have horth : (Q : Matrix (Fin n) (Fin n) ℝ) *
      (Q : Matrix (Fin n) (Fin n) ℝ).transpose = 1 :=
    (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).mp Q.property
  change (Q : Matrix (Fin n) (Fin n) ℝ) * M = M * Q
  calc (Q : Matrix (Fin n) (Fin n) ℝ) * M
      = (Q : Matrix (Fin n) (Fin n) ℝ) *
          ((Q : Matrix (Fin n) (Fin n) ℝ).transpose * M * Q) := by rw [hconj]
    _ = ((Q : Matrix (Fin n) (Fin n) ℝ) *
          (Q : Matrix (Fin n) (Fin n) ℝ).transpose) * M * Q := by simp only [mul_assoc]
    _ = M * Q := by rw [horth, one_mul]

/-- The second moment for a unit input, determined by its longitudinal moment and trace. -/
private lemma haarSignY_second_unit (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (v : Fin n → ℝ) (hv : euclidNorm n v = 1) (i j : Fin n) :
    ∫ U, haarSignY v U i * haarSignY v U j ∂ν =
      (if i = j then 1 - 2 / Real.pi else 0) + 2 * (n : ℝ) / Real.pi * (v i * v j) := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hvv : dotProduct v v = 1 := by
    have hs : euclidNorm n v ^ 2 = ∑ k, v k ^ 2 :=
      Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)
    simpa only [hv, one_pow, dotProduct, sq, mul_one] using hs.symm
  let M : Matrix (Fin n) (Fin n) ℝ :=
    fun k l => ∫ U, haarSignY v U k * haarSignY v U l ∂ν
  have hc : dotProduct v (M.mulVec v) = 1 + 2 * ((n : ℝ) - 1) / Real.pi := by
    rw [haarSignY_bilinear_moment n ν v v v]
    simpa only [sq] using haarSignY_longitudinal_unit n hn ν hν v hv
  obtain ⟨d, hd⟩ := haar_stabilizer_matrix_form n M v hvv
    (fun Q hQ => haarSignY_second_commute n ν hν v Q hQ)
  have ht : Matrix.trace M = n := by
    simpa only [Matrix.trace, Matrix.diag, M, sq] using haarSignY_trace_unit n ν hν v hv
  rw [hd, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec, hvv, hc] at ht
  simp only [Fintype.card_fin, smul_eq_mul, mul_one] at ht
  have hdval : d = 1 - 2 / Real.pi := by
    have he : ((n : ℝ) - 1) * (d - (1 - 2 / Real.pi)) = 0 := by
      calc ((n : ℝ) - 1) * (d - (1 - 2 / Real.pi))
          = d * n + (1 + 2 * ((n : ℝ) - 1) / Real.pi - d) - n := by ring
        _ = 0 := by linarith
    have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr hn1.ne'))
  have hcd : dotProduct v (M.mulVec v) - d = 2 * (n : ℝ) / Real.pi := by
    rw [hc, hdval]
    ring
  rw [hcd, hdval] at hd
  have hij := congrFun (congrFun hd i) j
  change M i j = _
  rw [hij]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.vecMulVec_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Part (i), fixed nonzero `a` of `lem:app-sgd-haar-sign` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Haar sign matrix]\label{lem:app-sgd-haar-sign}
Let $U$ be Haar on $O(n)$, $n\ge2$, let $a\in\R^n$ be nonzero, and put
$Y\defeq U^\T\sign(Ua)$. Then
\begin{equation}\label{eqn:app-sgd-haar-sign}
\EE_U\big[Y\tensor Y\big]=\Big(1-\frac2\pi\Big)\Id+\frac{2n}\pi\,\frac{a\tensor a}{\norm a^2}.
\end{equation}
The same holds conditionally on a random nonzero $a$ independent of $U$.
\end{lemma}
```
-/
theorem lem_app_sgd_haar_sign_i (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (a : Fin n → ℝ) (ha : a ≠ 0) (i j : Fin n) :
    ∫ U, haarSignY a U i * haarSignY a U j ∂ν
      = (if i = j then 1 - 2 / Real.pi else 0)
        + 2 * (n : ℝ) / Real.pi * (a i * a j / euclidNorm n a ^ 2) := by
  have hpos := euclidNorm_pos_haar n a ha
  have h := haarSignY_second_unit n hn ν hν ((euclidNorm n a)⁻¹ • a)
    (haar_normalize_unit n a ha) i j
  simp only [haarSignY_pos_smul n a _ (inv_pos.mpr hpos)] at h
  rw [h]
  congr 2
  simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, inv_pow]
  ring

/-- Part (ii), conditional on a random nonzero `a` independent of `U` of `lem:app-sgd-haar-sign` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{lemma}[Haar sign matrix]\label{lem:app-sgd-haar-sign}
Let $U$ be Haar on $O(n)$, $n\ge2$, let $a\in\R^n$ be nonzero, and put
$Y\defeq U^\T\sign(Ua)$. Then
\begin{equation}\label{eqn:app-sgd-haar-sign}
\EE_U\big[Y\tensor Y\big]=\Big(1-\frac2\pi\Big)\Id+\frac{2n}\pi\,\frac{a\tensor a}{\norm a^2}.
\end{equation}
The same holds conditionally on a random nonzero $a$ independent of $U$.
\end{lemma}
```
-/
theorem lem_app_sgd_haar_sign_ii {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (U : Ω → Matrix.orthogonalGroup (Fin n) ℝ) (hU : Measurable U) (hUlaw : P.map U = ν)
    (A : Ω → Fin n → ℝ) (hA : Measurable A) (hind : IndepFun U A P)
    (hA0 : ∀ᵐ ω ∂P, A ω ≠ 0) (i j : Fin n) :
    condExp (MeasurableSpace.comap A inferInstance) P
        (fun ω => haarSignY (A ω) (U ω) i * haarSignY (A ω) (U ω) j)
      =ᵐ[P] fun ω => (if i = j then 1 - 2 / Real.pi else 0)
        + 2 * (n : ℝ) / Real.pi * (A ω i * A ω j / euclidNorm n (A ω) ^ 2) := by
  haveI : IsProbabilityMeasure ν := hν.1
  haveI : PolishSpace (Matrix (Fin n) (Fin n) ℝ) := by
    change PolishSpace (Fin n → Fin n → ℝ)
    infer_instance
  haveI : PolishSpace (Matrix.orthogonalGroup (Fin n) ℝ) :=
    ((continuous_subtype_val : Continuous (fun U : Matrix.orthogonalGroup (Fin n) ℝ =>
      (U : Matrix (Fin n) (Fin n) ℝ))).isClosedEmbedding Subtype.val_injective).polishSpace
  have hkernel : condDistrib U A P =ᵐ[P.map A] Kernel.const (Fin n → ℝ) ν := by
    apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable hA hU
    rw [Measure.compProd_const, hind.symm.map_prod_eq_prod_map_map hA.aemeasurable hU.aemeasurable,
      hUlaw]
  have hkernel' : ∀ᵐ ω ∂P, condDistrib U A P (A ω) = ν :=
    ae_of_ae_map hA.aemeasurable hkernel
  have hc := condExp_prod_ae_eq_integral_condDistrib hA hU.aemeasurable
    (((haarSignY_measurable n i).mul (haarSignY_measurable n j)).stronglyMeasurable)
    (haarSignY_product_integrable P n A hA U hU i j)
  filter_upwards [hc, hkernel', hA0] with ω hω hk ha
  dsimp only [Pi.mul_apply] at hω
  rw [hω, hk]
  exact lem_app_sgd_haar_sign_i n hn ν hν (A ω) ha i j

/-! ## `prop:app-sgd-one-sample` -/

private lemma stdGaussianPi_prod_ne_dirac (n m : ℕ) (hn : 1 ≤ n)
    (p : (Fin n → ℝ) × (Fin m → ℝ)) :
    (stdGaussianPi n).prod (stdGaussianPi m) ≠ Measure.dirac p := by
  intro h
  let i : Fin n := ⟨0, hn⟩
  have hm : Measurable (fun q : (Fin n → ℝ) × (Fin m → ℝ) => q.1 i) := by fun_prop
  have he := congrArg (fun Q : Measure ((Fin n → ℝ) × (Fin m → ℝ)) =>
    Q.map (fun q => q.1 i)) h
  have hl : ((stdGaussianPi n).prod (stdGaussianPi m)).map
      (fun q => q.1 i) = gaussianReal 0 1 := by
    rw [show (fun q : (Fin n → ℝ) × (Fin m → ℝ) => q.1 i) =
        (fun z : Fin n → ℝ => z i) ∘ Prod.fst by rfl,
      ← Measure.map_map (measurable_pi_apply i) measurable_fst,
      Measure.map_fst_prod, measure_univ, one_smul, stdGaussianPi_map_coord]
  have hr : (Measure.dirac p).map (fun q => q.1 i) = Measure.dirac (p.1 i) := by
    exact Measure.map_dirac' hm p
  rw [hl, hr] at he
  have hs := congrArg (fun Q : Measure ℝ => Q {p.1 i}) he
  simp only [Measure.dirac_apply' _ (measurableSet_singleton _), Set.mem_singleton_iff,
    if_pos rfl] at hs
  have hz : gaussianReal 0 1 {p.1 i} = 0 :=
    gaussianReal_absolutelyContinuous 0 one_ne_zero (Real.volume_singleton)
  rw [hz] at hs
  exact (zero_ne_one : (0 : ENNReal) ≠ 1) (by simpa using hs)

private lemma aemeasurable_pair_of_stdGaussianPi_prod_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (n m : ℕ) (hn : 1 ≤ n)
    (Z : Ω → Fin n → ℝ) (W : Ω → Fin m → ℝ)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (stdGaussianPi n).prod (stdGaussianPi m)) :
    AEMeasurable (fun ω => (Z ω, W ω)) P := by
  by_contra hmeas
  rw [Measure.map_of_not_aemeasurable_of_ne_zero hmeas
    (IsProbabilityMeasure.ne_zero P)] at hZW
  exact stdGaussianPi_prod_ne_dirac n m hn _ hZW.symm

private lemma stdGaussianPi_coord_ne_zero_ae (n : ℕ) (i : Fin n) :
    ∀ᵐ z ∂(stdGaussianPi n), z i ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not]
  change (stdGaussianPi n) ((fun z : Fin n → ℝ => z i) ⁻¹' {0}) = 0
  rw [← Measure.map_apply (measurable_pi_apply i) (measurableSet_singleton 0),
    stdGaussianPi_map_coord]
  exact gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton

private lemma one_sample_haar_moment (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (μ : Fin n → ℝ) (hμ : ∀ k, 0 < μ k) (i : Fin n) :
    ∫ g, (∫ V, haarSignY (fun k => Real.sqrt (μ k) * g k) V i ^ 2 ∂ν)
        ∂(stdGaussianPi n)
      = 1 - 2 / Real.pi + 2 * (n : ℝ) / Real.pi *
          ∫ g, μ i * g i ^ 2 / ∑ l, μ l * g l ^ 2 ∂(stdGaussianPi n) := by
  haveI : IsProbabilityMeasure ν := hν.1
  let i0 : Fin n := ⟨0, lt_of_lt_of_le (by omega) hn⟩
  have hA0 : ∀ᵐ g ∂(stdGaussianPi n), (fun k => Real.sqrt (μ k) * g k) ≠ 0 := by
    filter_upwards [stdGaussianPi_coord_ne_zero_ae n i0] with g hg
    intro h
    have := congrFun h i0
    exact hg ((mul_eq_zero.mp this).resolve_left (Real.sqrt_ne_zero'.2 (hμ i0)))
  have hnorm : ∀ g : Fin n → ℝ,
      euclidNorm n (fun k => Real.sqrt (μ k) * g k) ^ 2 = ∑ k, μ k * g k ^ 2 := by
    intro g
    unfold euclidNorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun k _ => sq_nonneg _)]
    apply Finset.sum_congr rfl
    intro k _
    rw [mul_pow, Real.sq_sqrt (hμ k).le]
  have hpoint : ∀ᵐ g ∂(stdGaussianPi n),
      (∫ V, haarSignY (fun k => Real.sqrt (μ k) * g k) V i ^ 2 ∂ν) =
        (1 - 2 / Real.pi) + 2 * (n : ℝ) / Real.pi *
          (μ i * g i ^ 2 / ∑ l, μ l * g l ^ 2) := by
    filter_upwards [hA0] with g hg
    have h := lem_app_sgd_haar_sign_i n hn ν hν
      (fun k => Real.sqrt (μ k) * g k) hg i i
    rw [if_pos rfl, hnorm] at h
    rw [show Real.sqrt (μ i) * g i * (Real.sqrt (μ i) * g i) = μ i * g i ^ 2 by
      rw [show Real.sqrt (μ i) * g i * (Real.sqrt (μ i) * g i) =
        Real.sqrt (μ i) ^ 2 * g i ^ 2 by ring, Real.sq_sqrt (hμ i).le]] at h
    simpa only [sq] using h
  rw [integral_congr_ae hpoint]
  have hratio : Integrable (fun g : Fin n → ℝ =>
      μ i * g i ^ 2 / ∑ l, μ l * g l ^ 2) (stdGaussianPi n) := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      ((measurable_const.mul ((measurable_pi_apply i).pow_const 2)).div
        (Finset.measurable_sum _ fun l _ =>
          measurable_const.mul ((measurable_pi_apply l).pow_const 2))).aestronglyMeasurable ?_
    filter_upwards [] with g
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (mul_nonneg (hμ i).le (sq_nonneg _))
      (Finset.sum_nonneg fun l _ => mul_nonneg (hμ l).le (sq_nonneg _)))]
    by_cases hd : ∑ l, μ l * g l ^ 2 = 0
    · simp [hd]
    · apply (div_le_one (lt_of_le_of_ne
        (Finset.sum_nonneg fun l _ => mul_nonneg (hμ l).le (sq_nonneg _))
        (Ne.symm hd))).2
      exact Finset.single_le_sum (fun l _ => mul_nonneg (hμ l).le (sq_nonneg _))
        (Finset.mem_univ i)
  rw [integral_add (integrable_const _) (hratio.const_mul _), integral_const_mul]
  simp <;> ring

private lemma stdGaussianPi_linear_mul_linear (n : ℕ) (a b : Fin n → ℝ) :
    ∫ z, (∑ q, z q * a q) * (∑ r, z r * b r) ∂(stdGaussianPi n) =
      ∑ q, a q * b q := by
  have h := stdGaussianPi_quadratic_mean n (fun q r => a q * b r)
  rw [show (fun z : Fin n → ℝ => ∑ q, ∑ r, z q * (a q * b r) * z r) =
      fun z => (∑ q, z q * a q) * (∑ r, z r * b r) by
    funext z
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro r _
    ring] at h
  simpa [Matrix.trace, Matrix.diag] using h

private lemma haarSigmaOut_apply (n : ℕ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (μ : Fin n → ℝ) (k l : Fin n) :
    haarSigmaOut V μ k l = ∑ q, (V : Matrix (Fin n) (Fin n) ℝ) k q * μ q *
      (V : Matrix (Fin n) (Fin n) ℝ) l q := by
  simp [haarSigmaOut, Matrix.mul_apply, Matrix.diagonal, Matrix.transpose_apply]

private lemma haarSigmaOut_diag_pos (n : ℕ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (μ : Fin n → ℝ) (hμ : ∀ q, 0 < μ q) (k : Fin n) : 0 < haarSigmaOut V μ k k := by
  rw [haarSigmaOut_apply]
  have heq : (∑ q, (V : Matrix (Fin n) (Fin n) ℝ) k q * μ q *
      (V : Matrix (Fin n) (Fin n) ℝ) k q) =
      ∑ q, μ q * (V : Matrix (Fin n) (Fin n) ℝ) k q ^ 2 := by
    apply Finset.sum_congr rfl
    intro q _
    ring
  rw [heq]
  have hrow : ∑ q, (V : Matrix (Fin n) (Fin n) ℝ) k q ^ 2 = 1 := by
    have horth := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 V.2
    have hdiag := congrFun (congrFun horth k) k
    simpa [Matrix.mul_apply, Matrix.transpose_apply, sq] using hdiag
  obtain ⟨q, hq⟩ : ∃ q, (V : Matrix (Fin n) (Fin n) ℝ) k q ≠ 0 := by
    by_contra h
    push_neg at h
    simp [h] at hrow
  apply Finset.sum_pos'
  · intro r _
    exact mul_nonneg (hμ r).le (sq_nonneg _)
  · exact ⟨q, Finset.mem_univ q, mul_pos (hμ q) (sq_pos_of_ne_zero hq)⟩

private lemma one_sample_arcsine (n : ℕ) (V : Matrix.orthogonalGroup (Fin n) ℝ)
    (μ : Fin n → ℝ) (hμ : ∀ q, 0 < μ q) (k l : Fin n) :
    ∫ z, Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
        (fun q => Real.sqrt (μ q) * z q) k) *
      Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
        (fun q => Real.sqrt (μ q) * z q) l) ∂(stdGaussianPi n) =
      sigmaSignMat (haarSigmaOut V μ) k l := by
  let a : Fin n → ℝ := fun q => Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q
  let b : Fin n → ℝ := fun q => Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q
  let g₁ : (Fin n → ℝ) → ℝ := fun z => ∑ q, z q * a q
  let g₂ : (Fin n → ℝ) → ℝ := fun z => ∑ q, z q * b q
  have hg₁ : g₁ = fun z => Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
      (fun q => Real.sqrt (μ q) * z q) k := by
    funext z
    simp only [g₁, a, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hg₂ : g₂ = fun z => Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
      (fun q => Real.sqrt (μ q) * z q) l := by
    funext z
    simp only [g₂, b, Matrix.mulVec]
    apply Finset.sum_congr rfl
    intro q _
    ring
  have hmap : (stdGaussianPi n).map (WithLp.toLp 2 :
      (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) =
      stdGaussian (EuclideanSpace ℝ (Fin n)) := by
    unfold stdGaussianPi
    exact map_pi_eq_stdGaussian
  have hX : HasGaussianLaw (WithLp.toLp 2 :
      (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) (stdGaussianPi n) :=
    (show HasLaw (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      (stdGaussian (EuclideanSpace ℝ (Fin n))) (stdGaussianPi n) from
      ⟨by fun_prop, hmap⟩).hasGaussianLaw
  let av : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  let bv : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  let L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ × ℝ :=
    (innerSL ℝ av).prod (innerSL ℝ bv)
  have hlaw : HasGaussianLaw (fun z => (g₁ z, g₂ z)) (stdGaussianPi n) := by
    convert hX.map_fun L using 1
    funext z
    simp [L, av, bv, g₁, g₂, a, b, PiLp.inner_apply, mul_comm]
  have hmean₁ : ∫ z, g₁ z ∂(stdGaussianPi n) = 0 := by
    have hm := integral_map (μ := stdGaussianPi n)
      (φ := fun z : Fin n → ℝ => ∑ q, z q * a q)
      (Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).mul measurable_const).aemeasurable
      (f := id) aestronglyMeasurable_id
    rw [stdGaussianPi_linear_map] at hm
    change (∫ y, y ∂(gaussianReal 0 (Real.toNNReal (∑ q, a q ^ 2)))) = _ at hm
    rw [integral_id_gaussianReal] at hm
    simpa only [g₁, id_eq] using hm.symm
  have hmean₂ : ∫ z, g₂ z ∂(stdGaussianPi n) = 0 := by
    have hm := integral_map (μ := stdGaussianPi n)
      (φ := fun z : Fin n → ℝ => ∑ q, z q * b q)
      (Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).mul measurable_const).aemeasurable
      (f := id) aestronglyMeasurable_id
    rw [stdGaussianPi_linear_map] at hm
    change (∫ y, y ∂(gaussianReal 0 (Real.toNNReal (∑ q, b q ^ 2)))) = _ at hm
    rw [integral_id_gaussianReal] at hm
    simpa only [g₂, id_eq] using hm.symm
  have hva : variance g₁ (stdGaussianPi n) = haarSigmaOut V μ k k := by
    rw [variance_eq_sub hlaw.fst.memLp_two, hmean₁]
    norm_num
    change (∫ z, g₁ z ^ 2 ∂(stdGaussianPi n)) = haarSigmaOut V μ k k
    rw [show (fun z => g₁ z ^ 2) = fun z => g₁ z * g₁ z by funext z; ring,
      stdGaussianPi_linear_mul_linear]
    rw [haarSigmaOut_apply]
    apply Finset.sum_congr rfl
    intro q _
    simp only [a]
    rw [show (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q) *
      (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q) =
      (V : Matrix (Fin n) (Fin n) ℝ) k q * μ q *
        (V : Matrix (Fin n) (Fin n) ℝ) k q by
      rw [show Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q *
        (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q) =
        Real.sqrt (μ q) ^ 2 * (V : Matrix (Fin n) (Fin n) ℝ) k q ^ 2 by ring,
        Real.sq_sqrt (hμ q).le]; ring]
  have hvb : variance g₂ (stdGaussianPi n) = haarSigmaOut V μ l l := by
    rw [variance_eq_sub hlaw.snd.memLp_two, hmean₂]
    norm_num
    change (∫ z, g₂ z ^ 2 ∂(stdGaussianPi n)) = haarSigmaOut V μ l l
    rw [show (fun z => g₂ z ^ 2) = fun z => g₂ z * g₂ z by funext z; ring,
      stdGaussianPi_linear_mul_linear]
    rw [haarSigmaOut_apply]
    apply Finset.sum_congr rfl
    intro q _
    simp only [b]
    rw [show (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q) *
      (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q) =
      (V : Matrix (Fin n) (Fin n) ℝ) l q * μ q *
        (V : Matrix (Fin n) (Fin n) ℝ) l q by
      rw [show Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q *
        (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q) =
        Real.sqrt (μ q) ^ 2 * (V : Matrix (Fin n) (Fin n) ℝ) l q ^ 2 by ring,
        Real.sq_sqrt (hμ q).le]; ring]
  have hcross : ∫ z, g₁ z * g₂ z ∂(stdGaussianPi n) = haarSigmaOut V μ k l := by
    rw [stdGaussianPi_linear_mul_linear, haarSigmaOut_apply]
    apply Finset.sum_congr rfl
    intro q _
    simp only [a, b]
    rw [show (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q) *
      (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q) =
      (V : Matrix (Fin n) (Fin n) ℝ) k q * μ q *
        (V : Matrix (Fin n) (Fin n) ℝ) l q by
      rw [show Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) k q *
        (Real.sqrt (μ q) * (V : Matrix (Fin n) (Fin n) ℝ) l q) =
        Real.sqrt (μ q) ^ 2 * (V : Matrix (Fin n) (Fin n) ℝ) k q *
          (V : Matrix (Fin n) (Fin n) ℝ) l q by ring,
        Real.sq_sqrt (hμ q).le]; ring]
  have harc := (lem_app_sgd_arcsine_i (stdGaussianPi n) g₁ g₂ hlaw hmean₁ hmean₂
    (hva.symm ▸ haarSigmaOut_diag_pos n V μ hμ k)
    (hvb.symm ▸ haarSigmaOut_diag_pos n V μ hμ l)).2.2
  have harc' :
      (∫ z, Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) k) *
        Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) l) ∂(stdGaussianPi n)) =
        2 / Real.pi * Real.arcsin (gaussCorr (stdGaussianPi n) g₁ g₂) := by
    simpa only [hg₁, hg₂] using harc
  rw [harc']
  unfold sigmaSignMat gaussCorr
  rw [hva, hvb, hcross]

private lemma one_sample_sigma_eq_haar (n : ℕ)
    (V : Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ)
    (hμ : ∀ q, 0 < μ q) (i : Fin n) :
    ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
        sigmaSignMat (haarSigmaOut V μ) k l *
        (V : Matrix (Fin n) (Fin n) ℝ) l i =
      ∫ z, haarSignY (fun q => Real.sqrt (μ q) * z q) V i ^ 2
        ∂(stdGaussianPi n) := by
  have hint : ∀ k l : Fin n, Integrable (fun z : Fin n → ℝ =>
      ((V : Matrix (Fin n) (Fin n) ℝ) k i *
        (Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) k) *
        Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) l))) *
        (V : Matrix (Fin n) (Fin n) ℝ) l i) (stdGaussianPi n) := by
    intro k l
    have hs : Measurable Real.sign := by
      unfold Real.sign
      exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
        (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)
    have hyk : Measurable (fun z : Fin n → ℝ =>
        Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) k) := by fun_prop
    have hyl : Measurable (fun z : Fin n → ℝ =>
        Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) l) := by fun_prop
    refine Integrable.mono' (integrable_const
      (|(V : Matrix (Fin n) (Fin n) ℝ) k i * (V : Matrix (Fin n) (Fin n) ℝ) l i|))
      ((measurable_const.mul ((hs.comp hyk).mul (hs.comp hyl))).mul
        measurable_const).aestronglyMeasurable ?_
    filter_upwards [] with z
    have hs : ∀ x : ℝ, ‖Real.sign x‖ ≤ 1 := by
      intro x
      rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
    rw [Real.norm_eq_abs, abs_mul, abs_mul, mul_assoc]
    have hsign : |Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) k) *
        Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) l)| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul, Real.norm_eq_abs] using
        mul_le_mul (hs _) (hs _) (norm_nonneg _) zero_le_one
    calc |(V : Matrix (Fin n) (Fin n) ℝ) k i| *
          (|Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
            (fun q => Real.sqrt (μ q) * z q) k) *
          Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
            (fun q => Real.sqrt (μ q) * z q) l)| *
            |(V : Matrix (Fin n) (Fin n) ℝ) l i|)
        ≤ |(V : Matrix (Fin n) (Fin n) ℝ) k i| *
          (1 * |(V : Matrix (Fin n) (Fin n) ℝ) l i|) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hsign (abs_nonneg _)) (abs_nonneg _)
      _ = |(V : Matrix (Fin n) (Fin n) ℝ) k i *
          (V : Matrix (Fin n) (Fin n) ℝ) l i| := by rw [abs_mul, one_mul]
  rw [show (∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
      sigmaSignMat (haarSigmaOut V μ) k l *
      (V : Matrix (Fin n) (Fin n) ℝ) l i) =
      ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
        (∫ z, Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) k) *
          Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
          (fun q => Real.sqrt (μ q) * z q) l) ∂(stdGaussianPi n)) *
        (V : Matrix (Fin n) (Fin n) ℝ) l i by
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    rw [one_sample_arcsine n V μ hμ k l]]
  have hsq : (fun z : Fin n → ℝ =>
      haarSignY (fun q => Real.sqrt (μ q) * z q) V i ^ 2) =
      fun z => ∑ k, ∑ l,
        ((V : Matrix (Fin n) (Fin n) ℝ) k i *
          (Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
            (fun q => Real.sqrt (μ q) * z q) k) *
          Real.sign (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
            (fun q => Real.sqrt (μ q) * z q) l))) *
          (V : Matrix (Fin n) (Fin n) ℝ) l i := by
    funext z
    unfold haarSignY Matrix.mulVec dotProduct
    simp only [Matrix.transpose_apply]
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  rw [hsq, integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => hint k l)]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finsetSum _ (fun l _ => hint k l)]
  apply Finset.sum_congr rfl
  intro l _
  symm
  rw [integral_mul_const, integral_const_mul]

private lemma one_sample_second_equality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (U : Ω → Matrix.orthogonalGroup (Fin n) ℝ) (hU : Measurable U) (hUlaw : P.map U = ν)
    (μ : Fin n → ℝ) (hμ : ∀ k, 0 < μ k) (i : Fin n) :
    (∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut (U ω) μ) k l *
          (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P) =
      1 - 2 / Real.pi + 2 * (n : ℝ) / Real.pi *
        ∫ g, μ i * g i ^ 2 / ∑ l, μ l * g l ^ 2 ∂(stdGaussianPi n) := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hA : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ × (Fin n → ℝ) =>
      fun q => Real.sqrt (μ q) * p.2 q) := by fun_prop
  have hFint : Integrable (Function.uncurry (fun V g =>
      haarSignY (fun q => Real.sqrt (μ q) * g q) V i ^ 2))
      (ν.prod (stdGaussianPi n)) := by
    have hp := haarSignY_product_integrable (ν.prod (stdGaussianPi n)) n
      (fun p => fun q => Real.sqrt (μ q) * p.2 q) hA
      (fun p => p.1) measurable_fst i i
    refine hp.congr (Filter.Eventually.of_forall fun p => ?_)
    change haarSignY (fun q => Real.sqrt (μ q) * p.2 q) p.1 i *
      haarSignY (fun q => Real.sqrt (μ q) * p.2 q) p.1 i =
      haarSignY (fun q => Real.sqrt (μ q) * p.2 q) p.1 i ^ 2
    rw [sq]
  have hswap := integral_integral_swap hFint
  have hGae : AEStronglyMeasurable
      (fun V : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut V μ) k l *
          (V : Matrix (Fin n) (Fin n) ℝ) l i) ν := by
    refine (hFint.integral_prod_left.aestronglyMeasurable.congr ?_)
    filter_upwards [] with V
    exact (one_sample_sigma_eq_haar n V μ hμ i).symm
  have hGae' : AEStronglyMeasurable
      (fun V : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut V μ) k l *
          (V : Matrix (Fin n) (Fin n) ℝ) l i) (P.map U) := by
    rwa [hUlaw]
  calc
    (∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut (U ω) μ) k l *
          (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P)
        = ∫ V, ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut V μ) k l *
          (V : Matrix (Fin n) (Fin n) ℝ) l i ∂ν := by
            calc
              _ = ∫ V, ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
                    sigmaSignMat (haarSigmaOut V μ) k l *
                    (V : Matrix (Fin n) (Fin n) ℝ) l i ∂(P.map U) :=
                (integral_map hU.aemeasurable hGae').symm
              _ = _ := by rw [hUlaw]
    _ = ∫ V, ∫ g, haarSignY (fun q => Real.sqrt (μ q) * g q) V i ^ 2
          ∂(stdGaussianPi n) ∂ν := by
            congr 1
            funext V
            exact one_sample_sigma_eq_haar n V μ hμ i
    _ = ∫ g, ∫ V, haarSignY (fun q => Real.sqrt (μ q) * g q) V i ^ 2 ∂ν
          ∂(stdGaussianPi n) := hswap
    _ = _ := one_sample_haar_moment n hn ν hν μ hμ i

private lemma real_sign_mul (x y : ℝ) : Real.sign (x * y) = Real.sign x * Real.sign y := by
  rcases lt_trichotomy x 0 with hx | hx | hx <;>
    rcases lt_trichotomy y 0 with hy | hy | hy <;>
    simp [hx, hy, Real.sign_of_neg, Real.sign_of_pos, mul_neg, mul_pos,
      mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]

private lemma stdGaussianPi_linear_ne_zero_ae (n : ℕ) (a : Fin n → ℝ) (ha : a ≠ 0) :
    ∀ᵐ z ∂(stdGaussianPi n), ∑ q, z q * a q ≠ 0 := by
  have hsum : 0 < ∑ q, a q ^ 2 := by
    obtain ⟨q, hq⟩ : ∃ q, a q ≠ 0 := by
      by_contra h
      push_neg at h
      exact ha (funext h)
    exact Finset.sum_pos' (fun r _ => sq_nonneg _) ⟨q, Finset.mem_univ q, sq_pos_of_ne_zero hq⟩
  rw [ae_iff]
  simp only [ne_eq, not_not]
  change (stdGaussianPi n) ((fun z : Fin n → ℝ => ∑ q, z q * a q) ⁻¹' {0}) = 0
  have hlin : Measurable (fun z : Fin n → ℝ => ∑ q, z q * a q) :=
    Finset.measurable_sum _ fun q _ => (measurable_pi_apply q).mul measurable_const
  rw [← Measure.map_apply hlin (measurableSet_singleton 0),
    stdGaussianPi_linear_map]
  apply gaussianReal_absolutelyContinuous 0
  · rw [Ne, Real.toNNReal_eq_zero, not_le]
    exact hsum
  · exact Real.volume_singleton

private lemma stdGaussianPi_mulVec_ne_zero_ae {n m : ℕ}
    (Δ : Matrix (Fin n) (Fin m) ℝ) (hΔ : Δ ≠ 0) :
    ∀ᵐ w ∂(stdGaussianPi m), Δ.mulVec w ≠ 0 := by
  obtain ⟨k, l, hkl⟩ : ∃ k l, Δ k l ≠ 0 := by
    by_contra h
    push_neg at h
    exact hΔ (Matrix.ext fun k l => h k l)
  have hrow : (fun l => Δ k l) ≠ 0 := fun h => hkl (congrFun h l)
  filter_upwards [stdGaussianPi_linear_ne_zero_ae m (fun l => Δ k l) hrow] with w hw
  intro h
  apply hw
  have := congrFun h k
  change (∑ x, Δ k x * w x) = 0 at this
  simpa only [mul_comm] using this

private lemma one_sample_residual_ne_zero_ae {n m : ℕ}
    (V : Matrix.orthogonalGroup (Fin n) ℝ) (μ : Fin n → ℝ) (hμ : ∀ q, 0 < μ q)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (hΔ : Δ ≠ 0) :
    ∀ᵐ p ∂(stdGaussianPi n).prod (stdGaussianPi m),
      dotProduct (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
        (fun q => Real.sqrt (μ q) * p.1 q)) (Δ.mulVec p.2) ≠ 0 := by
  have hm : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) |
      dotProduct (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
        (fun q => Real.sqrt (μ q) * p.1 q)) (Δ.mulVec p.2) ≠ 0} := by
    exact (measurableSet_singleton 0).compl.preimage (by fun_prop)
  rw [Measure.ae_prod_iff_ae_ae hm, Measure.ae_ae_comm hm]
  filter_upwards [stdGaussianPi_mulVec_ne_zero_ae Δ hΔ] with w hDw
  let t := Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ).transpose (Δ.mulVec w)
  have ht : t ≠ 0 := by
    intro ht0
    apply hDw
    have horth : (V : Matrix (Fin n) (Fin n) ℝ) *
        (V : Matrix (Fin n) (Fin n) ℝ).transpose = 1 :=
      (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 V.2
    have hv := congrArg (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)) ht0
    dsimp only [t] at hv
    rw [Matrix.mulVec_mulVec, horth, Matrix.one_mulVec, Matrix.mulVec_zero] at hv
    exact hv
  have ha : (fun q => Real.sqrt (μ q) * t q) ≠ 0 := by
    intro h
    apply ht
    funext q
    have hq := congrFun h q
    exact (mul_eq_zero.mp hq).resolve_left (Real.sqrt_ne_zero'.2 (hμ q))
  filter_upwards [stdGaussianPi_linear_ne_zero_ae n
    (fun q => Real.sqrt (μ q) * t q) ha] with z hz
  intro hres
  apply hz
  rw [← hres]
  symm
  rw [dotProduct_comm, Matrix.dotProduct_mulVec,
    ← Matrix.transpose_transpose (V : Matrix (Fin n) (Fin n) ℝ), Matrix.vecMul_transpose]
  unfold t dotProduct
  apply Finset.sum_congr rfl
  intro q _
  ring

private lemma one_sample_cancel {n m : ℕ} (μ : Fin n → ℝ)
    (V : Matrix.orthogonalGroup (Fin n) ℝ) (z : Fin n → ℝ) (w : Fin m → ℝ)
    (Δ : Matrix (Fin n) (Fin m) ℝ) (i : Fin n)
    (hr : dotProduct (Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
      (fun q => Real.sqrt (μ q) * z q)) (Δ.mulVec w) ≠ 0)
    (hw : ∀ j, w j ≠ 0) :
    ∑ j, (∑ k, oneSampleSign Δ (oneSampleBatch μ V z w) k j *
        (V : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 =
      (m : ℝ) * haarSignY (fun q => Real.sqrt (μ q) * z q) V i ^ 2 := by
  let y := Matrix.mulVec (V : Matrix (Fin n) (Fin n) ℝ)
    (fun q => Real.sqrt (μ q) * z q)
  have happ : ∀ k j, oneSampleSign Δ (oneSampleBatch μ V z w) k j =
      Real.sign (dotProduct y (Δ.mulVec w)) * Real.sign (y k) * Real.sign (w j) := by
    intro k j
    unfold oneSampleSign
    change Real.sign (physGrad Δ (oneSampleBatch μ V z w) k j) = _
    unfold physGrad residual oneSampleBatch
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      Nat.cast_one, div_one, one_mul]
    change Real.sign (dotProduct y (Δ.mulVec w) * (y k * w j)) = _
    rw [real_sign_mul, real_sign_mul]
    ring
  have hsr : Real.sign (dotProduct y (Δ.mulVec w)) ^ 2 = 1 := by
    change dotProduct y (Δ.mulVec w) ≠ 0 at hr
    rcases Real.sign_apply_eq_of_ne_zero _ hr with h | h <;> simp [h]
  have hsw : ∀ j, Real.sign (w j) ^ 2 = 1 := by
    intro j
    rcases Real.sign_apply_eq_of_ne_zero _ (hw j) with h | h <;> simp [h]
  have hsum : ∀ j, (∑ k, oneSampleSign Δ (oneSampleBatch μ V z w) k j *
      (V : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 =
      haarSignY (fun q => Real.sqrt (μ q) * z q) V i ^ 2 := by
    intro j
    simp_rw [happ]
    rw [show (∑ k, (Real.sign (dotProduct y (Δ.mulVec w)) * Real.sign (y k) *
        Real.sign (w j)) * (V : Matrix (Fin n) (Fin n) ℝ) k i) =
        Real.sign (dotProduct y (Δ.mulVec w)) * Real.sign (w j) *
          haarSignY (fun q => Real.sqrt (μ q) * z q) V i by
      change (∑ k, (Real.sign (dotProduct y (Δ.mulVec w)) * Real.sign (y k) *
        Real.sign (w j)) * (V : Matrix (Fin n) (Fin n) ℝ) k i) =
        Real.sign (dotProduct y (Δ.mulVec w)) * Real.sign (w j) *
          ∑ k, (V : Matrix (Fin n) (Fin n) ℝ) k i * Real.sign (y k)
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring]
    rw [mul_pow, mul_pow, hsr, hsw]
    ring
  simp_rw [hsum]
  simp

private lemma real_sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact measurable_const.ite (measurableSet_lt measurable_id measurable_const)
    (measurable_const.ite (measurableSet_lt measurable_const measurable_id) measurable_const)

private lemma one_sample_first_equality {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n m : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (U : Ω → Matrix.orthogonalGroup (Fin n) ℝ) (hU : Measurable U) (hUlaw : P.map U = ν)
    (Z : Ω → Fin n → ℝ) (W : Ω → Fin m → ℝ)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (stdGaussianPi n).prod (stdGaussianPi m))
    (hind : IndepFun U (fun ω => (Z ω, W ω)) P)
    (μ : Fin n → ℝ) (hμ : ∀ k, 0 < μ k)
    (Δfun : Matrix.orthogonalGroup (Fin n) ℝ → Matrix (Fin n) (Fin m) ℝ)
    (hΔ : Measurable Δfun) (hΔ0 : ∀ᵐ ω ∂P, Δfun (U ω) ≠ 0) (i : Fin n) :
    (∫ ω, ∑ j, (∑ k, oneSampleSign (Δfun (U ω))
          (oneSampleBatch μ (U ω) (Z ω) (W ω)) k j *
          (U ω : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 ∂P) =
      (m : ℝ) * ∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i *
        sigmaSignMat (haarSigmaOut (U ω) μ) k l *
        (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P := by
  haveI : IsProbabilityMeasure ν := hν.1
  have hpair : AEMeasurable (fun ω => (Z ω, W ω)) P :=
    aemeasurable_pair_of_stdGaussianPi_prod_law P n m (by omega) Z W hZW
  have hJ : AEMeasurable (fun ω => (U ω, (Z ω, W ω))) P :=
    hU.aemeasurable.prodMk hpair
  have hJlaw : P.map (fun ω => (U ω, (Z ω, W ω))) =
      ν.prod ((stdGaussianPi n).prod (stdGaussianPi m)) := by
    rw [hind.map_prod_eq_prod_map_map hU.aemeasurable hpair, hUlaw, hZW]
  let L := fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      ((Fin n → ℝ) × (Fin m → ℝ)) =>
    ∑ j, (∑ k, oneSampleSign (Δfun p.1) (oneSampleBatch μ p.1 p.2.1 p.2.2) k j *
      (p.1 : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2
  let R := fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      ((Fin n → ℝ) × (Fin m → ℝ)) =>
    (m : ℝ) * haarSignY (fun q => Real.sqrt (μ q) * p.2.1 q) p.1 i ^ 2
  have hA : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      ((Fin n → ℝ) × (Fin m → ℝ)) =>
      fun q => Real.sqrt (μ q) * p.2.1 q) := by fun_prop
  have hV : Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      ((Fin n → ℝ) × (Fin m → ℝ)) => p.1) := measurable_fst
  have hRmeas : Measurable R := by
    exact measurable_const.mul (((haarSignY_measurable n i).comp (hA.prodMk hV)).pow_const 2)
  have hsamp : ∀ k j, Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
      ((Fin n → ℝ) × (Fin m → ℝ)) =>
      oneSampleSign (Δfun p.1) (oneSampleBatch μ p.1 p.2.1 p.2.2) k j) := by
    intro k j
    unfold oneSampleSign
    exact real_sign_measurable.comp (by
      change Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        ((Fin n → ℝ) × (Fin m → ℝ)) =>
        physGrad (Δfun p.1) (oneSampleBatch μ p.1 p.2.1 p.2.2) k j)
      unfold physGrad residual oneSampleBatch
      fun_prop)
  have hLmeas : Measurable L := by
    have hentry : ∀ k, Measurable (fun p : Matrix.orthogonalGroup (Fin n) ℝ ×
        ((Fin n → ℝ) × (Fin m → ℝ)) =>
        (p.1 : Matrix (Fin n) (Fin n) ℝ) k i) := by
      intro k
      exact (measurable_pi_apply i).comp ((measurable_pi_apply k).comp
        (measurable_subtype_coe.comp measurable_fst))
    exact Finset.measurable_sum _ fun j _ =>
      (Finset.measurable_sum _ fun k _ =>
        (hsamp k j).mul (hentry k)).pow_const 2
  have hΔν : ∀ᵐ V ∂ν, Δfun V ≠ 0 := by
    rw [← hUlaw, ae_map_iff hU.aemeasurable]
    · exact hΔ0
    · exact (measurableSet_singleton (0 : Matrix (Fin n) (Fin m) ℝ)).compl.preimage hΔ
  have hw : ∀ᵐ w ∂(stdGaussianPi m), ∀ j, w j ≠ 0 := by
    rw [ae_all_iff]
    exact fun j => stdGaussianPi_coord_ne_zero_ae m j
  have hwp : ∀ᵐ p ∂(stdGaussianPi n).prod (stdGaussianPi m), ∀ j, p.2 j ≠ 0 := by
    have hmset : MeasurableSet {p : (Fin n → ℝ) × (Fin m → ℝ) | ∀ j, p.2 j ≠ 0} := by
      have hwsnd : Measurable (fun p : (Fin n → ℝ) × (Fin m → ℝ) => p.2) := measurable_snd
      have hs := MeasurableSet.iInter fun j => (measurableSet_singleton 0).compl.preimage
        ((measurable_pi_apply j).comp hwsnd)
      convert hs using 1
      ext p
      simp
    rw [Measure.ae_prod_iff_ae_ae hmset]
    filter_upwards [] with z
    exact hw
  have hcancel : L =ᵐ[ν.prod ((stdGaussianPi n).prod (stdGaussianPi m))] R := by
    have hmset : MeasurableSet {p | L p = R p} :=
      hLmeas.stronglyMeasurable.measurableSet_eq_fun hRmeas.stronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae hmset).2
    filter_upwards [hΔν] with V hDV
    filter_upwards [one_sample_residual_ne_zero_ae V μ hμ (Δfun V) hDV, hwp] with p hr hp
    exact one_sample_cancel μ V p.1 p.2 (Δfun V) i hr hp
  have hRint : Integrable R (ν.prod ((stdGaussianPi n).prod (stdGaussianPi m))) := by
    refine Integrable.mono' (integrable_const ((m : ℝ) * (n : ℝ) ^ 2))
      hRmeas.aestronglyMeasurable ?_
    filter_upwards [] with p
    rw [Real.norm_eq_abs, abs_mul, abs_sq, abs_of_nonneg (Nat.cast_nonneg m)]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
    simpa only [sq_abs, abs_of_nonneg (show (0 : ℝ) ≤ n by positivity)] using
      pow_le_pow_left₀ (abs_nonneg _) (haarSignY_abs_le n _ _ i) 2
  have hLint : Integrable L (ν.prod ((stdGaussianPi n).prod (stdGaussianPi m))) :=
    hRint.congr hcancel.symm
  have hLae : AEStronglyMeasurable L
      (P.map (fun ω => (U ω, (Z ω, W ω)))) := by
    rw [hJlaw]
    exact hLint.aestronglyMeasurable
  have hhaarint : Integrable (Function.uncurry (fun V z =>
      haarSignY (fun q => Real.sqrt (μ q) * z q) V i ^ 2))
      (ν.prod (stdGaussianPi n)) := by
    have hp := haarSignY_product_integrable (ν.prod (stdGaussianPi n)) n
      (fun p => fun q => Real.sqrt (μ q) * p.2 q) (by fun_prop)
      (fun p => p.1) measurable_fst i i
    refine hp.congr (Filter.Eventually.of_forall fun p => ?_)
    change _ * _ = _ ^ 2
    rw [sq]
  have hGae : AEStronglyMeasurable
      (fun V : Matrix.orthogonalGroup (Fin n) ℝ =>
        ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut V μ) k l *
          (V : Matrix (Fin n) (Fin n) ℝ) l i) ν := by
    refine (hhaarint.integral_prod_left.aestronglyMeasurable.congr ?_)
    filter_upwards [] with V
    exact (one_sample_sigma_eq_haar n V μ hμ i).symm
  calc
    (∫ ω, ∑ j, (∑ k, oneSampleSign (Δfun (U ω))
          (oneSampleBatch μ (U ω) (Z ω) (W ω)) k j *
          (U ω : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 ∂P)
        = ∫ p, L p ∂(ν.prod ((stdGaussianPi n).prod (stdGaussianPi m))) := by
          rw [← hJlaw, integral_map hJ hLae]
    _ = ∫ p, R p ∂(ν.prod ((stdGaussianPi n).prod (stdGaussianPi m))) :=
      integral_congr_ae hcancel
    _ = (m : ℝ) * ∫ V, ∫ z, haarSignY
          (fun q => Real.sqrt (μ q) * z q) V i ^ 2 ∂(stdGaussianPi n) ∂ν := by
      rw [integral_prod R hRint]
      simp only [R]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with V
      calc
        (∫ p, (m : ℝ) * haarSignY
            (fun q => Real.sqrt (μ q) * p.1 q) V i ^ 2
            ∂(stdGaussianPi n).prod (stdGaussianPi m))
            = ∫ p, ((m : ℝ) * haarSignY
                (fun q => Real.sqrt (μ q) * p.1 q) V i ^ 2) * (1 : ℝ)
                ∂(stdGaussianPi n).prod (stdGaussianPi m) := by
                  congr 1
                  funext p
                  ring
        _ = (∫ z, (m : ℝ) * haarSignY
              (fun q => Real.sqrt (μ q) * z q) V i ^ 2 ∂(stdGaussianPi n)) *
              ∫ _w : Fin m → ℝ, (1 : ℝ) ∂(stdGaussianPi m) :=
                integral_prod_mul (μ := stdGaussianPi n) (ν := stdGaussianPi m)
                  (L := ℝ) (fun z => (m : ℝ) * haarSignY
                    (fun q => Real.sqrt (μ q) * z q) V i ^ 2) (fun _w => 1)
        _ = (m : ℝ) * ∫ z, haarSignY
              (fun q => Real.sqrt (μ q) * z q) V i ^ 2 ∂(stdGaussianPi n) := by
                simp [integral_const_mul]
    _ = (m : ℝ) * ∫ V, ∑ k, ∑ l, (V : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut V μ) k l *
          (V : Matrix (Fin n) (Fin n) ℝ) l i ∂ν := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with V
      exact (one_sample_sigma_eq_haar n V μ hμ i).symm
    _ = (m : ℝ) * ∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i *
          sigmaSignMat (haarSigmaOut (U ω) μ) k l *
          (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P := by
      congr 1
      have hGae' := hGae
      rw [← hUlaw] at hGae'
      exact ((integral_map hU.aemeasurable hGae').symm.trans (by rw [hUlaw])).symm


/-- Part (both equalities, as one declaration) of `prop:app-sgd-one-sample` (snapshot `cr-2026-10-23`). LaTeX statement, verbatim:
```latex
\begin{proposition}[One sample]\label{prop:app-sgd-one-sample}
Let $B=1$, $\Nout\ge2$, $\Sigmaout=U\Lambda U^\T$ with $U$ Haar and
$\Lambda=\diag(\mu_i)\succ0$, and $\Sigmain=\Idin$. Let $\Delta$ be any
function of $U$ with $\Delta\ne0$ almost surely, and $S=\sign(G^\circ)$. Then
\[
\EE\norm{S^\T u_i}^2=\Nin\,\EE\big[u_i^\T\Sigmaoutsign u_i\big]=\Nin\Big(1-\frac2\pi+\frac{2\Nout}\pi\,\EE\frac{\mu_ig_i^2}{\sum_l\mu_lg_l^2}\Big),
\]
where $(\Sigmaoutsign)_{kl}\defeq\frac2\pi\arcsin\big((\Sigmaout)_{kl}/\sqrt{(\Sigmaout)_{kk}(\Sigmaout)_{ll}}\big)$
and $g$ is a standard Gaussian vector in $\R^{\Nout}$.
\end{proposition}
```
-/
theorem prop_app_sgd_one_sample {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (n m : ℕ) (hn : 2 ≤ n)
    (ν : Measure (Matrix.orthogonalGroup (Fin n) ℝ)) (hν : IsOrthHaar ν)
    (U : Ω → Matrix.orthogonalGroup (Fin n) ℝ) (hU : Measurable U) (hUlaw : P.map U = ν)
    (Z : Ω → Fin n → ℝ) (W : Ω → Fin m → ℝ)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (stdGaussianPi n).prod (stdGaussianPi m))
    (hind : IndepFun U (fun ω => (Z ω, W ω)) P)
    (μ : Fin n → ℝ) (hμ : ∀ k, 0 < μ k)
    (Δfun : Matrix.orthogonalGroup (Fin n) ℝ → Matrix (Fin n) (Fin m) ℝ) (hΔ : Measurable Δfun)
    (hΔ0 : ∀ᵐ ω ∂P, Δfun (U ω) ≠ 0) (i : Fin n) :
    (∫ ω, ∑ j, (∑ k, oneSampleSign (Δfun (U ω)) (oneSampleBatch μ (U ω) (Z ω) (W ω)) k j
          * (U ω : Matrix (Fin n) (Fin n) ℝ) k i) ^ 2 ∂P
        = (m : ℝ) * ∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i
            * sigmaSignMat (haarSigmaOut (U ω) μ) k l * (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P) ∧
    (∫ ω, ∑ k, ∑ l, (U ω : Matrix (Fin n) (Fin n) ℝ) k i
            * sigmaSignMat (haarSigmaOut (U ω) μ) k l * (U ω : Matrix (Fin n) (Fin n) ℝ) l i ∂P
        = 1 - 2 / Real.pi + 2 * (n : ℝ) / Real.pi *
            ∫ g, μ i * g i ^ 2 / ∑ l, μ l * g l ^ 2 ∂(stdGaussianPi n)) := by
  constructor
  · exact one_sample_first_equality P n m hn ν hν U hU hUlaw Z W hZW hind μ hμ
      Δfun hΔ hΔ0 i
  · exact one_sample_second_equality P n hn ν hν U hU hUlaw μ hμ i

end Muon.SignSGD
