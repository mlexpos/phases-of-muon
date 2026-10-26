import Muon.Foundations.Conventions
import Muon.Foundations.Nuclear

/-!
# Appendix B: finite-dimensional resolvent algebra

Snapshot `cr-2026-10-22`. Source: `sections/02-deterministic-equivalents/section.tex`,
the finite tools of the Gram closure (`lem:app-de-resolvent` at l.607, `lem:app-de-deletion`
at l.667, `lem:app-de-coeff` at l.821) and the nuclear-norm Lipschitz bound
`lem:app-de-lipschitz` (l.1078). This module merges the card's `Resolvent.lean` and
`Deletion.lean` (CARD §5, WP L-B.5).

Deterministic: no probability space. Resolvents are `R_s(M) = (MMᵀ + s Id)⁻¹` with `s > 0`
(the paper's `z = -s`), so every inverse is of a positive definite matrix. Norms are the
project's named norms `Muon.opNorm`, `Muon.fro`, `Muon.nuc` (no Matrix norm instance is used
in a statement). Vectors are `Vec k = Fin k → ℝ`; the paper's Euclidean norm enters only
through `sqNorm`, the squared Euclidean norm `∑ᵢ xᵢ²`.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace Muon.DetEquiv

/-- Squared Euclidean norm `‖x‖² = ∑ᵢ xᵢ²` of a real vector (the paper's `\mathsf N`
in `eqn:app-de-Lambda-inverse`, `section.tex` l.695–698). Not the sup norm of
`Fin k → ℝ`. -/
def sqNorm {k : ℕ} (x : Vec k) : ℝ := ∑ i, x i ^ 2

/-- Output-side resolvent `R_s(M) = (MMᵀ + s Id)⁻¹` (`eqn:app-de-RXdef`, `section.tex`
l.601–605). The inverse is genuine for `s > 0`. -/
def Rs {m n : ℕ} (M : Mat m n) (s : ℝ) : Mat m m :=
  (M * Mᵀ + s • (1 : Mat m m))⁻¹

/-- Input-side resolvent `R̃_s(M) = (MᵀM + s Id)⁻¹` (`eqn:app-de-RXdef`, `section.tex`
l.601–605). -/
def Rts {m n : ℕ} (M : Mat m n) (s : ℝ) : Mat n n :=
  (Mᵀ * M + s • (1 : Mat n n))⁻¹

/-- Mixed resolvent `𝖷_s(M) = R_s(M) M` (`eqn:app-de-RXdef`, `section.tex` l.601–605). -/
def Xs {m n : ℕ} (M : Mat m n) (s : ℝ) : Mat m n :=
  Rs M s * M

/-- `𝖴 = uᵀ R_s(M₀) u` (`eqn:app-de-UVC`, `section.tex` l.672–677). -/
def delU {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (s : ℝ) : ℝ :=
  dotProduct u (Rs M₀ s *ᵥ u)

/-- `𝖵 = vᵀ R̃_s(M₀) v` (`eqn:app-de-UVC`, `section.tex` l.672–677). -/
def delV {m n : ℕ} (M₀ : Mat m n) (v : Vec n) (s : ℝ) : ℝ :=
  dotProduct v (Rts M₀ s *ᵥ v)

/-- `𝖢 = uᵀ 𝖷_s(M₀) v` (`eqn:app-de-UVC`, `section.tex` l.672–677). -/
def delC {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (v : Vec n) (s : ℝ) : ℝ :=
  dotProduct u (Xs M₀ s *ᵥ v)

/-- `Λ = (1 + 𝗁𝖢)² + s 𝗁² 𝖴𝖵` for `M = M₀ + 𝗁 u ⊗ v` (`eqn:app-de-UVC`, `section.tex`
l.672–677). Applied to `M` with `-𝗁` it gives the quantity `Λ'` of `lem:app-de-deletion`. -/
def delLambda {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ) : ℝ :=
  (1 + h * delC M₀ u v s) ^ 2 + s * h ^ 2 * delU M₀ u s * delV M₀ v s

/-- `α₁ = 𝗁(1 + 𝗁𝖢)/Λ` (`eqn:app-de-coefficients`, `section.tex` l.679–683). -/
def alpha1 {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ) : ℝ :=
  h * (1 + h * delC M₀ u v s) / delLambda M₀ h u v s

/-- `α₂ = 𝗁² 𝖴/Λ` (`eqn:app-de-coefficients`, `section.tex` l.679–683). -/
def alpha2 {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ) : ℝ :=
  h ^ 2 * delU M₀ u s / delLambda M₀ h u v s

/-- `α₃ = -s 𝗁² 𝖵/Λ` (`eqn:app-de-coefficients`, `section.tex` l.679–683). -/
def alpha3 {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (s : ℝ) : ℝ :=
  -(s * h ^ 2 * delV M₀ v s) / delLambda M₀ h u v s

/-- Constant `C_I = max(1, s₋⁻¹)(1 + 3/(4√s₋))³` with `s₋ = min I` (`lem:app-de-coeff`,
`section.tex` l.821–823). For `I` empty `sInf I = 0`, but the statements quantify over `s ∈ I`. -/
def coeffConst (I : Set ℝ) : ℝ :=
  max 1 ((sInf I)⁻¹) * (1 + 3 / (4 * Real.sqrt (sInf I))) ^ 3

/-! ### Private helpers for `lem_app_de_resolvent` (elementary, no SVD) -/

private lemma resAux_isUnit {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat a a)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'

private lemma resAux_isUnit_T {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    IsUnit (Kᵀ * K + s • (1 : Mat b b)).det := by
  have h := resAux_isUnit Kᵀ s hs
  rwa [Matrix.transpose_transpose] at h

private lemma resAux_mulVec_inv {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) (x : Vec a) :
    (K * Kᵀ + s • (1 : Mat a a)) *ᵥ ((K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (resAux_isUnit K s hs), Matrix.one_mulVec]

private lemma resAux_vecMul {a b : ℕ} (K : Mat a b) (y : Vec a) : y ᵥ* K = Kᵀ *ᵥ y := by
  have h := Matrix.vecMul_transpose Kᵀ y
  rwa [Matrix.transpose_transpose] at h

private lemma resAux_dot_mulVec {a b : ℕ} (K : Mat a b) (y : Vec a) (x : Vec b) :
    y ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ y) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, resAux_vecMul]

private lemma resAux_quad {a b : ℕ} (K : Mat a b) (s : ℝ) (y : Vec a) :
    y ⬝ᵥ ((K * Kᵀ + s • (1 : Mat a a)) *ᵥ y) = sqNorm (Kᵀ *ᵥ y) + s * sqNorm y := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, ← Matrix.mulVec_mulVec, resAux_dot_mulVec]
  simp [sqNorm, dotProduct, sq]

private lemma resAux_cs {a : ℕ} (y x : Vec a) : (y ⬝ᵥ x) ^ 2 ≤ sqNorm y * sqNorm x := by
  simpa [dotProduct, sqNorm] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y x

private lemma resAux_sqNorm_nonneg {a : ℕ} (x : Vec a) : 0 ≤ sqNorm x :=
  Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma resAux_real_R (p t q X s : ℝ) (hs : 0 < s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hX : 0 ≤ X) (hp : p = t + s * q) (hcs : p ^ 2 ≤ q * X) : s ^ 2 * q ≤ X := by
  by_contra hcon
  push_neg at hcon
  have hsq : s * q ≤ p := by linarith
  have hq0 : 0 < q := by
    rcases eq_or_lt_of_le hq with h0 | h0
    · rw [← h0, mul_zero] at hcon
      linarith
    · exact h0
  have h1 : (s * q) ^ 2 ≤ p ^ 2 := by nlinarith [mul_nonneg hs.le hq]
  have h2 := mul_lt_mul_of_pos_left hcon hq0
  nlinarith

private lemma resAux_real_X (p t q X s : ℝ) (hs : 0 < s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hX : 0 ≤ X) (hp : p = t + s * q) (hcs : p ^ 2 ≤ t * X) : 4 * s * q ≤ X := by
  have ht' : t = p - s * q := by linarith
  subst ht'
  have key : 0 ≤ X * (X - 4 * s * q) := by nlinarith [sq_nonneg (2 * p - X)]
  rcases eq_or_lt_of_le hX with h0 | h0
  · subst h0
    nlinarith [sq_nonneg p, mul_nonneg hs.le hq]
  · have := (mul_nonneg_iff_of_pos_left h0).mp key
    linarith

/-- Bound on `R = (K Kᵀ + s)⁻¹` in the squared-vector form. -/
private lemma resAux_bound_R {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) (x : Vec a) :
    s ^ 2 * sqNorm ((K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ x) ≤ sqNorm x := by
  have hy : (K * Kᵀ + s • (1 : Mat a a)) *ᵥ ((K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ x) = x :=
    resAux_mulVec_inv K s hs x
  generalize hyd : (K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ x = y at hy ⊢
  have hp : y ⬝ᵥ x = sqNorm (Kᵀ *ᵥ y) + s * sqNorm y := by
    rw [← hy]; exact resAux_quad K s y
  exact resAux_real_R _ _ _ _ s hs (resAux_sqNorm_nonneg _) (resAux_sqNorm_nonneg _)
    (resAux_sqNorm_nonneg _) hp (resAux_cs y x)

/-- Bound on `R M` in the squared-vector form: `4 s ‖R M x‖² ≤ ‖x‖²`. -/
private lemma resAux_bound_X {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) (x : Vec b) :
    4 * s * sqNorm ((K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ (K *ᵥ x)) ≤ sqNorm x := by
  have hy : (K * Kᵀ + s • (1 : Mat a a)) *ᵥ ((K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ (K *ᵥ x))
      = K *ᵥ x := resAux_mulVec_inv K s hs _
  generalize hyd : (K * Kᵀ + s • (1 : Mat a a))⁻¹ *ᵥ (K *ᵥ x) = y at hy ⊢
  have hp : y ⬝ᵥ (K *ᵥ x) = sqNorm (Kᵀ *ᵥ y) + s * sqNorm y := by
    rw [← hy]; exact resAux_quad K s y
  have hcs : (y ⬝ᵥ (K *ᵥ x)) ^ 2 ≤ sqNorm (Kᵀ *ᵥ y) * sqNorm x := by
    rw [resAux_dot_mulVec]; exact resAux_cs _ _
  exact resAux_real_X _ _ _ _ s hs (resAux_sqNorm_nonneg _) (resAux_sqNorm_nonneg _)
    (resAux_sqNorm_nonneg _) hp hcs

open scoped Matrix.Norms.L2Operator in
/-- Operator-norm bound from a squared-vector bound. -/
private lemma resAux_opNorm_le {a b : ℕ} (K : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Vec b, sqNorm (K *ᵥ x) ≤ c ^ 2 * sqNorm x) : opNorm K ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))‖
      ≤ c * ‖x‖
  have hx : sqNorm (EuclideanSpace.equiv (Fin b) ℝ x) = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm, Real.norm_eq_abs, sq_abs]
  have hy : sqNorm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))
      = ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (K *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp [sqNorm, Real.norm_eq_abs, sq_abs]
  have h2 := h (EuclideanSpace.equiv (Fin b) ℝ x)
  rw [hx, hy] at h2
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg hc (norm_nonneg _)) ?_
  rw [mul_pow]
  exact h2

private lemma resAux_opNorm_Rs {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    opNorm (Rs M s) ≤ 1 / s := by
  unfold Rs
  refine resAux_opNorm_le _ (one_div_nonneg.mpr hs.le) fun x => ?_
  have h := resAux_bound_R M s hs x
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (pow_pos hs 2)]
  linarith

private lemma resAux_opNorm_Rts {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    opNorm (Rts M s) ≤ 1 / s := by
  unfold Rts
  refine resAux_opNorm_le _ (one_div_nonneg.mpr hs.le) fun x => ?_
  have h := resAux_bound_R Mᵀ s hs x
  rw [Matrix.transpose_transpose] at h
  rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, le_div_iff₀ (pow_pos hs 2)]
  linarith

private lemma resAux_opNorm_Xs {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    opNorm (Xs M s) ≤ 1 / (2 * Real.sqrt s) := by
  unfold Xs Rs
  refine resAux_opNorm_le _ (div_nonneg zero_le_one (by positivity)) fun x => ?_
  rw [← Matrix.mulVec_mulVec]
  have h := resAux_bound_X M s hs x
  have hc : (1 / (2 * Real.sqrt s)) ^ 2 * sqNorm x = sqNorm x / (4 * s) := by
    rw [div_pow, one_pow, mul_pow, Real.sq_sqrt hs.le]
    ring
  rw [hc, le_div_iff₀ (by linarith)]
  linarith

private lemma resAux_intertw {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    (M * Mᵀ + s • (1 : Mat m m))⁻¹ * M = M * (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by
  have hA : (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s • (1 : Mat m m)) = 1 :=
    Matrix.nonsing_inv_mul _ (resAux_isUnit M s hs)
  have hB : (Mᵀ * M + s • (1 : Mat n n)) * (Mᵀ * M + s • (1 : Mat n n))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (resAux_isUnit_T M s hs)
  have hAM : (M * Mᵀ + s • (1 : Mat m m)) * M = M * (Mᵀ * M + s • (1 : Mat n n)) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  calc (M * Mᵀ + s • (1 : Mat m m))⁻¹ * M
      = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * M * ((Mᵀ * M + s • (1 : Mat n n)) *
          (Mᵀ * M + s • (1 : Mat n n))⁻¹) := by rw [hB, Matrix.mul_one]
    _ = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * (Mᵀ * M + s • (1 : Mat n n))) *
          (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * ((M * Mᵀ + s • (1 : Mat m m)) * M) *
          (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by rw [hAM]
    _ = ((M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s • (1 : Mat m m))) * M *
          (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by simp only [Matrix.mul_assoc]
    _ = M * (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by rw [hA, Matrix.one_mul]

private lemma resAux_id5 {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    Mᵀ * (M * Mᵀ + s • (1 : Mat m m))⁻¹ * M = (1 : Mat n n) - s • (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by
  have hB : (Mᵀ * M + s • (1 : Mat n n)) * (Mᵀ * M + s • (1 : Mat n n))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (resAux_isUnit_T M s hs)
  calc Mᵀ * (M * Mᵀ + s • (1 : Mat m m))⁻¹ * M
      = Mᵀ * ((M * Mᵀ + s • (1 : Mat m m))⁻¹ * M) := Matrix.mul_assoc _ _ _
    _ = Mᵀ * (M * (Mᵀ * M + s • (1 : Mat n n))⁻¹) := by rw [resAux_intertw M s hs]
    _ = (Mᵀ * M) * (Mᵀ * M + s • (1 : Mat n n))⁻¹ := (Matrix.mul_assoc _ _ _).symm
    _ = ((Mᵀ * M + s • (1 : Mat n n)) - s • (1 : Mat n n)) * (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by
        rw [add_sub_cancel_right]
    _ = (1 : Mat n n) - s • (Mᵀ * M + s • (1 : Mat n n))⁻¹ := by
        rw [Matrix.sub_mul, hB, Matrix.smul_mul, Matrix.one_mul]

private lemma resAux_id6 {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ) = (1 : Mat m m) - s • (M * Mᵀ + s • (1 : Mat m m))⁻¹ := by
  have hA : (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s • (1 : Mat m m)) = 1 :=
    Matrix.nonsing_inv_mul _ (resAux_isUnit M s hs)
  calc (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ)
      = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * ((M * Mᵀ + s • (1 : Mat m m)) - s • (1 : Mat m m)) := by
        rw [add_sub_cancel_right]
    _ = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s • (1 : Mat m m))
          - (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (s • (1 : Mat m m)) := Matrix.mul_sub _ _ _
    _ = (1 : Mat m m) - s • (M * Mᵀ + s • (1 : Mat m m))⁻¹ := by
        rw [hA, Matrix.mul_smul, Matrix.mul_one]

open scoped Matrix.Norms.L2Operator in
private lemma resAux_lip {m n : ℕ} (M : Mat m n) (s s' : ℝ) (hs : 0 < s) (hs' : 0 < s') :
    opNorm (Rs M s - Rs M s') ≤ |s - s'| / (s * s') := by
  have hn1 : ‖(M * Mᵀ + s • (1 : Mat m m))⁻¹‖ ≤ 1 / s := by
    have h := resAux_opNorm_Rs M s hs
    rw [opNorm_eq_norm] at h
    exact h
  have hn2 : ‖(M * Mᵀ + s' • (1 : Mat m m))⁻¹‖ ≤ 1 / s' := by
    have h := resAux_opNorm_Rs M s' hs'
    rw [opNorm_eq_norm] at h
    exact h
  have hA : (M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s • (1 : Mat m m)) = 1 :=
    Matrix.nonsing_inv_mul _ (resAux_isUnit M s hs)
  have hA' : (M * Mᵀ + s' • (1 : Mat m m)) * (M * Mᵀ + s' • (1 : Mat m m))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (resAux_isUnit M s' hs')
  have hdiff : (M * Mᵀ + s' • (1 : Mat m m)) - (M * Mᵀ + s • (1 : Mat m m))
      = (s' - s) • (1 : Mat m m) := by
    rw [sub_smul]; abel
  have key : Rs M s - Rs M s' = (s' - s) • ((M * Mᵀ + s • (1 : Mat m m))⁻¹ *
      (M * Mᵀ + s' • (1 : Mat m m))⁻¹) := by
    unfold Rs
    calc (M * Mᵀ + s • (1 : Mat m m))⁻¹ - (M * Mᵀ + s' • (1 : Mat m m))⁻¹
        = (M * Mᵀ + s • (1 : Mat m m))⁻¹ * ((M * Mᵀ + s' • (1 : Mat m m))
            - (M * Mᵀ + s • (1 : Mat m m))) * (M * Mᵀ + s' • (1 : Mat m m))⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc (M * Mᵀ + s • (1 : Mat m m))⁻¹
            (M * Mᵀ + s' • (1 : Mat m m)), hA', Matrix.mul_one, hA, Matrix.one_mul]
      _ = (s' - s) • ((M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s' • (1 : Mat m m))⁻¹) := by
          rw [hdiff, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  rw [key, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]
  have hprod := Matrix.l2_opNorm_mul ((M * Mᵀ + s • (1 : Mat m m))⁻¹)
    ((M * Mᵀ + s' • (1 : Mat m m))⁻¹)
  calc |s' - s| * ‖(M * Mᵀ + s • (1 : Mat m m))⁻¹ * (M * Mᵀ + s' • (1 : Mat m m))⁻¹‖
      ≤ |s' - s| * (‖(M * Mᵀ + s • (1 : Mat m m))⁻¹‖ * ‖(M * Mᵀ + s' • (1 : Mat m m))⁻¹‖) :=
        mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
    _ ≤ |s' - s| * ((1 / s) * (1 / s')) := by gcongr
    _ = |s - s'| / (s * s') := by rw [abs_sub_comm]; field_simp

/-- lem:app-de-resolvent. Snapshot `cr-2026-10-22`. LaTeX (`section.tex` l.607–622):
\begin{lemma}[Resolvent identities]\label{lem:app-de-resolvent}
For every $M$ and $s>0$,
\[
\begin{gathered}
\norm{R_s(M)}\le\frac1s,\qquad
\norm{\widetilde R_s(M)}\le\frac1s,\qquad \norm{\mathsf X_s(M)}\le\frac{1}{2\sqrt s},\\
R_s(M)M=M\widetilde R_s(M),\qquad
M^\T R_s(M)M=\Id_{\Nin}-s\widetilde R_s(M),\\
R_s(M)MM^\T=\Id_{\Nout}-sR_s(M),
\end{gathered}
\]
and for $s,s'>0$,
\[
\norm{R_s(M)-R_{s'}(M)}\le\frac{\abs{s-s'}}{ss'}.
\]
\end{lemma} -/
theorem lem_app_de_resolvent {m n : ℕ} (M : Mat m n) (s : ℝ) (hs : 0 < s) :
    opNorm (Rs M s) ≤ 1 / s ∧
    opNorm (Rts M s) ≤ 1 / s ∧
    opNorm (Xs M s) ≤ 1 / (2 * Real.sqrt s) ∧
    Rs M s * M = M * Rts M s ∧
    Mᵀ * Rs M s * M = (1 : Mat n n) - s • Rts M s ∧
    Rs M s * (M * Mᵀ) = (1 : Mat m m) - s • Rs M s ∧
    ∀ s' : ℝ, 0 < s' → opNorm (Rs M s - Rs M s') ≤ |s - s'| / (s * s') :=
  ⟨resAux_opNorm_Rs M s hs, resAux_opNorm_Rts M s hs, resAux_opNorm_Xs M s hs,
    resAux_intertw M s hs, resAux_id5 M s hs, resAux_id6 M s hs,
    fun s' hs' => resAux_lip M s s' hs hs'⟩

/-! ### Private helpers for `lem_app_de_deletion` (determinant, Woodbury, bounds) -/

/-- Two-column matrix `[a | b]`. -/
private abbrev dlP {m : ℕ} (a b : Vec m) : Matrix (Fin m) (Fin 2) ℝ :=
  Matrix.of fun i (j : Fin 2) => ![a i, b i] j

private lemma dlAux_dlP_mulVec {m : ℕ} (a b : Vec m) (x : Fin 2 → ℝ) :
    dlP a b *ᵥ x = x 0 • a + x 1 • b := by
  ext i
  simp [dlP, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private lemma dlAux_quad {m : ℕ} (a b : Vec m) (θ00 θ01 θ10 θ11 : ℝ) :
    dlP a b * !![θ00, θ01; θ10, θ11] * (dlP a b)ᵀ =
      θ00 • outer a a + θ01 • outer a b + θ10 • outer b a + θ11 • outer b b := by
  ext i j
  simp [dlP, Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.transpose_apply,
    Matrix.vecMulVec_apply] <;> ring

private lemma dlAux_det_add {m : ℕ} (G0 R0 : Mat m m) (hR : G0 * R0 = 1)
    (P : Matrix (Fin m) (Fin 2) ℝ) (Q : Matrix (Fin 2) (Fin 2) ℝ) :
    (G0 + P * Q * Pᵀ).det = G0.det * (1 + Q * (Pᵀ * R0 * P)).det := by
  have hG : G0 + P * Q * Pᵀ = G0 * (1 + R0 * P * Q * Pᵀ) := by
    simp only [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  rw [hG, Matrix.det_mul]
  congr 1
  have h1 : R0 * P * Q * Pᵀ = (R0 * P) * (Q * Pᵀ) := by simp only [Matrix.mul_assoc]
  have h2 : Q * Pᵀ * (R0 * P) = Q * (Pᵀ * R0 * P) := by simp only [Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm, h2]

private lemma dlAux_inv {m : ℕ} (G0 R0 : Mat m m) (hR : G0 * R0 = 1)
    (P : Matrix (Fin m) (Fin 2) ℝ) (Q T : Matrix (Fin 2) (Fin 2) ℝ)
    (hT : (1 + Q * (Pᵀ * R0 * P)) * T = Q) :
    (G0 + P * Q * Pᵀ)⁻¹ = R0 - R0 * P * T * Pᵀ * R0 := by
  refine Matrix.inv_eq_right_inv ?_
  have hT' : T + Q * (Pᵀ * R0 * P) * T = Q := by
    have h := hT
    rw [Matrix.add_mul, Matrix.one_mul] at h
    exact h
  have key : Q - T - Q * (Pᵀ * R0 * P) * T = 0 := by
    calc Q - T - Q * (Pᵀ * R0 * P) * T = (T + Q * (Pᵀ * R0 * P) * T) - T
          - Q * (Pᵀ * R0 * P) * T := by rw [hT']
      _ = 0 := by abel
  have hz : P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0 = 0 := by
    rw [key]; simp
  have hexp : P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0
      = P * Q * Pᵀ * R0 - P * T * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
  have hGX : G0 * (R0 - R0 * P * T * Pᵀ * R0) = 1 - P * T * Pᵀ * R0 := by
    rw [Matrix.mul_sub, show G0 * (R0 * P * T * Pᵀ * R0) = (G0 * R0) * (P * T * Pᵀ * R0) by
      simp only [Matrix.mul_assoc], hR, Matrix.one_mul]
  have hPX : P * Q * Pᵀ * (R0 - R0 * P * T * Pᵀ * R0)
      = P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0 := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
  rw [Matrix.add_mul, hGX, hPX]
  have hfin : (1 - P * T * Pᵀ * R0) + (P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0)
      = 1 + P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0 := by
    rw [hexp]; abel
  rw [hfin, hz, add_zero]

private lemma dlAux_sand {m : ℕ} (R0 : Mat m m) (P : Matrix (Fin m) (Fin 2) ℝ)
    (Θ : Matrix (Fin 2) (Fin 2) ℝ) (hsym : R0ᵀ = R0) :
    R0 * P * Θ * Pᵀ * R0 = (R0 * P) * Θ * (R0 * P)ᵀ := by
  rw [Matrix.transpose_mul, hsym]
  simp only [Matrix.mul_assoc]

private lemma dlAux_RP {m : ℕ} (R0 : Mat m m) (a b : Vec m) :
    R0 * dlP a b = dlP (R0 *ᵥ a) (R0 *ᵥ b) := by
  ext i j
  fin_cases j <;> simp [dlP, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma dlAux_apply {m : ℕ} (R0 : Mat m m) (P : Matrix (Fin m) (Fin 2) ℝ)
    (Θ : Matrix (Fin 2) (Fin 2) ℝ) (c : Fin 2 → ℝ) :
    (R0 - R0 * P * Θ * Pᵀ * R0) *ᵥ (P *ᵥ c)
      = R0 *ᵥ (P *ᵥ (c - Θ *ᵥ (Pᵀ *ᵥ (R0 *ᵥ (P *ᵥ c))))) := by
  rw [Matrix.sub_mulVec]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private lemma dlAux_det_pos {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    0 < (K * Kᵀ + s • (1 : Mat a a)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  rw [add_comm]
  exact (Matrix.PosDef.add_posSemidef h2 h1).det_pos

/-- Rank-two decomposition of the Gram matrix `M Mᵀ + s` for `M = M₀ + h u vᵀ`. -/
private lemma dlAux_G {m n : ℕ} (M₀ : Mat m n) (h s : ℝ) (u : Vec m) (v : Vec n) :
    (M₀ + h • outer u v) * (M₀ + h • outer u v)ᵀ + s • (1 : Mat m m) =
      (M₀ * M₀ᵀ + s • (1 : Mat m m)) +
        dlP u (M₀ *ᵥ v) * !![h ^ 2 * sqNorm v, h; h, 0] * (dlP u (M₀ *ᵥ v))ᵀ := by
  have hA : ∀ i j : Fin m, ∑ x, (M₀ i x + h * (u i * v x)) * (M₀ j x + h * (u j * v x)) =
      ∑ x, M₀ i x * M₀ j x + (h * u j * ∑ x, M₀ i x * v x + h * u i * ∑ x, M₀ j x * v x
        + h ^ 2 * u i * u j * ∑ x, v x ^ 2) := by
    intro i j
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  ext i j
  simp only [dlP, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, Matrix.mulVec, dotProduct, outer, Matrix.vecMulVec_apply,
    Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.add_apply, Matrix.smul_apply]
  rw [hA i j]
  simp only [sqNorm]
  ring

/-- Symmetry of the output resolvent. -/
private lemma dlAux_Rs_symm {m n : ℕ} (M : Mat m n) (s : ℝ) : (Rs M s)ᵀ = Rs M s := by
  unfold Rs
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul, add_comm]

private lemma dlAux_cross {m : ℕ} (R0 : Mat m m) (hsym : R0ᵀ = R0) (a b : Vec m) :
    b ⬝ᵥ (R0 *ᵥ a) = a ⬝ᵥ (R0 *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, resAux_vecMul, hsym, dotProduct_comm]

private lemma dlAux_gen {m : ℕ} (R0 : Mat m m) (A : Matrix (Fin m) (Fin 2) ℝ) (i j : Fin 2) :
    (Aᵀ * R0 * A) i j = (fun k => A k i) ⬝ᵥ (R0 *ᵥ fun k => A k j) := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma dlAux_W {m : ℕ} (R0 : Mat m m) (hsym : R0ᵀ = R0) (a b : Vec m) :
    (dlP a b)ᵀ * R0 * dlP a b =
      !![a ⬝ᵥ (R0 *ᵥ a), a ⬝ᵥ (R0 *ᵥ b); a ⬝ᵥ (R0 *ᵥ b), b ⬝ᵥ (R0 *ᵥ b)] := by
  have hc := dlAux_cross R0 hsym a b
  have ca : (fun k => dlP a b k 0) = a := by funext k; simp [dlP]
  have cb : (fun k => dlP a b k 1) = b := by funext k; simp [dlP]
  ext i j
  rw [dlAux_gen]
  fin_cases i <;> fin_cases j <;> simp [ca, cb, hc]

private lemma dlAux_W11 {m n : ℕ} (M₀ : Mat m n) (s : ℝ) (hs : 0 < s) (v : Vec n) :
    (M₀ *ᵥ v) ⬝ᵥ (Rs M₀ s *ᵥ (M₀ *ᵥ v)) = sqNorm v - s * delV M₀ v s := by
  have hid : M₀ᵀ * Rs M₀ s * M₀ = 1 - s • Rts M₀ s := resAux_id5 M₀ s hs
  have hvv : v ⬝ᵥ v = sqNorm v := by simp [sqNorm, dotProduct, sq]
  rw [dotProduct_comm, resAux_dot_mulVec,
    show M₀ᵀ *ᵥ (Rs M₀ s *ᵥ (M₀ *ᵥ v)) = (M₀ᵀ * Rs M₀ s * M₀) *ᵥ v by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc], hid, Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.smul_mulVec, sub_dotProduct, smul_dotProduct, hvv]
  rw [dotProduct_comm (Rts M₀ s *ᵥ v) v]
  rfl

private lemma dlAux_scal (h s U C V N L α1 α2 α3 : ℝ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + s * h ^ 2 * U * V)
    (hα1 : α1 = h * (1 + h * C) / L) (hα2 : α2 = h ^ 2 * U / L)
    (hα3 : α3 = -(s * h ^ 2 * V) / L) :
    (1 + !![h ^ 2 * N, h; h, 0] * !![U, C; C, N - s * V]) *
      !![-α3, α1; α1, -α2] = !![h ^ 2 * N, h; h, 0] := by
  subst hα1 hα2 hα3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;>
    (subst hLdef; ring)

private lemma dlAux_vec (h s U C V N L α1 α2 α3 : ℝ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + s * h ^ 2 * U * V)
    (hα1 : α1 = h * (1 + h * C) / L) (hα2 : α2 = h ^ 2 * U / L)
    (hα3 : α3 = -(s * h ^ 2 * V) / L) :
    h • (![h * N, 1] - !![-α3, α1; α1, -α2] *ᵥ (!![U, C; C, N - s * V] *ᵥ ![h * N, 1])) =
      ![-α3, α1] := by
  subst hα1 hα2 hα3
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> field_simp <;>
    (subst hLdef; ring)

private lemma dlAux_det_rel {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (s : ℝ) (hM : M = M₀ + h • outer u v) (hs : 0 < s) :
    (M * Mᵀ + s • (1 : Mat m m)).det =
      (M₀ * M₀ᵀ + s • (1 : Mat m m)).det * delLambda M₀ h u v s := by
  subst hM
  have hG0 : (M₀ * M₀ᵀ + s • (1 : Mat m m)) * Rs M₀ s = 1 :=
    Matrix.mul_nonsing_inv _ (resAux_isUnit M₀ s hs)
  have hsym := dlAux_Rs_symm M₀ s
  have hU : u ⬝ᵥ (Rs M₀ s *ᵥ u) = delU M₀ u s := rfl
  have hC : u ⬝ᵥ (Rs M₀ s *ᵥ (M₀ *ᵥ v)) = delC M₀ u v s := by
    unfold delC Xs; rw [Matrix.mulVec_mulVec]
  rw [dlAux_G M₀ h s u v, dlAux_det_add _ _ hG0, dlAux_W _ hsym, hU, hC, dlAux_W11 M₀ s hs v]
  congr 1
  rw [Matrix.det_fin_two]
  simp [delLambda, Matrix.mul_apply, Fin.sum_univ_two]
  ring

private lemma dlAux_Lam_pos {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (s : ℝ) (hM : M = M₀ + h • outer u v) (hs : 0 < s) :
    0 < delLambda M₀ h u v s := by
  have h1 := dlAux_det_rel M₀ h u v M s hM hs
  have h2 := dlAux_det_pos M s hs
  have h3 := dlAux_det_pos M₀ s hs
  have h4 : 0 < (M₀ * M₀ᵀ + s • (1 : Mat m m)).det * delLambda M₀ h u v s := by
    rw [← h1]; exact h2
  exact pos_of_mul_pos_right h4 h3.le

/-- Bounds on `𝖴 = uᵀ R_s(M) u`. -/
private lemma dlAux_U {m n : ℕ} (M : Mat m n) (u : Vec m) (s : ℝ) (hs : 0 < s) :
    0 ≤ delU M u s ∧ s * delU M u s ≤ sqNorm u := by
  have hy : (M * Mᵀ + s • (1 : Mat m m)) *ᵥ (Rs M s *ᵥ u) = u :=
    resAux_mulVec_inv M s hs u
  have hquad : (Rs M s *ᵥ u) ⬝ᵥ u = sqNorm (Mᵀ *ᵥ (Rs M s *ᵥ u)) + s * sqNorm (Rs M s *ᵥ u) := by
    have := resAux_quad M s (Rs M s *ᵥ u)
    rwa [hy] at this
  have hU : delU M u s = (Rs M s *ᵥ u) ⬝ᵥ u := by
    unfold delU; rw [dotProduct_comm]
  have hcs : ((Rs M s *ᵥ u) ⬝ᵥ u) ^ 2 ≤ sqNorm u * sqNorm (Rs M s *ᵥ u) := by
    rw [dotProduct_comm]; exact resAux_cs u (Rs M s *ᵥ u)
  have hb : s ^ 2 * sqNorm (Rs M s *ᵥ u) ≤ sqNorm u := resAux_bound_R M s hs u
  have hnn1 := resAux_sqNorm_nonneg (Mᵀ *ᵥ (Rs M s *ᵥ u))
  have hnn2 := resAux_sqNorm_nonneg (Rs M s *ᵥ u)
  have hnnu := resAux_sqNorm_nonneg u
  rw [hU]
  have hU0 : 0 ≤ (Rs M s *ᵥ u) ⬝ᵥ u := by
    rw [hquad]; exact add_nonneg hnn1 (mul_nonneg hs.le hnn2)
  refine ⟨hU0, ?_⟩
  have h1 : (s * ((Rs M s *ᵥ u) ⬝ᵥ u)) ^ 2 ≤ s ^ 2 * (sqNorm u * sqNorm (Rs M s *ᵥ u)) := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hcs (sq_nonneg s)
  have h2 : sqNorm u * (s ^ 2 * sqNorm (Rs M s *ᵥ u)) ≤ sqNorm u * sqNorm u :=
    mul_le_mul_of_nonneg_left hb hnnu
  have key : (s * ((Rs M s *ᵥ u) ⬝ᵥ u)) ^ 2 ≤ sqNorm u ^ 2 := by nlinarith
  nlinarith [key, hnnu, hU0, mul_nonneg hs.le hU0]

/-- Bounds on `𝖵 = vᵀ R̃_s(M) v`. -/
private lemma dlAux_V {m n : ℕ} (M : Mat m n) (v : Vec n) (s : ℝ) (hs : 0 < s) :
    0 ≤ delV M v s ∧ s * delV M v s ≤ sqNorm v := by
  have hVU : delV M v s = delU Mᵀ v s := by
    unfold delV delU Rts Rs; rw [Matrix.transpose_transpose]
  rw [hVU]
  exact dlAux_U Mᵀ v s hs

/-- Bound on the cross term `𝖢 = uᵀ 𝖷_s(M) v`. -/
private lemma dlAux_C {m n : ℕ} (M : Mat m n) (u : Vec m) (v : Vec n) (s : ℝ) (hs : 0 < s) :
    4 * s * delC M u v s ^ 2 ≤ sqNorm u * sqNorm v := by
  have hX : Xs M s *ᵥ v = Rs M s *ᵥ (M *ᵥ v) := by
    unfold Xs; rw [Matrix.mulVec_mulVec]
  have hC : delC M u v s = u ⬝ᵥ (Rs M s *ᵥ (M *ᵥ v)) := by
    unfold delC; rw [hX]
  have hcs : (u ⬝ᵥ (Rs M s *ᵥ (M *ᵥ v))) ^ 2 ≤ sqNorm u * sqNorm (Rs M s *ᵥ (M *ᵥ v)) :=
    resAux_cs u (Rs M s *ᵥ (M *ᵥ v))
  have hb : 4 * s * sqNorm (Rs M s *ᵥ (M *ᵥ v)) ≤ sqNorm v := resAux_bound_X M s hs v
  have hnnu := resAux_sqNorm_nonneg u
  rw [hC]
  have h1 := mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ 4 * s)
  have h2 := mul_le_mul_of_nonneg_left hb hnnu
  nlinarith

/-- Pure real bound behind `Λ' ≤ (1 + 3/(4√s) |h| N)²`. -/
private lemma dlAux_bound (h s Nu Nv U V C : ℝ) (hs : 0 < s) (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv)
    (hU0 : 0 ≤ U) (hU : s * U ≤ Nu) (hV0 : 0 ≤ V) (hV : s * V ≤ Nv)
    (hC : 4 * s * C ^ 2 ≤ Nu * Nv) :
    (1 + -h * C) ^ 2 + s * (-h) ^ 2 * U * V
      ≤ (1 + 3 / (4 * Real.sqrt s) * |h| * (Nu + Nv)) ^ 2 := by
  have hσ : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hσpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  set σ := Real.sqrt s with hσdef
  set t := |h| * (Nu + Nv) / (4 * σ) with htdef
  have ht0 : 0 ≤ t := by positivity
  have e3 : 3 / (4 * σ) * |h| * (Nu + Nv) = 3 * t := by rw [htdef]; ring
  rw [e3]
  have htσ : t * (4 * σ) = |h| * (Nu + Nv) := div_mul_cancel₀ _ (by positivity)
  have hsq : (4 * σ * |h * C|) ^ 2 ≤ (|h| * (Nu + Nv)) ^ 2 := by
    have habs : |h * C| ^ 2 = (h * C) ^ 2 := sq_abs _
    have habs2 : |h| ^ 2 = h ^ 2 := sq_abs _
    have e1 : (4 * σ * |h * C|) ^ 2 = 16 * s * (h * C) ^ 2 := by
      calc (4 * σ * |h * C|) ^ 2 = 16 * σ ^ 2 * |h * C| ^ 2 := by ring
        _ = 16 * s * (h * C) ^ 2 := by rw [hσ, habs]
    have e2 : (|h| * (Nu + Nv)) ^ 2 = h ^ 2 * (Nu + Nv) ^ 2 := by rw [mul_pow, habs2]
    rw [e1, e2]
    have h3 := mul_le_mul_of_nonneg_left hC (sq_nonneg h)
    nlinarith [sq_nonneg (Nu - Nv), sq_nonneg h]
  have hA0 : 0 ≤ 4 * σ * |h * C| := by positivity
  have hB0 : 0 ≤ |h| * (Nu + Nv) := by positivity
  have hle : 4 * σ * |h * C| ≤ |h| * (Nu + Nv) := by nlinarith [hsq, hA0, hB0]
  have hCt : |h * C| ≤ t := by nlinarith [htσ, hle]
  have hbnd := abs_le.mp hCt
  have hpart1 : (1 + -h * C) ^ 2 ≤ (1 + t) ^ 2 := by
    have hh : -h * C = -(h * C) := by ring
    rw [hh]
    nlinarith [hbnd.1, hbnd.2]
  have ht2 : t ^ 2 * (16 * s) = h ^ 2 * (Nu + Nv) ^ 2 := by
    calc t ^ 2 * (16 * s) = (t * (4 * σ)) ^ 2 := by rw [← hσ]; ring
      _ = (|h| * (Nu + Nv)) ^ 2 := by rw [htσ]
      _ = h ^ 2 * (Nu + Nv) ^ 2 := by rw [mul_pow, sq_abs]
  have hUV : (s * U) * (s * V) ≤ Nu * Nv := mul_le_mul hU hV (mul_nonneg hs.le hV0) hNu
  have hpart2 : s * (-h) ^ 2 * U * V ≤ 4 * t ^ 2 := by
    have hk : (s * (-h) ^ 2 * U * V) * (4 * s) ≤ (4 * t ^ 2) * (4 * s) := by
      have e4 : (4 * t ^ 2) * (4 * s) = h ^ 2 * (Nu + Nv) ^ 2 := by nlinarith [ht2]
      rw [e4]
      have e5 : (s * (-h) ^ 2 * U * V) * (4 * s) = 4 * h ^ 2 * ((s * U) * (s * V)) := by
        rw [neg_sq]; ring
      rw [e5]
      have h5 := mul_le_mul_of_nonneg_left hUV (by positivity : (0:ℝ) ≤ 4 * h ^ 2)
      nlinarith [sq_nonneg (Nu - Nv), sq_nonneg h]
    exact le_of_mul_le_mul_right hk (by positivity)
  nlinarith [hpart1, hpart2, ht0]


/-- lem:app-de-deletion. Snapshot `cr-2026-10-22`. LaTeX (`section.tex` l.667–699):
\begin{lemma}[Rank-two deletion]\label{lem:app-de-deletion}
Let $M=M_0+\mathsf h\,\mathsf u\tensor\mathsf v$ with $M_0\in\R^{\Nout\times\Nin}$,
$\mathsf h\in\R$, $\mathsf u\in\R^{\Nout}$, $\mathsf v\in\R^{\Nin}$, and $s>0$.
Write $R_0=R_s(M_0)$, $\widetilde R_0=\widetilde R_s(M_0)$,
$\mathsf X_0=\mathsf X_s(M_0)$, $R=R_s(M)$, and
\begin{equation}\label{eqn:app-de-UVC}
\mathsf U\defeq\mathsf u^\T R_0\mathsf u,\qquad
\mathsf V\defeq\mathsf v^\T\widetilde R_0\mathsf v,\qquad
\mathsf C\defeq\mathsf u^\T\mathsf X_0\mathsf v,\qquad
\Lambda\defeq(1+\mathsf h\mathsf C)^2+s\mathsf h^2\,\mathsf U\mathsf V .
\end{equation}
Then $\Lambda>0$, and with
\begin{equation}\label{eqn:app-de-coefficients}
\alpha_1\defeq\frac{\mathsf h(1+\mathsf h\mathsf C)}{\Lambda},\qquad
\alpha_2\defeq\frac{\mathsf h^2\,\mathsf U}{\Lambda},\qquad
\alpha_3\defeq-\frac{s\mathsf h^2\,\mathsf V}{\Lambda},
\end{equation}
one has
\begin{align}
R-R_0&=\alpha_3\,(R_0\mathsf u)\tensor(R_0\mathsf u)-\alpha_1\,(R_0\mathsf u)\tensor(\mathsf X_0\mathsf v)
-\alpha_1\,(\mathsf X_0\mathsf v)\tensor(R_0\mathsf u)+\alpha_2\,(\mathsf X_0\mathsf v)\tensor(\mathsf X_0\mathsf v) ,
\label{eqn:app-de-deletion-R}\\
\mathsf h\,RM\mathsf v&=-\alpha_3\,R_0\mathsf u+\alpha_1\,\mathsf X_0\mathsf v .
\label{eqn:app-de-deletion-RMv}
\end{align}
Moreover, if $\Lambda'$ denotes the quantity \cref{eqn:app-de-UVC} computed
from $M$ in place of $M_0$ and $-\mathsf h$ in place of $\mathsf h$, then
$\Lambda\Lambda'=1$, and consequently
\begin{equation}\label{eqn:app-de-Lambda-inverse}
\Lambda^{-1}\le\Big(1+\frac{3}{4\sqrt s}\,\abs{\mathsf h}\,\mathsf N\Big)^2,\qquad
\mathsf N\defeq\norm{\mathsf u}^2+\norm{\mathsf v}^2 .
\end{equation}
\end{lemma} -/
theorem lem_app_de_deletion {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (s : ℝ) (hM : M = M₀ + h • outer u v) (hs : 0 < s) :
    0 < delLambda M₀ h u v s ∧
    Rs M s - Rs M₀ s =
      (alpha3 M₀ h u v s) • outer (Rs M₀ s *ᵥ u) (Rs M₀ s *ᵥ u)
        - (alpha1 M₀ h u v s) • outer (Rs M₀ s *ᵥ u) (Xs M₀ s *ᵥ v)
        - (alpha1 M₀ h u v s) • outer (Xs M₀ s *ᵥ v) (Rs M₀ s *ᵥ u)
        + (alpha2 M₀ h u v s) • outer (Xs M₀ s *ᵥ v) (Xs M₀ s *ᵥ v) ∧
    h • (Rs M s *ᵥ (M *ᵥ v)) =
      (-alpha3 M₀ h u v s) • (Rs M₀ s *ᵥ u) + (alpha1 M₀ h u v s) • (Xs M₀ s *ᵥ v) ∧
    delLambda M₀ h u v s * delLambda M (-h) u v s = 1 ∧
    (delLambda M₀ h u v s)⁻¹ ≤ (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm u + sqNorm v)) ^ 2 := by
  have hsym := dlAux_Rs_symm M₀ s
  have hG0 : (M₀ * M₀ᵀ + s • (1 : Mat m m)) * Rs M₀ s = 1 :=
    Matrix.mul_nonsing_inv _ (resAux_isUnit M₀ s hs)
  have hdet0 : 0 < (M₀ * M₀ᵀ + s • (1 : Mat m m)).det := dlAux_det_pos M₀ s hs
  have hL : 0 < delLambda M₀ h u v s := dlAux_Lam_pos M₀ h u v M s hM hs
  have hLne : delLambda M₀ h u v s ≠ 0 := hL.ne'
  have hrel1 := dlAux_det_rel M₀ h u v M s hM hs
  have hM' : M₀ = M + (-h) • outer u v := by rw [hM]; module
  have hrel2 := dlAux_det_rel M (-h) u v M₀ s hM' hs
  have hGM : M * Mᵀ + s • (1 : Mat m m) =
      (M₀ * M₀ᵀ + s • (1 : Mat m m)) +
        dlP u (M₀ *ᵥ v) * !![h ^ 2 * sqNorm v, h; h, 0] * (dlP u (M₀ *ᵥ v))ᵀ := by
    rw [hM]; exact dlAux_G M₀ h s u v
  have hU : u ⬝ᵥ (Rs M₀ s *ᵥ u) = delU M₀ u s := rfl
  have hC : u ⬝ᵥ (Rs M₀ s *ᵥ (M₀ *ᵥ v)) = delC M₀ u v s := by
    unfold delC Xs; rw [Matrix.mulVec_mulVec]
  have hXv : Xs M₀ s *ᵥ v = Rs M₀ s *ᵥ (M₀ *ᵥ v) := by
    unfold Xs; rw [Matrix.mulVec_mulVec]
  have hT : (1 + !![h ^ 2 * sqNorm v, h; h, 0] *
      ((dlP u (M₀ *ᵥ v))ᵀ * Rs M₀ s * dlP u (M₀ *ᵥ v))) *
      !![-alpha3 M₀ h u v s, alpha1 M₀ h u v s; alpha1 M₀ h u v s, -alpha2 M₀ h u v s] =
      !![h ^ 2 * sqNorm v, h; h, 0] := by
    rw [dlAux_W _ hsym, hU, hC, dlAux_W11 M₀ s hs v]
    exact dlAux_scal h s (delU M₀ u s) (delC M₀ u v s) (delV M₀ v s) (sqNorm v)
      (delLambda M₀ h u v s) (alpha1 M₀ h u v s) (alpha2 M₀ h u v s) (alpha3 M₀ h u v s)
      hLne rfl rfl rfl rfl
  have hdecomp : Rs M s = Rs M₀ s - Rs M₀ s * dlP u (M₀ *ᵥ v) *
      !![-alpha3 M₀ h u v s, alpha1 M₀ h u v s; alpha1 M₀ h u v s, -alpha2 M₀ h u v s] *
      (dlP u (M₀ *ᵥ v))ᵀ * Rs M₀ s := by
    show (M * Mᵀ + s • (1 : Mat m m))⁻¹ = _
    rw [hGM]
    exact dlAux_inv _ _ hG0 _ _ _ hT
  have hdec2 : Rs M s = Rs M₀ s - (Rs M₀ s * dlP u (M₀ *ᵥ v)) *
      !![-alpha3 M₀ h u v s, alpha1 M₀ h u v s; alpha1 M₀ h u v s, -alpha2 M₀ h u v s] *
      (Rs M₀ s * dlP u (M₀ *ᵥ v))ᵀ := by
    rw [hdecomp, dlAux_sand _ _ _ hsym]
  have conj2 : Rs M s - Rs M₀ s =
      (alpha3 M₀ h u v s) • outer (Rs M₀ s *ᵥ u) (Rs M₀ s *ᵥ u)
        - (alpha1 M₀ h u v s) • outer (Rs M₀ s *ᵥ u) (Xs M₀ s *ᵥ v)
        - (alpha1 M₀ h u v s) • outer (Xs M₀ s *ᵥ v) (Rs M₀ s *ᵥ u)
        + (alpha2 M₀ h u v s) • outer (Xs M₀ s *ᵥ v) (Xs M₀ s *ᵥ v) := by
    rw [hdec2, dlAux_RP, dlAux_quad, hXv]
    module
  have hB : ∀ i, ∑ x, (M₀ i x + h * (u i * v x)) * v x =
      ∑ x, M₀ i x * v x + h * u i * sqNorm v := by
    intro i
    simp only [sqNorm, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hMv : M *ᵥ v = dlP u (M₀ *ᵥ v) *ᵥ ![h * sqNorm v, 1] := by
    rw [dlAux_dlP_mulVec]
    ext i
    simp only [hM, Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, outer,
      Matrix.vecMulVec_apply, smul_eq_mul, Pi.add_apply, Pi.smul_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
    rw [hB i]
    ring
  have hv := dlAux_vec h s (delU M₀ u s) (delC M₀ u v s) (delV M₀ v s) (sqNorm v)
    (delLambda M₀ h u v s) (alpha1 M₀ h u v s) (alpha2 M₀ h u v s) (alpha3 M₀ h u v s)
    hLne rfl rfl rfl rfl
  have conj3 : h • (Rs M s *ᵥ (M *ᵥ v)) =
      (-alpha3 M₀ h u v s) • (Rs M₀ s *ᵥ u) + (alpha1 M₀ h u v s) • (Xs M₀ s *ᵥ v) := by
    have hWc : (dlP u (M₀ *ᵥ v))ᵀ *ᵥ (Rs M₀ s *ᵥ (dlP u (M₀ *ᵥ v) *ᵥ ![h * sqNorm v, 1]))
        = ((dlP u (M₀ *ᵥ v))ᵀ * Rs M₀ s * dlP u (M₀ *ᵥ v)) *ᵥ ![h * sqNorm v, 1] := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hdecomp, hMv, dlAux_apply, hWc, dlAux_W _ hsym, hU, hC, dlAux_W11 M₀ s hs v]
    rw [← Matrix.mulVec_smul (Rs M₀ s) h, ← Matrix.mulVec_smul (dlP u (M₀ *ᵥ v)) h, hv,
      dlAux_dlP_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.mulVec_add,
      Matrix.mulVec_smul, hXv]
  have hprod : delLambda M₀ h u v s * delLambda M (-h) u v s = 1 := by
    apply mul_left_cancel₀ hdet0.ne'
    rw [mul_one]
    calc (M₀ * M₀ᵀ + s • (1 : Mat m m)).det * (delLambda M₀ h u v s * delLambda M (-h) u v s)
        = ((M₀ * M₀ᵀ + s • (1 : Mat m m)).det * delLambda M₀ h u v s) *
            delLambda M (-h) u v s := by ring
      _ = (M * Mᵀ + s • (1 : Mat m m)).det * delLambda M (-h) u v s := by rw [← hrel1]
      _ = (M₀ * M₀ᵀ + s • (1 : Mat m m)).det := hrel2.symm
  have conj4 : (delLambda M₀ h u v s)⁻¹ ≤
      (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm u + sqNorm v)) ^ 2 := by
    rw [inv_eq_of_mul_eq_one_right hprod]
    obtain ⟨hU0, hU⟩ := dlAux_U M u s hs
    obtain ⟨hV0, hV⟩ := dlAux_V M v s hs
    exact dlAux_bound h s (sqNorm u) (sqNorm v) (delU M u s) (delV M v s) (delC M u v s) hs
      (resAux_sqNorm_nonneg u) (resAux_sqNorm_nonneg v) hU0 hU hV0 hV (dlAux_C M u v s hs)
  exact ⟨hL, conj2, conj3, hprod, conj4⟩

/-! ### Private helpers for `lem_app_de_coeff` -/

private lemma coeffAux_elem (c x y : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 + c * (x * y) ≤ (1 + c) * (1 + x) * (1 + y) := by
  nlinarith [mul_nonneg hc hx, mul_nonneg hc hy, mul_nonneg hx hy,
    mul_nonneg (mul_nonneg hc hx) hy]

private lemma coeffAux_C (C s Nu Nv : ℝ) (hs : 0 < s) (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv)
    (h : 4 * s * C ^ 2 ≤ Nu * Nv) : |C| ≤ 1 / (4 * Real.sqrt s) * (Nu + Nv) := by
  have hσ : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hσp : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hne : 4 * Real.sqrt s ≠ 0 := mul_ne_zero (by norm_num) hσp.ne'
  have key : (|C| * (4 * Real.sqrt s)) ^ 2 ≤ (Nu + Nv) ^ 2 := by
    have e : (|C| * (4 * Real.sqrt s)) ^ 2 = 16 * s * C ^ 2 := by
      calc (|C| * (4 * Real.sqrt s)) ^ 2 = |C| ^ 2 * (16 * Real.sqrt s ^ 2) := by ring
        _ = 16 * s * C ^ 2 := by rw [sq_abs, hσ]; ring
    rw [e]
    nlinarith [sq_nonneg (Nu - Nv)]
  have hle : |C| * (4 * Real.sqrt s) ≤ Nu + Nv :=
    le_of_pow_le_pow_left₀ two_ne_zero (add_nonneg hNu hNv) key
  calc |C| = |C| * (4 * Real.sqrt s) * (1 / (4 * Real.sqrt s)) := by
        rw [mul_assoc, mul_one_div_cancel hne, mul_one]
    _ ≤ (Nu + Nv) * (1 / (4 * Real.sqrt s)) :=
        mul_le_mul_of_nonneg_right hle (by positivity)
    _ = 1 / (4 * Real.sqrt s) * (Nu + Nv) := by ring

private lemma coeffAux_joint (s U V Nu Nv : ℝ) (hs : 0 < s) (hU0 : 0 ≤ U) (hU : s * U ≤ Nu)
    (hV : s * V ≤ Nv) (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv) :
    U + s * V ≤ max 1 s⁻¹ * (Nu + Nv) := by
  have h1 : U ≤ s⁻¹ * Nu := by
    have e : U = s⁻¹ * (s * U) := by rw [← mul_assoc, inv_mul_cancel₀ hs.ne', one_mul]
    calc U = s⁻¹ * (s * U) := e
      _ ≤ s⁻¹ * Nu := mul_le_mul_of_nonneg_left hU (inv_nonneg.mpr hs.le)
  have h2 : s⁻¹ * Nu ≤ max 1 s⁻¹ * Nu := mul_le_mul_of_nonneg_right (le_max_right _ _) hNu
  have h3 : Nv ≤ max 1 s⁻¹ * Nv := by
    have := mul_le_mul_of_nonneg_right (le_max_left 1 s⁻¹) hNv
    linarith
  rw [mul_add]
  linarith

private lemma coeffAux_a1 (h C L N k R : ℝ) (hL : 0 < L) (hN : 0 ≤ N) (hk : 0 ≤ k)
    (hC : |C| ≤ k * N) (hinv : L⁻¹ ≤ (1 + 3 * k * (|h| * N)) ^ 2)
    (hR1 : 1 + k * (|h| * N) ≤ R) (hR2 : 1 + 3 * k * (|h| * N) ≤ R) :
    |h * (1 + h * C) / L| ≤ |h| * R ^ 3 := by
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  have hh : 0 ≤ |h| := abs_nonneg h
  have hkN : 0 ≤ 3 * k * (|h| * N) := mul_nonneg (mul_nonneg (by norm_num) hk) (mul_nonneg hh hN)
  have hR0 : 0 ≤ 1 + 3 * k * (|h| * N) := by linarith
  have hRR : 0 ≤ R := by linarith
  have hinv2 : L⁻¹ ≤ R ^ 2 := le_trans hinv (pow_le_pow_left₀ hR0 hR2 2)
  have e : |h * (1 + h * C) / L| = |h| * |1 + h * C| * L⁻¹ := by
    rw [abs_div, abs_mul, abs_of_pos hL, div_eq_mul_inv]
  have h1 : |1 + h * C| ≤ 1 + k * (|h| * N) := by
    calc |1 + h * C| ≤ |(1 : ℝ)| + |h * C| := abs_add_le _ _
      _ = 1 + |h| * |C| := by rw [abs_one, abs_mul]
      _ ≤ 1 + |h| * (k * N) := by gcongr
      _ = 1 + k * (|h| * N) := by ring
  rw [e]
  calc |h| * |1 + h * C| * L⁻¹ ≤ |h| * R * R ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans hR1) hh) hinv2 hLi.le (mul_nonneg hh hRR)
    _ = |h| * R ^ 3 := by ring

private lemma coeffAux_a2 (h s U V L Nu Nv M k R : ℝ) (hs : 0 < s) (hL : 0 < L)
    (hU0 : 0 ≤ U) (hV0 : 0 ≤ V) (hNu : 0 ≤ Nu) (hNv : 0 ≤ Nv) (hk : 0 ≤ k) (hM : 0 ≤ M)
    (hJ : U + s * V ≤ M * (Nu + Nv))
    (hinv : L⁻¹ ≤ (1 + 3 * k * (|h| * (Nu + Nv))) ^ 2)
    (hR2 : 1 + 3 * k * (|h| * (Nu + Nv)) ≤ R) :
    |h ^ 2 * U / L| + |-(s * h ^ 2 * V) / L| ≤ h ^ 2 * M * (Nu + Nv) * R ^ 2 := by
  have hN : 0 ≤ Nu + Nv := add_nonneg hNu hNv
  have hLi : 0 ≤ L⁻¹ := inv_nonneg.mpr hL.le
  have h1 : 0 ≤ h ^ 2 * U := mul_nonneg (sq_nonneg h) hU0
  have h2 : 0 ≤ s * h ^ 2 * V := mul_nonneg (mul_nonneg hs.le (sq_nonneg h)) hV0
  have e : |h ^ 2 * U / L| + |-(s * h ^ 2 * V) / L| = h ^ 2 * (U + s * V) * L⁻¹ := by
    rw [abs_div, abs_div, abs_neg, abs_of_pos hL, abs_of_nonneg h1, abs_of_nonneg h2]
    ring
  rw [e]
  have hsq : h ^ 2 * (U + s * V) ≤ h ^ 2 * (M * (Nu + Nv)) :=
    mul_le_mul_of_nonneg_left hJ (sq_nonneg h)
  have hnn3 : 0 ≤ 3 * k * (|h| * (Nu + Nv)) :=
    mul_nonneg (mul_nonneg (by norm_num) hk) (mul_nonneg (abs_nonneg h) hN)
  have hR0 : 0 ≤ 1 + 3 * k * (|h| * (Nu + Nv)) := by linarith
  have hLR : L⁻¹ ≤ R ^ 2 := le_trans hinv (pow_le_pow_left₀ hR0 hR2 2)
  calc h ^ 2 * (U + s * V) * L⁻¹ ≤ h ^ 2 * (M * (Nu + Nv)) * R ^ 2 :=
        mul_le_mul hsq hLR hLi (mul_nonneg (sq_nonneg h) (mul_nonneg hM hN))
    _ = h ^ 2 * M * (Nu + Nv) * R ^ 2 := by ring

private lemma coeffAux_rank {m : ℕ} (a b : Vec m) (α1 α2 α3 : ℝ) :
    Matrix.rank (α3 • outer a a - α1 • outer a b - α1 • outer b a + α2 • outer b b) ≤ 2 := by
  set P : Mat m 2 := Matrix.of fun i j => ![a i, b i] j with hP
  set K : Mat 2 2 := !![α3, -α1; -α1, α2] with hK
  have e : α3 • outer a a - α1 • outer a b - α1 • outer b a + α2 • outer b b = P * K * Pᵀ := by
    ext i j
    simp [P, K, Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.vecMulVec_apply]
    ring
  rw [e]
  have h1 : Matrix.rank (P * K * Pᵀ) ≤ Matrix.rank P :=
    le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_left _ _)
  have h2 : Matrix.rank P ≤ 2 := Matrix.rank_le_width P
  exact h1.trans h2

open scoped Matrix.Norms.L2Operator in
private lemma coeffAux_opNorm_sub {m n : ℕ} (A B : Mat m n) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_sub_le _ _

/-- lem:app-de-coeff. Snapshot `cr-2026-10-22`. LaTeX (`section.tex` l.821–833):
\begin{lemma}[Coefficient bounds]\label{lem:app-de-coeff}
Let $I\subset(0,\infty)$ be compact with $s_-=\min I$ and put
$C_I\defeq\max(1,s_-^{-1})\big(1+\tfrac{3}{4\sqrt{s_-}}\big)^3$. In the setting of
\cref{lem:app-de-deletion} with $\mathsf h=\varpi\,d$, $0\le\varpi\le1$, $d\in\R$, and
$s\in I$,
\begin{equation}\label{eqn:app-de-coeff-bounds}
\abs{\alpha_1}\le C_I\,\varpi\,(1+\abs d)^4(1+\mathsf N)^3,\qquad
\abs{\alpha_2}+\abs{\alpha_3}\le C_I\,\varpi^2(1+\abs d)^4(1+\mathsf N)^3 ,
\end{equation}
and the same bounds hold for $\alpha_1/\varpi$ and $(\alpha_2,\alpha_3)/\varpi^2$ with
the factors $\varpi$, $\varpi^2$ removed. Moreover $R-R_0$ has rank at most two and
$\norm{R-R_0}_*\le4/s$.
\end{lemma} -/
theorem lem_app_de_coeff {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (v : Vec n) (M : Mat m n) (d ϖ : ℝ)
    (hM : M = M₀ + (ϖ * d) • outer u v) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) :
    ∀ s ∈ I,
      |alpha1 M₀ (ϖ * d) u v s| ≤
          coeffConst I * ϖ * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 ∧
      |alpha2 M₀ (ϖ * d) u v s| + |alpha3 M₀ (ϖ * d) u v s| ≤
          coeffConst I * ϖ ^ 2 * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 ∧
      (0 < ϖ → |alpha1 M₀ (ϖ * d) u v s / ϖ| ≤
          coeffConst I * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
      (0 < ϖ → (|alpha2 M₀ (ϖ * d) u v s| + |alpha3 M₀ (ϖ * d) u v s|) / ϖ ^ 2 ≤
          coeffConst I * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
      Matrix.rank (Rs M s - Rs M₀ s) ≤ 2 ∧
      nuc (Rs M s - Rs M₀ s) ≤ 4 / s := by
  intro s hsI
  have hs : 0 < s := hIpos hsI
  obtain ⟨hL, conj2, -, -, conj4⟩ := lem_app_de_deletion M₀ (ϖ * d) u v M s hM hs
  have hNu : 0 ≤ sqNorm u := resAux_sqNorm_nonneg u
  have hNv : 0 ≤ sqNorm v := resAux_sqNorm_nonneg v
  have hN0 : 0 ≤ sqNorm u + sqNorm v := add_nonneg hNu hNv
  have hN1 : 0 ≤ 1 + (sqNorm u + sqNorm v) := by linarith
  have hU := dlAux_U M₀ u s hs
  have hV := dlAux_V M₀ v s hs
  have hCb := coeffAux_C (delC M₀ u v s) s (sqNorm u) (sqNorm v) hs hNu hNv
    (dlAux_C M₀ u v s hs)
  have hk0 : 0 ≤ 1 / (4 * Real.sqrt s) := by positivity
  have hϖd : |ϖ * d| = ϖ * |d| := by rw [abs_mul, abs_of_nonneg hϖ0]
  have hdabs : |ϖ * d| ≤ |d| := by
    rw [hϖd]; exact mul_le_of_le_one_left (abs_nonneg d) hϖ1
  -- the constant c = 3 / (4 √s₋) and the interval endpoint s₋ = min I
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 3 / (4 * Real.sqrt (sInf I)) := ⟨_, rfl⟩
  have hCI : coeffConst I = max 1 (sInf I)⁻¹ * (1 + c) ^ 3 := by
    unfold coeffConst; rw [hc]
  have hsm : sInf I ∈ I := hI.sInf_mem ⟨s, hsI⟩
  have hspos : 0 < sInf I := hIpos hsm
  have hsle : sInf I ≤ s := csInf_le hI.bddBelow hsI
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hc1 : 1 ≤ 1 + c := by linarith
  have hkc : 3 * (1 / (4 * Real.sqrt s)) ≤ c := by
    have hσ : 0 < Real.sqrt (sInf I) := Real.sqrt_pos.mpr hspos
    have hσle : Real.sqrt (sInf I) ≤ Real.sqrt s := Real.sqrt_le_sqrt hsle
    have e : 3 * (1 / (4 * Real.sqrt s)) = 3 / (4 * Real.sqrt s) := by ring
    rw [e, hc]
    exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  have hk_le : 1 / (4 * Real.sqrt s) ≤ c := by linarith
  have hMs : max 1 s⁻¹ ≤ max 1 (sInf I)⁻¹ := max_le_max le_rfl (inv_anti₀ hspos hsle)
  have hMI1 : 1 ≤ max 1 (sInf I)⁻¹ := le_max_left _ _
  -- the radius R = 1 + c |d| N dominating both resolvent-type factors
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = 1 + c * (|d| * (sqNorm u + sqNorm v)) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by
    rw [hR]; have := mul_nonneg hc0 (mul_nonneg (abs_nonneg d) hN0); linarith
  have hRle : R ≤ (1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v)) := by
    rw [hR]; exact coeffAux_elem c |d| _ hc0 (abs_nonneg d) hN0
  have hR1 : 1 + 1 / (4 * Real.sqrt s) * (|ϖ * d| * (sqNorm u + sqNorm v)) ≤ R := by
    rw [hR]
    have := mul_le_mul hk_le (mul_le_mul_of_nonneg_right hdabs hN0)
      (mul_nonneg (abs_nonneg _) hN0) hc0
    linarith
  have hR2 : 1 + 3 * (1 / (4 * Real.sqrt s)) * (|ϖ * d| * (sqNorm u + sqNorm v)) ≤ R := by
    rw [hR]
    have := mul_le_mul hkc (mul_le_mul_of_nonneg_right hdabs hN0)
      (mul_nonneg (abs_nonneg _) hN0) hc0
    linarith
  have hinv : (delLambda M₀ (ϖ * d) u v s)⁻¹ ≤
      (1 + 3 * (1 / (4 * Real.sqrt s)) * (|ϖ * d| * (sqNorm u + sqNorm v))) ^ 2 := by
    have e : 3 / (4 * Real.sqrt s) * |ϖ * d| * (sqNorm u + sqNorm v) =
        3 * (1 / (4 * Real.sqrt s)) * (|ϖ * d| * (sqNorm u + sqNorm v)) := by ring
    rw [e] at conj4
    exact conj4
  have hα1 : |alpha1 M₀ (ϖ * d) u v s| ≤ |ϖ * d| * R ^ 3 := by
    unfold alpha1
    exact coeffAux_a1 (ϖ * d) (delC M₀ u v s) (delLambda M₀ (ϖ * d) u v s) _
      (1 / (4 * Real.sqrt s)) R hL hN0 hk0 hCb hinv hR1 hR2
  have hJ := coeffAux_joint s _ _ _ _ hs hU.1 hU.2 hV.2 hNu hNv
  have hα23 : |alpha2 M₀ (ϖ * d) u v s| + |alpha3 M₀ (ϖ * d) u v s| ≤
      (ϖ * d) ^ 2 * max 1 s⁻¹ * (sqNorm u + sqNorm v) * R ^ 2 := by
    unfold alpha2 alpha3
    exact coeffAux_a2 (ϖ * d) s (delU M₀ u s) (delV M₀ v s)
      (delLambda M₀ (ϖ * d) u v s) (sqNorm u) (sqNorm v) (max 1 s⁻¹)
      (1 / (4 * Real.sqrt s)) R hs hL hU.1 hV.1 hNu hNv hk0
      (le_trans zero_le_one (le_max_left _ _)) hJ hinv hR2
  -- the final polynomial bounds in terms of C_I
  have hX0 : 0 ≤ (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 :=
    mul_nonneg (pow_nonneg (by linarith [abs_nonneg d]) 4) (pow_nonneg hN1 3)
  have hfin1 : |d| * R ^ 3 ≤
      coeffConst I * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by
    have hR3 : R ^ 3 ≤ ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 3 :=
      pow_le_pow_left₀ hR0 hRle 3
    have step1 : |d| * R ^ 3 ≤
        (1 + |d|) * ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 3 :=
      mul_le_mul (by linarith [abs_nonneg d]) hR3 (pow_nonneg hR0 3)
        (by linarith [abs_nonneg d])
    have e1 : (1 + |d|) * ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 3 =
        (1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := by ring
    have hc3 : (1 + c) ^ 3 ≤ max 1 (sInf I)⁻¹ * (1 + c) ^ 3 :=
      le_mul_of_one_le_left (pow_nonneg (by linarith) 3) hMI1
    have h4 := mul_le_mul_of_nonneg_right hc3 hX0
    rw [hCI]
    calc |d| * R ^ 3 ≤ _ := step1
      _ = (1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := e1
      _ ≤ max 1 (sInf I)⁻¹ * (1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) :=
          h4
      _ = max 1 (sInf I)⁻¹ * (1 + c) ^ 3 * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by
          ring
  have hQ : d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2 ≤
      (1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := by
    have hd2 : d ^ 2 ≤ (1 + |d|) ^ 2 := by
      rw [← sq_abs d]; exact pow_le_pow_left₀ (abs_nonneg d) (by linarith [abs_nonneg d]) 2
    have hR2' : R ^ 2 ≤ ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 2 :=
      pow_le_pow_left₀ hR0 hRle 2
    have s1 : d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2 ≤
        (1 + |d|) ^ 2 * (sqNorm u + sqNorm v) *
          ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_right hd2 hN0) hR2' (sq_nonneg R)
        (mul_nonneg (sq_nonneg _) hN0)
    have hN3 : (sqNorm u + sqNorm v) * (1 + (sqNorm u + sqNorm v)) ^ 2 ≤
        (1 + (sqNorm u + sqNorm v)) ^ 3 := by
      have e : (1 + (sqNorm u + sqNorm v)) ^ 3 =
          (sqNorm u + sqNorm v) * (1 + (sqNorm u + sqNorm v)) ^ 2 +
            (1 + (sqNorm u + sqNorm v)) ^ 2 := by ring
      rw [e]; exact le_add_of_nonneg_right (sq_nonneg _)
    calc d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2
        ≤ (1 + |d|) ^ 2 * (sqNorm u + sqNorm v) *
          ((1 + c) * (1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 2 := s1
      _ = (1 + c) ^ 2 * ((1 + |d|) ^ 4 * ((sqNorm u + sqNorm v) * (1 + (sqNorm u + sqNorm v)) ^ 2)) := by
          ring
      _ ≤ (1 + c) ^ 2 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN3
            (pow_nonneg (by linarith [abs_nonneg d]) 4)) (pow_nonneg (by linarith) 2)
      _ ≤ (1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by norm_num)) hX0
  have hfin2 : (ϖ * d) ^ 2 * max 1 s⁻¹ * (sqNorm u + sqNorm v) * R ^ 2 ≤
      ϖ ^ 2 * (coeffConst I * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3)) := by
    have hP0 : 0 ≤ d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2 :=
      mul_nonneg (mul_nonneg (sq_nonneg d) hN0) (sq_nonneg R)
    have ea : (ϖ * d) ^ 2 * max 1 s⁻¹ * (sqNorm u + sqNorm v) * R ^ 2 =
        ϖ ^ 2 * max 1 s⁻¹ * (d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2) := by ring
    rw [ea, hCI]
    calc ϖ ^ 2 * max 1 s⁻¹ * (d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2)
        ≤ ϖ ^ 2 * max 1 (sInf I)⁻¹ * (d ^ 2 * (sqNorm u + sqNorm v) * R ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMs (sq_nonneg ϖ)) hP0
      _ ≤ ϖ ^ 2 * max 1 (sInf I)⁻¹ *
          ((1 + c) ^ 3 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3)) :=
          mul_le_mul_of_nonneg_left hQ (mul_nonneg (sq_nonneg ϖ) (le_trans zero_le_one hMI1))
      _ = ϖ ^ 2 * (max 1 (sInf I)⁻¹ * (1 + c) ^ 3 *
          ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3)) := by ring
  have p1 : |alpha1 M₀ (ϖ * d) u v s| ≤
      coeffConst I * ϖ * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by
    calc |alpha1 M₀ (ϖ * d) u v s| ≤ |ϖ * d| * R ^ 3 := hα1
      _ = ϖ * (|d| * R ^ 3) := by rw [hϖd]; ring
      _ ≤ ϖ * (coeffConst I * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) :=
          mul_le_mul_of_nonneg_left hfin1 hϖ0
      _ = coeffConst I * ϖ * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by ring
  have p2 : |alpha2 M₀ (ϖ * d) u v s| + |alpha3 M₀ (ϖ * d) u v s| ≤
      coeffConst I * ϖ ^ 2 * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 :=
    hα23.trans (hfin2.trans_eq (by ring))
  have hrank : Matrix.rank (Rs M s - Rs M₀ s) ≤ 2 := by
    rw [conj2]
    exact coeffAux_rank _ _ _ _ _
  refine ⟨p1, p2, fun hϖ => ?_, fun hϖ => ?_, hrank, ?_⟩
  · rw [abs_div, abs_of_pos hϖ, div_le_iff₀ hϖ]
    exact p1.trans_eq (by ring)
  · rw [div_le_iff₀ (pow_pos hϖ 2)]
    exact p2.trans_eq (by ring)
  · have hop : opNorm (Rs M s - Rs M₀ s) ≤ 2 / s := by
      have h1 := coeffAux_opNorm_sub (Rs M s) (Rs M₀ s)
      have h2 := resAux_opNorm_Rs M s hs
      have h3 := resAux_opNorm_Rs M₀ s hs
      have e : 2 / s = 1 / s + 1 / s := by ring
      linarith
    have hrk : (Matrix.rank (Rs M s - Rs M₀ s) : ℝ) ≤ 2 := by exact_mod_cast hrank
    have hop0 : 0 ≤ opNorm (Rs M s - Rs M₀ s) := by unfold opNorm; exact norm_nonneg _
    calc nuc (Rs M s - Rs M₀ s)
        ≤ (Matrix.rank (Rs M s - Rs M₀ s) : ℝ) * opNorm (Rs M s - Rs M₀ s) :=
          nuc_le_rank_mul_opNorm _
      _ ≤ 2 * opNorm (Rs M s - Rs M₀ s) := mul_le_mul_of_nonneg_right hrk hop0
      _ ≤ 2 * (2 / s) := mul_le_mul_of_nonneg_left hop (by norm_num)
      _ = 4 / s := by ring

private lemma lipAux_inv_diff {m : ℕ} (A B : Mat m m) (hA : IsUnit A.det) (hB : IsUnit B.det) :
    A⁻¹ - B⁻¹ = A⁻¹ * (B - A) * B⁻¹ := by
  have e1 : A⁻¹ * B * B⁻¹ = A⁻¹ := by
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hB, Matrix.mul_one]
  have e2 : A⁻¹ * A * B⁻¹ = B⁻¹ := by
    rw [Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  rw [Matrix.mul_sub, Matrix.sub_mul, e1, e2]

private lemma lipAux_resid {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) :
    Rs K s - Rs K' s = Rs K s * (K' - K) * (K'ᵀ * Rs K' s) + Rs K s * K * (K' - K)ᵀ * Rs K' s := by
  have h1 : Rs K s - Rs K' s = Rs K s * ((K' * K'ᵀ + s • (1 : Mat m m)) -
      (K * Kᵀ + s • (1 : Mat m m))) * Rs K' s :=
    lipAux_inv_diff _ _ (resAux_isUnit K s hs) (resAux_isUnit K' s hs)
  have h2 : (K' * K'ᵀ + s • (1 : Mat m m)) - (K * Kᵀ + s • (1 : Mat m m)) =
      (K' - K) * K'ᵀ + K * (K' - K)ᵀ := by
    rw [Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [h1, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

private lemma lipAux_opNorm_Rt_K {m n : ℕ} (K : Mat m n) (s : ℝ) (hs : 0 < s) :
    opNorm (Kᵀ * Rs K s) ≤ 1 / (2 * Real.sqrt s) := by
  have hI : Kᵀ * Rs K s = (Kᵀ * K + s • (1 : Mat n n))⁻¹ * Kᵀ := by
    have := resAux_intertw Kᵀ s hs
    rw [Matrix.transpose_transpose] at this
    unfold Rs
    exact this.symm
  rw [hI]
  have h := resAux_opNorm_Xs Kᵀ s hs
  unfold Xs Rs at h
  rw [Matrix.transpose_transpose] at h
  exact h

private lemma lipAux_opNorm_nonneg {m n : ℕ} (X : Mat m n) : 0 ≤ opNorm X := by
  unfold opNorm
  exact norm_nonneg _

/-- lem:app-de-lipschitz. Snapshot `cr-2026-10-22`. LaTeX (`section.tex` l.1078–1080):
\begin{lemma}[Nuclear-norm Lipschitz bound]\label{lem:app-de-lipschitz}
For $K,K'\in\R^{\Nout\times\Nin}$ and $s>0$,
$\norm{R_s(K)-R_s(K')}_*\le2s^{-3/2}\norm{K-K'}_*$. -/
theorem lem_app_de_lipschitz {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) :
    nuc (Rs K s - Rs K' s) ≤ 2 / (s * Real.sqrt s) * nuc (K - K') := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hΔ : nuc (K - K') = nuc (K' - K) := by
    have h : K - K' = (-1 : ℝ) • (K' - K) := by rw [neg_one_smul, neg_sub]
    rw [h, nuc_smul]
    simp
  have hD : 0 ≤ nuc (K' - K) := nuc_nonneg _
  have hR : opNorm (Rs K s) ≤ 1 / s := resAux_opNorm_Rs K s hs
  have hR' : opNorm (Rs K' s) ≤ 1 / s := resAux_opNorm_Rs K' s hs
  have hT : opNorm (K'ᵀ * Rs K' s) ≤ 1 / (2 * Real.sqrt s) := lipAux_opNorm_Rt_K K' s hs
  have hX : opNorm (Rs K s * K) ≤ 1 / (2 * Real.sqrt s) := resAux_opNorm_Xs K s hs
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
  have hs2 : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
  have b1 : opNorm (Rs K s) * nuc (K' - K) * opNorm (K'ᵀ * Rs K' s) ≤
      1 / s * nuc (K' - K) * (1 / (2 * Real.sqrt s)) :=
    mul_le_mul (mul_le_mul_of_nonneg_right hR hD) hT (lipAux_opNorm_nonneg _)
      (mul_nonneg hs1 hD)
  have b2 : opNorm (Rs K s * K) * nuc (K' - K)ᵀ * opNorm (Rs K' s) ≤
      1 / (2 * Real.sqrt s) * nuc (K' - K) * (1 / s) := by
    rw [nuc_transpose]
    exact mul_le_mul (mul_le_mul_of_nonneg_right hX hD) hR' (lipAux_opNorm_nonneg _)
      (mul_nonneg hs2 hD)
  have t1 := le_trans (nuc_mul_three_le (Rs K s) (K' - K) (K'ᵀ * Rs K' s)) b1
  have t2 := le_trans (nuc_mul_three_le (Rs K s * K) (K' - K)ᵀ (Rs K' s)) b2
  have hsum : 1 / s * nuc (K' - K) * (1 / (2 * Real.sqrt s)) +
      1 / (2 * Real.sqrt s) * nuc (K' - K) * (1 / s) = 1 / (s * Real.sqrt s) * nuc (K' - K) := by
    field_simp
    ring
  have hcoef : 1 / (s * Real.sqrt s) ≤ 2 / (s * Real.sqrt s) := by
    apply div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc nuc (Rs K s - Rs K' s)
      = nuc (Rs K s * (K' - K) * (K'ᵀ * Rs K' s) + Rs K s * K * (K' - K)ᵀ * Rs K' s) := by
        rw [lipAux_resid K K' s hs]
    _ ≤ nuc (Rs K s * (K' - K) * (K'ᵀ * Rs K' s)) + nuc (Rs K s * K * (K' - K)ᵀ * Rs K' s) :=
        nuc_add_le _ _
    _ ≤ 1 / s * nuc (K' - K) * (1 / (2 * Real.sqrt s)) +
        1 / (2 * Real.sqrt s) * nuc (K' - K) * (1 / s) := add_le_add t1 t2
    _ = 1 / (s * Real.sqrt s) * nuc (K' - K) := hsum
    _ ≤ 2 / (s * Real.sqrt s) * nuc (K' - K) := mul_le_mul_of_nonneg_right hcoef hD
    _ = 2 / (s * Real.sqrt s) * nuc (K - K') := by rw [hΔ]

end Muon.DetEquiv

end
