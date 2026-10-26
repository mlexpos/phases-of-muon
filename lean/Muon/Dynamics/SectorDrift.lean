import Muon.Dynamics.Sector
import Muon.Drift.Tail

/-!
# Appendix E, `lem:app-dyn-mean`(i)–(ii): the Appendix C chain at complex `z ∈ 𝕊`
(interface draft)

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, proof of `lem:app-dyn-mean`
(i) and (ii), ll. 841–903. The proof asserts that the coefficient moments, the rank, multiplier and
covariance bounds, the exact identity and the Gram-term split of Appendix C "hold for `z ∈ 𝕊`
with `s` replaced by `x` in their right sides" (ll. 858–861, 871–874), and assembles them into
`𝓗(z)𝖸_B(z) = E_0(z)`, `‖E_0(z)‖_F ≤ C/x`, `Re b_B ≥ 0` (ll. 875–893). This module states the
complex analogue of each real Lean statement used there, in the same quantifier shape, with
`s ≥ s₀` replaced by `z ∈ 𝕊`, `Re z ≥ s₀` and `s` replaced by `x = Re z` on the right. It imports
no module that imports `Muon.Dynamics.FiniteMean`.

Objects (all new, complex analogues of `Muon.Drift.Defs` and `Muon.Drift.Coefficients`):
* `XzC K z = Rres K (-z) * K.map ofReal` is the source's `𝖷_z(K)`. It is definitionally
  `Muon.Dynamics.Xz` of `FiniteMean.lean`, which is downstream; `meanC` is definitionally
  `Muon.Dynamics.cmean`, and `HmixC w F S t z` is definitionally `Muon.Dynamics.Hz w P F S t z`
  (checked by `rfl` in a scratch file importing both). A later refactor should make the
  `FiniteMean` objects abbreviations of these.
* `ageAlphaC1..3`, `delAlphaC1..3`: the coefficients `colAlpha1..3` of `Muon.Drift.Column` over
  `ℂ`, at the cast real data `(M₀, ϖ d, 𝗎, 𝗏)` of `ageAlpha1..3` / `delAlpha1..3`.
* `HjC`, `phiJC`, `bjC`, `CjC`, `bBC`, `phiFreshC`: the complex `𝓗_j(z)`, `φ_j`, `b_j`, `𝒞_j`,
  `b_B(z)`, `φ_ϖ(K)` of `eqn:app-drift-Cj`, `eqn:app-drift-phi`.
* `condExpMatC`: entrywise conditional expectation of a complex random matrix (the `ℂ` analogue of
  `Muon.Foundations.condExpMat`).
Norms of complex scalars are `‖·‖` (`= Complex.abs`); the source's `|·|`.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv Muon.Drift

noncomputable section

namespace Muon.Dynamics

variable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Complex objects -/

/-- The mixed resolvent `𝖷_z(K) = R_z(K) K = (KKᵀ + z)⁻¹ K` of a real matrix at complex `z`
(`lem:app-dyn-mean`, ll. 761–766). Definitionally `Muon.Dynamics.Xz` (`FiniteMean.lean`). -/
def XzC {m n : ℕ} (K : Mat m n) (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  Rres K (-z) * K.map (fun x : ℝ => (x : ℂ))

/-- Entrywise expectation of a complex random matrix. Definitionally `Muon.Dynamics.cmean`. -/
def meanC {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω)
    (X : Ω → Matrix (Fin m) (Fin n) ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂P

/-- Entrywise conditional expectation of a complex random matrix (the `ℂ` analogue of
`Muon.Foundations.condExpMat`). -/
def condExpMatC {Ω : Type*} {m n : ℕ} (𝒢 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : Ω → Matrix (Fin m) (Fin n) ℂ) : Ω → Matrix (Fin m) (Fin n) ℂ :=
  fun ω => Matrix.of fun i j => condExp 𝒢 μ (fun ω' => X ω' i j) ω

/-- `𝓗(z) = 𝔼 𝖷_z(M_t)` for the weighted buffer (`lem:app-dyn-mean`, l. 765). The complex
analogue of `Muon.Drift.Hmix`; definitionally `Muon.Dynamics.Hz w P F S t z`. -/
def HmixC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) :
    Matrix (Fin m) (Fin n) ℂ :=
  meanC P (fun ω => XzC (WeightedBuf w F S t ω) z)

/-- `α₁` at `z` for `(M₀, 𝗁, 𝗎, 𝗏) = (M₀, ϖ d_j, u_j, v_j)` (complex `ageAlpha1`). -/
def ageAlphaC1 (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (M0 : Ω → Mat m n) (ϖ : ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  colAlpha1 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * ageD F S t j ω : ℝ) : ℂ)
    (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)) z

/-- `α₂` at `z` (complex `ageAlpha2`). -/
def ageAlphaC2 (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (M0 : Ω → Mat m n) (ϖ : ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  colAlpha2 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * ageD F S t j ω : ℝ) : ℂ)
    (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)) z

/-- `α₃` at `z` (complex `ageAlpha3`). -/
def ageAlphaC3 (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (M0 : Ω → Mat m n) (ϖ : ℝ) (z : ℂ) (ω : Ω) : ℂ :=
  colAlpha3 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * ageD F S t j ω : ℝ) : ℂ)
    (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)) z

/-- Deleted-sample `α_{1,j}` at `z`: `ageAlphaC1` with `M₀ = M_0^{(j1)}`, `ϖ = w_j`
(complex `delAlpha1`). -/
def delAlphaC1 (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) (ω : Ω) : ℂ :=
  ageAlphaC1 F S t j (delBufAge w F S t j) (w j) z ω

/-- Deleted-sample `α_{2,j}` at `z` (complex `delAlpha2`). -/
def delAlphaC2 (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) (ω : Ω) : ℂ :=
  ageAlphaC2 F S t j (delBufAge w F S t j) (w j) z ω

/-- `𝓗_j(z) = 𝔼 𝖷_z(M_0^{(j1)})` (complex `Hj`, `eqn:app-drift-deletion-mean`). -/
def HjC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  meanC P (fun ω => XzC (delBufAge w F S t j ω) z)

/-- `φ_j = 𝔼_{𝒢_{j1}} α_{2,j1}` at `z` (complex `phiJ`, `eqn:app-drift-Cj`). -/
def phiJC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) : Ω → ℂ :=
  condExp (sigmaOthers F S t j) P (delAlphaC2 w F S t j z)

/-- `b_j = 𝔼 φ_j` at `z` (complex `bj`). -/
def bjC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) : ℂ :=
  ∫ ω, phiJC w F S t j z ω ∂P

/-- `𝒞_j = 𝔼[(φ_j − b_j) 𝖷_z(M_0^{(j1)})]` (complex `Cj`). -/
def CjC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (z : ℂ) : Matrix (Fin m) (Fin n) ℂ :=
  meanC P (fun ω => (phiJC w F S t j z ω - bjC w F S t j z) • XzC (delBufAge w F S t j ω) z)

/-- `b_B(z) = ∑_j b_j` (complex `bB`, l. 883). -/
def bBC (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) : ℂ :=
  ∑' j, bjC w F S t j z

/-- `φ_ϖ(K) = 𝔼 α₂` at `z` for a fresh sample (complex `phiFresh`, `eqn:app-drift-phi`). -/
def phiFreshC (F : FrozenParams m n B) (K : Mat m n) (ϖ : ℝ) (z : ℂ) : ℂ :=
  ∫ x, colAlpha2 (K.map (fun y : ℝ => (y : ℂ)))
      ((ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2) : ℝ) : ℂ)
      (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z ∂(freshMeas m n)

/-- `𝖸_B(z)`'s covariance factor `Σ_in` cast to `ℂ` (notation for the statements below). -/
abbrev SinC (F : FrozenParams m n B) : Matrix (Fin n) (Fin n) ℂ :=
  F.C.Sin.map (fun x : ℝ => (x : ℂ))

/-! ## Bridge to the real objects -/

private lemma sd0_self_dot {k : ℕ} (y : Fin k → ℂ) :
    star y ⬝ᵥ y = (‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2 : ℝ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ((EuclideanSpace.equiv (Fin k) ℂ).symm y)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

private lemma sd0_cs {k : ℕ} (x y : Fin k → ℂ) :
    (star y ⬝ᵥ x).re ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ *
      ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖ := by
  calc
    (star y ⬝ᵥ x).re ≤ ‖star y ⬝ᵥ x‖ := Complex.re_le_norm _
    _ = ‖inner ℂ ((EuclideanSpace.equiv (Fin k) ℂ).symm y)
        ((EuclideanSpace.equiv (Fin k) ℂ).symm x)‖ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    _ ≤ _ := norm_inner_le_norm _ _

open scoped ComplexOrder in
private lemma sd0_energy {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : G.PosSemidef)
    (z : ℂ) (x y : Fin k → ℂ)
    (hy : (G + z • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ y = x) :
    z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ≤
      ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖ := by
  have hpos := hG.re_dotProduct_nonneg y
  have hreal : (star y ⬝ᵥ x).re =
      (star y ⬝ᵥ (G *ᵥ y)).re + z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2 := by
    rw [← hy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re]
    rw [sd0_self_dot y, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hc := sd0_cs x y
  rw [hreal] at hc
  by_cases hy0 : ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ = 0
  · rw [hy0, mul_zero]
    exact norm_nonneg _
  · have hyp : 0 < ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy0)
    have hm : z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2 ≤
        ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ *
          ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖ := by
      have hp := add_le_add_right hpos
        (z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2)
      exact le_trans (by simpa [add_comm] using hp) hc
    apply le_of_mul_le_mul_left _ hyp
    nlinarith [hm]

open scoped Matrix.Norms.L2Operator in
private lemma sd0_opNorm_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin b → ℂ, ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (A *ᵥ x)‖ ≤
      c * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm x‖) : opNorm A ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv (Fin a) ℂ).symm
      (A *ᵥ (EuclideanSpace.equiv (Fin b) ℂ x))‖ ≤ c * ‖x‖
  simpa using h (EuclideanSpace.equiv (Fin b) ℂ x)

open scoped ComplexOrder in
private lemma sd0_colR_bound {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (z : ℂ) (hz : 0 < z.re)
    (hdet : IsUnit (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)).det) :
    opNorm (colR K z) ≤ 1 / z.re := by
  unfold colR
  refine sd0_opNorm_le _ (one_div_nonneg.mpr hz.le) fun x => ?_
  let y := (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *ᵥ x
  have hy : (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hG : (K * Kᵀ).PosSemidef := by
    rw [← hreal]
    exact Matrix.posSemidef_self_mul_conjTranspose K
  have he := sd0_energy (K * Kᵀ) hG z x y hy
  dsimp [y] at he ⊢
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin a) ℂ).symm x‖ / z.re :=
      (le_div_iff₀ hz).2 (by simpa [mul_comm] using he)
    _ = 1 / z.re * ‖(EuclideanSpace.equiv (Fin a) ℂ).symm x‖ := by ring

private lemma sd0_quad {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (y : Fin a → ℂ) :
    star y ⬝ᵥ ((K * Kᵀ) *ᵥ y) = star (Kᵀ *ᵥ y) ⬝ᵥ (Kᵀ *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hw : star y ᵥ* K = star (Kᵀ *ᵥ y) := by
    rw [Matrix.star_mulVec, ← hreal, Matrix.conjTranspose_conjTranspose]
  rw [hw]

private lemma sd0_cross {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (y : Fin a → ℂ) (q : Fin b → ℂ) :
    star y ⬝ᵥ (K *ᵥ q) = star (Kᵀ *ᵥ y) ⬝ᵥ q := by
  rw [Matrix.dotProduct_mulVec]
  have hw : star y ᵥ* K = star (Kᵀ *ᵥ y) := by
    rw [Matrix.star_mulVec, ← hreal, Matrix.conjTranspose_conjTranspose]
  rw [hw]

private lemma sd0_mixed_bound {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (z : ℂ) (hz : 0 < z.re)
    (hdet : IsUnit (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)).det) :
    opNorm (colR K z * K) ≤ 1 / (2 * Real.sqrt z.re) := by
  refine sd0_opNorm_le _ (div_nonneg zero_le_one (by positivity)) fun q => ?_
  let y := (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *ᵥ (K *ᵥ q)
  have hy : (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ y = K *ᵥ q := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have heq : star (Kᵀ *ᵥ y) ⬝ᵥ q =
      star (Kᵀ *ᵥ y) ⬝ᵥ (Kᵀ *ᵥ y) + z * (star y ⬝ᵥ y) := by
    rw [← sd0_cross K hreal y q, ← hy, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, sd0_quad K hreal]
  have hcs := sd0_cs q (Kᵀ *ᵥ y)
  have hrealEq := congrArg Complex.re heq
  rw [sd0_self_dot (Kᵀ *ᵥ y), sd0_self_dot y] at hrealEq
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] at hrealEq
  have hmain : ‖(EuclideanSpace.equiv (Fin b) ℂ).symm (Kᵀ *ᵥ y)‖ ^ 2 +
      z.re * ‖(EuclideanSpace.equiv (Fin a) ℂ).symm y‖ ^ 2 ≤
      ‖(EuclideanSpace.equiv (Fin b) ℂ).symm (Kᵀ *ᵥ y)‖ *
        ‖(EuclideanSpace.equiv (Fin b) ℂ).symm q‖ := by
    rw [← hrealEq]
    exact hcs
  have hsq : 4 * z.re * ‖(EuclideanSpace.equiv (Fin a) ℂ).symm y‖ ^ 2 ≤
      ‖(EuclideanSpace.equiv (Fin b) ℂ).symm q‖ ^ 2 := by
    nlinarith [sq_nonneg
      (2 * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm (Kᵀ *ᵥ y)‖ -
        ‖(EuclideanSpace.equiv (Fin b) ℂ).symm q‖)]
  dsimp [y] at hsq ⊢
  rw [← Matrix.mulVec_mulVec]
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  have hs : Real.sqrt z.re ^ 2 = z.re := Real.sq_sqrt hz.le
  calc
    ‖(EuclideanSpace.equiv (Fin a) ℂ).symm
        ((K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *ᵥ (K *ᵥ q))‖ ^ 2
        ≤ ‖(EuclideanSpace.equiv (Fin b) ℂ).symm q‖ ^ 2 / (4 * z.re) :=
      (le_div_iff₀ (by positivity : 0 < 4 * z.re)).2 (by nlinarith [hsq])
    _ = (1 / (2 * Real.sqrt z.re) *
        ‖(EuclideanSpace.equiv (Fin b) ℂ).symm q‖) ^ 2 := by
      rw [mul_pow, div_pow, one_pow, mul_pow, hs]
      ring


open scoped Matrix.Norms.L2Operator in
private lemma sd0_entry_le {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℂ) (i : Fin p) (j : Fin q) :
    ‖A i j‖ ≤ opNorm A := by
  have h1 := Matrix.l2_opNorm_mulVec A (EuclideanSpace.single j (1 : ℂ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℂ).symm
    (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℂ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℂ).symm
      (A *ᵥ ⇑(EuclideanSpace.single j (1 : ℂ)))) i = A i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3] at h2
  rw [opNorm_eq_norm]
  linarith

open scoped Matrix.Norms.L2Operator in
private lemma sd0_opNorm_mul {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ)
    (B : Matrix (Fin b) (Fin c) ℂ) : opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

private lemma sd0_unit {m n : ℕ} (K : Mat m n) (z : ℂ) (hz : 0 < z.re) :
    IsUnit (K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ +
      z • (1 : Matrix (Fin m) (Fin m) ℂ)).det := by
  have hznot : ∀ r : ℝ, 0 ≤ r → -z ≠ (r : ℂ) := by
    intro r hr he
    have hre := congrArg Complex.re he
    simp only [map_neg, Complex.neg_re, Complex.ofReal_re] at hre
    linarith
  obtain ⟨hu, -⟩ := gram_isUnit K (-z) hznot
  have hG : (K * Kᵀ).map Complex.ofReal =
      K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ := by
    rw [← Matrix.transpose_map]
    exact Matrix.map_mul (f := Complex.ofRealHom)
  rw [hG, neg_smul, sub_neg_eq_add] at hu
  exact (Matrix.isUnit_iff_isUnit_det _).mp hu

private lemma sd0_Rres_eq {m n : ℕ} (K : Mat m n) (z : ℂ) :
    Rres K (-z) = (K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ +
      z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ := by
  rw [rres_neg_eq_colR]; rfl

private lemma sd0_R_bound {m n : ℕ} (K : Mat m n) (z : ℂ) (hz : 0 < z.re) :
    opNorm (Rres K (-z)) ≤ 1 / z.re := by
  have hreal : (K.map (fun x : ℝ => (x : ℂ)))ᴴ = (K.map (fun x : ℝ => (x : ℂ)))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [rres_neg_eq_colR]
  exact sd0_colR_bound _ hreal z hz (sd0_unit K z hz)

private lemma sd0_X_bound {m n : ℕ} (K : Mat m n) (z : ℂ) (hz : 0 < z.re) :
    opNorm (XzC K z) ≤ 1 / (2 * Real.sqrt z.re) := by
  have hreal : (K.map (fun x : ℝ => (x : ℂ)))ᴴ = (K.map (fun x : ℝ => (x : ℂ)))ᵀ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  unfold XzC
  rw [rres_neg_eq_colR]
  exact sd0_mixed_bound _ hreal z hz (sd0_unit K z hz)

/-- resolvent identity -/
private lemma sd0_resid {a : ℕ} (G : Matrix (Fin a) (Fin a) ℂ) (z w : ℂ)
    (hz : IsUnit (G + z • (1 : Matrix (Fin a) (Fin a) ℂ)).det)
    (hw : IsUnit (G + w • (1 : Matrix (Fin a) (Fin a) ℂ)).det) :
    (G + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ - (G + w • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ =
      (w - z) • ((G + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *
        (G + w • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹) := by
  have h1 := Matrix.nonsing_inv_mul _ hz
  have h2 := Matrix.mul_nonsing_inv _ hw
  have e : (G + w • (1 : Matrix (Fin a) (Fin a) ℂ)) - (G + z • (1 : Matrix (Fin a) (Fin a) ℂ)) =
      (w - z) • (1 : Matrix (Fin a) (Fin a) ℂ) := by
    rw [add_sub_add_left_eq_sub, ← sub_smul]
  calc _ = (G + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *
        ((G + w • (1 : Matrix (Fin a) (Fin a) ℂ)) - (G + z • (1 : Matrix (Fin a) (Fin a) ℂ))) *
        (G + w • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ := by
        rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1,
          Matrix.one_mul]
    _ = _ := by rw [e, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

private lemma sd0_X_diff {m n : ℕ} (K : Mat m n) (z w : ℂ) (hz : 0 < z.re) (hw : 0 < w.re) :
    XzC K z - XzC K w = (w - z) • (Rres K (-z) * XzC K w) := by
  unfold XzC
  rw [← Matrix.sub_mul, sd0_Rres_eq, sd0_Rres_eq, sd0_resid _ z w (sd0_unit K z hz)
    (sd0_unit K w hw), Matrix.smul_mul, ← Matrix.mul_assoc]


private lemma sd0_posDef {m n : ℕ} (M : Mat m n) {c : ℝ} (hc : 0 < c) :
    (M * Mᵀ + c • (1 : Mat m m)).PosDef := by
  have h0 : (M * Mᵀ).PosSemidef := by
    simpa using Matrix.posSemidef_self_mul_conjTranspose M
  have hd : (c • (1 : Mat m m)).PosDef := by
    have : c • (1 : Mat m m) = Matrix.diagonal (fun _ : Fin m => c) := by
      ext i j
      by_cases h : i = j <;> simp [h]
    rw [this]
    exact Matrix.posDef_diagonal_iff.mpr (fun _ => hc)
  rw [add_comm]
  exact hd.add_posSemidef h0

private lemma sd0_Xz_ofReal {m n : ℕ} (K : Mat m n) {x : ℝ} (hx : 0 < x) (i : Fin m) (j : Fin n) :
    XzC K (x : ℂ) i j = ((Muon.DetEquiv.Xs K x i j : ℝ) : ℂ) := by
  set A : Mat m m := K * Kᵀ + x • (1 : Mat m m) with hA
  have hdet : A.det ≠ 0 := (sd0_posDef K hx).det_pos.ne'
  have h1 : (K * Kᵀ).map (fun r : ℝ => (r : ℂ)) - (-(x : ℂ)) • (1 : Matrix (Fin m) (Fin m) ℂ) =
      A.map (fun r : ℝ => (r : ℂ)) := by
    ext a b
    by_cases h : a = b <;> simp [hA, Matrix.map_apply, h]
  have e : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hdet)
  have h2 : A.map (fun r : ℝ => (r : ℂ)) * (A⁻¹).map (fun r : ℝ => (r : ℂ)) = 1 := by
    have := Matrix.map_mul (L := A) (M := A⁻¹) (f := Complex.ofRealHom)
    rw [e, Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this.symm
  have h4 : Rres K (-(x : ℂ)) = (A⁻¹).map (fun r : ℝ => (r : ℂ)) := by
    unfold Rres
    rw [h1]
    exact Matrix.inv_eq_right_inv h2
  have h5 : XzC K (x : ℂ) = (Muon.DetEquiv.Xs K x).map (fun r : ℝ => (r : ℂ)) := by
    unfold XzC
    rw [h4]
    have := Matrix.map_mul (L := A⁻¹) (M := K) (f := Complex.ofRealHom)
    exact this.symm
  rw [h5]; rfl


private lemma sd0_contAt_R {m n : ℕ} (K : Mat m n) (z0 : ℂ) (hz0 : 0 < z0.re) :
    ContinuousAt (fun z : ℂ => Rres K (-z)) z0 := by
  have hc : Continuous (fun z : ℂ => K.map (fun x : ℝ => (x : ℂ)) *
      (K.map (fun x : ℝ => (x : ℂ)))ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    fun_prop
  have hd : ContinuousAt Ring.inverse (K.map (fun x : ℝ => (x : ℂ)) *
      (K.map (fun x : ℝ => (x : ℂ)))ᵀ + z0 • (1 : Matrix (Fin m) (Fin m) ℂ)).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (sd0_unit K z0 hz0))
  simp_rw [sd0_Rres_eq]
  exact (continuousAt_matrix_inv _ hd).comp_of_eq hc.continuousAt rfl

private lemma sd0_cont_R {m n : ℕ} (z : ℂ) (hz : 0 < z.re) :
    Continuous (fun K : Mat m n => Rres K (-z)) := by
  have hc : Continuous (fun K : Mat m n => K.map (fun x : ℝ => (x : ℂ)) *
      (K.map (fun x : ℝ => (x : ℂ)))ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) := by
    have : Continuous (fun K : Mat m n => K.map (fun x : ℝ => (x : ℂ))) :=
      Continuous.matrix_map continuous_id Complex.continuous_ofReal
    fun_prop
  simp_rw [sd0_Rres_eq]
  rw [continuous_iff_continuousAt]
  intro K
  have hd : ContinuousAt Ring.inverse (K.map (fun x : ℝ => (x : ℂ)) *
      (K.map (fun x : ℝ => (x : ℂ)))ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp (sd0_unit K z hz))
  exact (continuousAt_matrix_inv _ hd).comp_of_eq hc.continuousAt rfl

private lemma sd0_cont_X {m n : ℕ} (z : ℂ) (hz : 0 < z.re) :
    Continuous (fun K : Mat m n => XzC K z) := by
  have : Continuous (fun K : Mat m n => K.map (fun x : ℝ => (x : ℂ))) :=
    Continuous.matrix_map continuous_id Complex.continuous_ofReal
  exact (sd0_cont_R z hz).matrix_mul this

private lemma sd0_hasDeriv {m n : ℕ} (K : Mat m n) (z0 : ℂ) (hz0 : 0 < z0.re) (i : Fin m)
    (k : Fin n) :
    HasDerivAt (fun z => XzC K z i k) (-(Rres K (-z0) * XzC K z0) i k) z0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcont : ContinuousAt (fun z : ℂ => (Rres K (-z) * XzC K z0) i k) z0 := by
    have h2 : Continuous (fun M : Matrix (Fin m) (Fin m) ℂ => (M * XzC K z0) i k) :=
      (continuous_id.matrix_mul continuous_const).matrix_elem i k
    exact h2.continuousAt.comp (sd0_contAt_R K z0 hz0)
  have ht : Tendsto (fun z : ℂ => -((Rres K (-z) * XzC K z0) i k)) (𝓝[≠] z0)
      (𝓝 (-(Rres K (-z0) * XzC K z0) i k)) :=
    hcont.neg.tendsto.mono_left nhdsWithin_le_nhds
  refine ht.congr' ?_
  have hre : ∀ᶠ z in 𝓝 z0, 0 < z.re :=
    IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hz0
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds hre, self_mem_nhdsWithin] with z hz hne
  have hne' : z - z0 ≠ 0 := sub_ne_zero.mpr hne
  have hd := congrFun (congrFun (sd0_X_diff K z z0 hz hz0) i) k
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hd
  rw [slope_def_field, show XzC K z i k - XzC K z0 i k = (z0 - z) * _ from hd]
  field_simp
  ring

open scoped Matrix.Norms.L2Operator in
private lemma sd0_lip {m n : ℕ} (K : Mat m n) (r : ℝ) (hr : 0 < r) (z w : ℂ) (hz : r ≤ z.re)
    (hw : r ≤ w.re) (i : Fin m) (k : Fin n) :
    ‖XzC K z i k - XzC K w i k‖ ≤ (1 / r * (1 / (2 * Real.sqrt r))) * ‖z - w‖ := by
  have hz0 : 0 < z.re := lt_of_lt_of_le hr hz
  have hw0 : 0 < w.re := lt_of_lt_of_le hr hw
  have hd := congrFun (congrFun (sd0_X_diff K z w hz0 hw0) i) k
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at hd
  rw [hd, norm_mul, norm_sub_rev w z]
  have h1 : ‖(Rres K (-z) * XzC K w) i k‖ ≤ 1 / r * (1 / (2 * Real.sqrt r)) := by
    refine (sd0_entry_le _ i k).trans ((sd0_opNorm_mul _ _).trans ?_)
    have a1 : opNorm (Rres K (-z)) ≤ 1 / r :=
      (sd0_R_bound K z hz0).trans (one_div_le_one_div_of_le hr hz)
    have a2 : opNorm (XzC K w) ≤ 1 / (2 * Real.sqrt r) :=
      (sd0_X_bound K w hw0).trans (one_div_le_one_div_of_le (by positivity)
        (by have := Real.sqrt_le_sqrt hw; linarith))
    have a3 : 0 ≤ opNorm (XzC K w) := by rw [opNorm_eq_norm]; exact norm_nonneg _
    exact mul_le_mul a1 a2 a3 (by positivity)
  nlinarith [norm_nonneg (z - w), h1]

private lemma sd0_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma sd0_meas_WB {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (Muon.DetEquiv.WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := sd0_hQ F
  unfold Muon.DetEquiv.WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

/-- At real `z = s > 0` the complex expected mixed resolvent is the cast of the real one:
`𝓗(s) = 𝔼 𝖷_s(M_t)` "at real `z = s` these are the objects of `eqn:app-de-RXdef`"
(`sections/05-dynamics/section.tex` ll. 765–766). This is how every `_sector` statement below
specializes to its real counterpart. -/
theorem hmixC_ofReal (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (s : ℝ) (hs : 0 < s) :
    HmixC w F S t (s : ℂ) = (Hmix w F S t s).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  simp only [HmixC, meanC, Hmix, Muon.mean, Matrix.of_apply, Matrix.map_apply]
  rw [← integral_complex_ofReal]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => sd0_Xz_ofReal _ hs i j)

/-! ## Coefficient moments (`lem:app-drift-coeffmoments` over `𝕊`) -/

private lemma sd1pf_sqNorm_nonneg {k : ℕ} (x : Vec k) : 0 ≤ sqNorm x := by
  unfold sqNorm; exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma sd1pf_eucNorm_sq {k : ℕ} (z : Vec k) : eucNorm z ^ 2 = sqNorm z := by
  unfold eucNorm sqNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

private lemma sd1_cond {Ω' E : Type*} {G : MeasurableSpace Ω'} [mΩ' : MeasurableSpace Ω'] [MeasurableSpace E]
    {P : Measure Ω'} [IsProbabilityMeasure P] (hG : G ≤ mΩ')
    (X : Ω' → E) (hX : Measurable X)
    (hind : Indep G (MeasurableSpace.comap X inferInstance) P)
    (H : E → ℝ) (hH : Measurable H) (hHint : Integrable (fun ω => H (X ω)) P)
    (f : Ω' → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 ≤ c)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfle : ∀ ω, f ω ≤ c * H (X ω)) :
    Integrable f P ∧ ∀ᵐ ω ∂P, condExp G P f ω ≤ c * ∫ ω', H (X ω') ∂P := by
  have hcH : Integrable (fun ω => c * H (X ω)) P := hHint.const_mul c
  have hfi : Integrable f P := by
    refine Integrable.mono' hcH hf.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
    exact hfle ω
  refine ⟨hfi, ?_⟩
  have h1 : condExp G P f ≤ᵐ[P] condExp G P (fun ω => c * H (X ω)) :=
    condExp_mono hfi hcH (Filter.Eventually.of_forall hfle)
  have h2 : condExp G P (fun ω => c * H (X ω)) =ᵐ[P] fun ω => c * condExp G P (fun ω' => H (X ω')) ω :=
    condExp_smul c (fun ω => H (X ω)) G
  have hmeas : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun ω => H (X ω)) :=
    (hH.comp (comap_measurable X)).stronglyMeasurable
  have h3 : condExp G P (fun ω => H (X ω)) =ᵐ[P] fun _ => ∫ ω', H (X ω') ∂P :=
    condExp_indep_eq (hX.comap_le) hG hmeas hind.symm
  filter_upwards [h1, h2, h3] with ω a b d
  have d' : condExp G P (fun ω => H (X ω)) ω = ∫ ω', H (X ω') ∂P := d
  have b' : condExp G P (fun ω => c * H (X ω)) ω = c * condExp G P (fun ω => H (X ω)) ω := b
  calc condExp G P f ω ≤ condExp G P (fun ω => c * H (X ω)) ω := a
    _ = _ := by rw [b', d']

private lemma sd1_lint_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (p : ENNReal) μ ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (K ^ p) := by
  have hp0 : ((p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _)
    hf.aestronglyMeasurable, ENNReal.toReal_natCast] at h
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 := ENNReal.rpow_le_rpow h hpr.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hK hpr.le, Real.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr.le,
    Real.rpow_natCast]

private lemma sd1_one_add_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) : (1 + a) ^ p ≤ 2 ^ p * (1 + a ^ p) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + a ^ p) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ha p])
  · calc (1 + a) ^ p ≤ (2 * a) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * a ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + a ^ p) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma sd1_pow_moment {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (k : ℕ) (hk : 1 ≤ k) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (k : ENNReal) μ ≤ ENNReal.ofReal K) :
    Integrable (fun x => |f x| ^ k) μ ∧ ∫ x, |f x| ^ k ∂μ ≤ K ^ k := by
  have hl := sd1_lint_pow μ f hf k hk K hK h
  have hm : Measurable (fun x => |f x| ^ k) := by fun_prop
  have hnn : 0 ≤ᵐ[μ] (fun x => |f x| ^ k) := Filter.Eventually.of_forall fun x => by positivity
  have hint : Integrable (fun x => |f x| ^ k) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hl

private lemma sd1_W_moment (p : ℕ) (hp : 1 ≤ p) (CS γ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (C : Covariances m n)
      (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
      (hC : opNorm C.Sout ≤ CS ∧ opNorm C.Sin ≤ CS) (Ah : Mat m n) (hA : fro Ah = 1),
      Integrable (fun x : Vec m × Vec n =>
        ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) (gaussPair m n) ∧
      ∫ x, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p ∂(gaussPair m n) ≤ K := by
  obtain ⟨Kd, hKd0, hKd⟩ : ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (m n : ℕ) (Ah : Mat m n), fro Ah = 1 →
      eLpNorm (fun x => resid Ah x) ((8 * p : ℕ) : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal Kd := by
    refine ⟨((Nat.doubleFactorial (8 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / ((4 * p : ℕ) : ℝ)),
      by positivity, fun m n Ah hA => ?_⟩
    have := lem_app_de_moments_ii Ah hA (4 * p) (by omega)
    have e : 2 * (4 * p) = 8 * p := by ring
    rw [e] at this
    exact this
  obtain ⟨KN, hKN0, hKN⟩ : ∃ KN : ℝ, 0 ≤ KN ∧ ∀ (m n B : ℕ) (C : Covariances m n)
      (hdim : (m : ℝ) ≤ (max γ 0) * (B : ℝ) ∧ (n : ℝ) ≤ (max γ 0) * (B : ℝ))
      (hC : opNorm C.Sout ≤ max CS 0 ∧ opNorm C.Sin ≤ max CS 0),
      eLpNorm (momN C B) ((6 * p : ℕ) : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal KN := by
    refine ⟨2 * max CS 0 * max γ 0 *
      ((Nat.doubleFactorial (2 * (6 * p) - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / ((6 * p : ℕ) : ℝ)),
      by positivity, fun m n B C hdim hC => ?_⟩
    exact lem_app_de_moments_i C B (max γ 0) (max CS 0) hdim hC (6 * p) (by omega)
  refine ⟨2 ^ (8 * p) * (1 + Kd ^ (8 * p)) + 2 ^ (6 * p) * (1 + KN ^ (6 * p)), by positivity,
    fun m n B C hdim hγ hC Ah hA => ?_⟩
  have hdim' : (m : ℝ) ≤ (max γ 0) * (B : ℝ) ∧ (n : ℝ) ≤ (max γ 0) * (B : ℝ) := by
    rw [max_eq_left hγ]; exact hdim
  have hC' : opNorm C.Sout ≤ max CS 0 ∧ opNorm C.Sin ≤ max CS 0 :=
    ⟨hC.1.trans (le_max_left _ _), hC.2.trans (le_max_left _ _)⟩
  have hNm : Measurable (momN C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hNnn : ∀ x, 0 ≤ momN C B x := fun x => by unfold momN; positivity
  have hdm : Measurable (fun x : Vec m × Vec n => resid Ah x) := by unfold resid; fun_prop
  obtain ⟨hdI, hdB⟩ := sd1_pow_moment (gaussPair m n) (fun x => resid Ah x) hdm (8 * p)
    (by omega) Kd hKd0 (hKd m n Ah hA)
  obtain ⟨hNI, hNB⟩ := sd1_pow_moment (gaussPair m n) (momN C B) hNm (6 * p)
    (by omega) KN hKN0 (hKN m n B C hdim' hC')
  have habsN : ∀ x : Vec m × Vec n, |momN C B x| = momN C B x := fun x => abs_of_nonneg (hNnn x)
  simp_rw [habsN] at hNI hNB
  have hpt : ∀ x : Vec m × Vec n, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p
      ≤ (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p) := by
    intro x
    have ha := sd1_one_add_pow _ (abs_nonneg (resid Ah x)) (8 * p)
    have hb := sd1_one_add_pow _ (hNnn x) (6 * p)
    have h1 : ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p
        = (1 + |resid Ah x|) ^ (4 * p) * (1 + momN C B x) ^ (3 * p) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have h2 : (1 + |resid Ah x|) ^ (4 * p) * (1 + momN C B x) ^ (3 * p)
        ≤ (1 + |resid Ah x|) ^ (8 * p) + (1 + momN C B x) ^ (6 * p) := by
      have e1 : (1 + |resid Ah x|) ^ (8 * p) = ((1 + |resid Ah x|) ^ (4 * p)) ^ 2 := by
        rw [← pow_mul]; ring_nf
      have e2 : (1 + momN C B x) ^ (6 * p) = ((1 + momN C B x) ^ (3 * p)) ^ 2 := by
        rw [← pow_mul]; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg ((1 + |resid Ah x|) ^ (4 * p) - (1 + momN C B x) ^ (3 * p)),
        pow_nonneg (by linarith [abs_nonneg (resid Ah x)] : (0 : ℝ) ≤ 1 + |resid Ah x|) (4 * p),
        pow_nonneg (by linarith [hNnn x] : (0 : ℝ) ≤ 1 + momN C B x) (3 * p)]
    rw [h1]
    nlinarith [h2, ha, hb]
  have hg : Integrable (fun x : Vec m × Vec n =>
      (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p)) (gaussPair m n) :=
    ((integrable_const _).add (hdI.const_mul _)).add (hNI.const_mul _)
  have hWm : Measurable (fun x : Vec m × Vec n =>
      ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) := by
    have : Measurable (fun x : Vec m × Vec n => resid Ah x) := hdm
    fun_prop
  have hWI : Integrable (fun x : Vec m × Vec n =>
      ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) (gaussPair m n) := by
    refine Integrable.mono' hg hWm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hNnn x; positivity)]
    exact hpt x
  refine ⟨hWI, ?_⟩
  calc ∫ x, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p ∂(gaussPair m n)
      ≤ ∫ x, ((2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p)) ∂(gaussPair m n) :=
        integral_mono hWI hg hpt
    _ = (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * ∫ x, |resid Ah x| ^ (8 * p) ∂(gaussPair m n)
        + 2 ^ (6 * p) * ∫ x, momN C B x ^ (6 * p) ∂(gaussPair m n) := by
        have h1 : Integrable (fun x : Vec m × Vec n =>
            (2 ^ (8 * p) + 2 ^ (6 * p) : ℝ) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p))
            (gaussPair m n) := (integrable_const _).add (hdI.const_mul _)
        rw [integral_add h1 (hNI.const_mul _), integral_add (integrable_const _) (hdI.const_mul _),
          integral_const_mul, integral_const_mul]
        simp
    _ ≤ 2 ^ (8 * p) * (1 + Kd ^ (8 * p)) + 2 ^ (6 * p) * (1 + KN ^ (6 * p)) := by
        have := mul_le_mul_of_nonneg_left hdB (by positivity : (0 : ℝ) ≤ 2 ^ (8 * p))
        have := mul_le_mul_of_nonneg_left hNB (by positivity : (0 : ℝ) ≤ 2 ^ (6 * p))
        nlinarith



private lemma sd1_Rtil_eq {m n : ℕ} (K : Mat m n) (w : ℂ) : Rtil K w = Rres Kᵀ w := by
  unfold Rtil Rres; rw [Matrix.transpose_transpose]

private lemma sd1_alpha_cont {m n : ℕ} (z : ℂ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colAlpha1 (q.1.map (fun x : ℝ => (x : ℂ))) ((q.2.1 : ℝ) : ℂ)
        (fun i => (q.2.2.1 i : ℂ)) (fun i => (q.2.2.2 i : ℂ)) z) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colAlpha2 (q.1.map (fun x : ℝ => (x : ℂ))) ((q.2.1 : ℝ) : ℂ)
        (fun i => (q.2.2.1 i : ℂ)) (fun i => (q.2.2.2 i : ℂ)) z) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colAlpha3 (q.1.map (fun x : ℝ => (x : ℂ))) ((q.2.1 : ℝ) : ℂ)
        (fun i => (q.2.2.1 i : ℂ)) (fun i => (q.2.2.2 i : ℂ)) z) := by
  have hR : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colR (q.1.map (fun x : ℝ => (x : ℂ))) z) := by
    have : (fun q : Mat m n × ℝ × Vec m × Vec n => colR (q.1.map (fun x : ℝ => (x : ℂ))) z) =
        fun q => Rres q.1 (-z) := by
      funext q; exact (rres_neg_eq_colR q.1 z).symm
    rw [this]
    exact (sd0_cont_R z hz).comp continuous_fst
  have hRt : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colRt (q.1.map (fun x : ℝ => (x : ℂ))) z) := by
    have : (fun q : Mat m n × ℝ × Vec m × Vec n => colRt (q.1.map (fun x : ℝ => (x : ℂ))) z) =
        fun q => Rres q.1ᵀ (-z) := by
      funext q; rw [← rtil_neg_eq_colRt, sd1_Rtil_eq]
    rw [this]
    exact (sd0_cont_R z hz).comp (continuous_fst.matrix_transpose)
  have hMc : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      q.1.map (fun x : ℝ => (x : ℂ))) :=
    Continuous.matrix_map continuous_fst Complex.continuous_ofReal
  have hh : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n => ((q.2.1 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (continuous_fst.comp continuous_snd)
  have hu : ∀ i, Continuous (fun q : Mat m n × ℝ × Vec m × Vec n => ((q.2.2.1 i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_fst.comp (continuous_snd.comp continuous_snd)))
  have hv : ∀ i, Continuous (fun q : Mat m n × ℝ × Vec m × Vec n => ((q.2.2.2 i : ℝ) : ℂ)) :=
    fun i => Complex.continuous_ofReal.comp
      ((continuous_apply i).comp (continuous_snd.comp (continuous_snd.comp continuous_snd)))
  have hU : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colU (q.1.map (fun x : ℝ => (x : ℂ))) (fun i => (q.2.2.1 i : ℂ)) z) := by
    unfold colU
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finset_sum _ fun i _ => (hu i).mul (continuous_finset_sum _ fun j _ =>
      (hR.matrix_elem i j).mul (hu j))
  have hV : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colV (q.1.map (fun x : ℝ => (x : ℂ))) (fun i => (q.2.2.2 i : ℂ)) z) := by
    unfold colV
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finset_sum _ fun i _ => (hv i).mul (continuous_finset_sum _ fun j _ =>
      (hRt.matrix_elem i j).mul (hv j))
  have hC : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colC (q.1.map (fun x : ℝ => (x : ℂ))) (fun i => (q.2.2.1 i : ℂ))
        (fun i => (q.2.2.2 i : ℂ)) z) := by
    unfold colC colX
    simp only [dotProduct, Matrix.mulVec]
    have hX : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
        colR (q.1.map (fun x : ℝ => (x : ℂ))) z * q.1.map (fun x : ℝ => (x : ℂ))) :=
      hR.matrix_mul hMc
    exact continuous_finset_sum _ fun i _ => (hu i).mul (continuous_finset_sum _ fun j _ =>
      (hX.matrix_elem i j).mul (hv j))
  have hL : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      colLambda (q.1.map (fun x : ℝ => (x : ℂ))) ((q.2.1 : ℝ) : ℂ)
        (fun i => (q.2.2.1 i : ℂ)) (fun i => (q.2.2.2 i : ℂ)) z) := by
    unfold colLambda
    exact ((continuous_const.add (hh.mul hC)).pow 2).add
      ((((continuous_const.mul (hh.pow 2)).mul hU).mul hV))
  have hne : ∀ q : Mat m n × ℝ × Vec m × Vec n,
      colLambda (q.1.map (fun x : ℝ => (x : ℂ))) ((q.2.1 : ℝ) : ℂ)
        (fun i => (q.2.2.1 i : ℂ)) (fun i => (q.2.2.2 i : ℂ)) z ≠ 0 := fun q =>
    (lem_app_de_deletion_sector q.1 q.2.1 q.2.2.1 q.2.2.2 _ z rfl hz hzS).1
  refine ⟨?_, ?_, ?_⟩
  · unfold colAlpha1
    exact (hh.mul (continuous_const.add (hh.mul hC))).div hL hne
  · unfold colAlpha2
    exact ((hh.pow 2).mul hU).div hL hne
  · unfold colAlpha3
    exact ((continuous_const.mul (hh.pow 2)).mul hV).neg.div hL hne

private lemma sd1_meas_comp {Ω : Type*} [MeasurableSpace Ω] {α β : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β] [MeasurableSpace β]
    [BorelSpace β] (f : α → β) (hf : Continuous f) {q : Ω → α} (hq : Measurable q) :
    Measurable (fun ω => f (q ω)) := hf.measurable.comp hq

private lemma sd1_sq_eq {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) :
    sqNorm (momU F.C B x) + sqNorm (momV F.C B x) = momN F.C B x := by
  simp only [momN, sd1pf_eucNorm_sq]

set_option maxHeartbeats 1000000 in
private theorem sd1_main (p : ℕ) (hp : 1 ≤ p) (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ : ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        (∀ ω, 0 ≤ (ageAlphaC2 F S t j M0 ϖ z ω).re) ∧
        (Integrable (fun ω => ‖ageAlphaC1 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC1 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ) ^ p) ∧
        (Integrable (fun ω => ‖ageAlphaC3 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC3 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ ^ 2) ^ p) ∧
        (Integrable (fun ω => ‖ageAlphaC2 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC2 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ ^ 2 / z.re) ^ p) := by
  obtain ⟨K0, hK00, hK0⟩ := sd1_W_moment p hp CS γ
  obtain ⟨c, hc⟩ := lem_app_de_coeff_sector s0 hs0
  obtain ⟨c', hc'⟩ : ∃ c' : ℝ, c' = max c 0 := ⟨_, rfl⟩
  have hc'0 : 0 ≤ c' := by rw [hc']; exact le_max_right _ _
  have hcc' : c ≤ c' := by rw [hc']; exact le_max_left _ _
  obtain ⟨Mom, hMom⟩ : ∃ Mom : ℝ, Mom = max 1 K0 := ⟨_, rfl⟩
  have hMom1 : 1 ≤ Mom := by rw [hMom]; exact le_max_left _ _
  have hK0Mom : K0 ≤ Mom ^ p := by
    calc K0 ≤ Mom := by rw [hMom]; exact le_max_right _ _
      _ ≤ Mom ^ p := le_self_pow₀ hMom1 (by omega)
  refine ⟨c' * Mom, ?_⟩
  intro Ω inst m n B P _ F S t j M0 ϖ hCo hCi hm hn hϖ0 hϖ1 hM0 z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM0m : Measurable M0 := hM0.mono hG le_rfl
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  have hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ) := ⟨hm, hn⟩
  obtain ⟨hWI, hWB⟩ := hK0 m n B F.C hdim hγ ⟨hCo, hCi⟩ F.A F.hA
  set Wb : Vec m × Vec n → ℝ := fun x => (1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3 with hWbdef
  set W : Vec m × Vec n → ℝ := fun x => Wb x ^ p with hWdef
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hNm : Measurable (momN F.C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hWm : Measurable W := by
    simp only [hWdef, hWbdef]
    fun_prop
  have hWnn : ∀ x, 0 ≤ Wb x := fun x => by
    have : 0 ≤ momN F.C B x := by unfold momN; positivity
    simp only [hWbdef]; positivity
  have hHint : Integrable (fun ω => W (X ω)) P := by
    have : Integrable W (P.map X) := by rw [hlaw]; exact hWI
    exact (integrable_map_measure hWm.aestronglyMeasurable hX.aemeasurable).mp this
  have hHval : ∫ ω, W (X ω) ∂P ≤ Mom ^ p := by
    have : ∫ y, W y ∂(P.map X) = ∫ ω, W (X ω) ∂P :=
      integral_map hX.aemeasurable hWm.aestronglyMeasurable
    rw [← this, hlaw]
    exact hWB.trans hK0Mom
  have key : ∀ (A : Ω → ℂ) (k : ℝ), Measurable A → 0 ≤ k → (∀ ω, ‖A ω‖ ≤ k * Wb (X ω)) →
      Integrable (fun ω => ‖A ω‖ ^ p) P ∧
        ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P (fun ω' => ‖A ω'‖ ^ p) ω ≤ (k * Mom) ^ p := by
    intro A k hA hk hle
    obtain ⟨hi, hc⟩ := sd1_cond hG X hX hind W hWm hHint (fun ω => ‖A ω‖ ^ p)
      (by have := hA; fun_prop) (k ^ p) (by positivity) (fun ω => by positivity)
      (fun ω => by
        calc ‖A ω‖ ^ p ≤ (k * Wb (X ω)) ^ p := pow_le_pow_left₀ (norm_nonneg _) (hle ω) p
          _ = k ^ p * W (X ω) := by simp only [hWdef]; rw [mul_pow])
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hHval (by positivity)
  obtain ⟨c1, c2, c3⟩ := sd1_alpha_cont (m := m) (n := n) z hspos hzS
  have hUm : Measurable (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hX
  have hVm : Measurable (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hX
  have hDm : Measurable (fun ω => ϖ * resid F.A (X ω)) := (hdm.comp hX).const_mul ϖ
  have hq : Measurable (fun ω => (M0 ω, ϖ * resid F.A (X ω), momU F.C B (X ω), momV F.C B (X ω))) :=
    hM0m.prodMk (hDm.prodMk (hUm.prodMk hVm))
  have e1 : ∀ ω, ageAlphaC1 F S t j M0 ϖ z ω = colAlpha1 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ)) (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have e2 : ∀ ω, ageAlphaC2 F S t j M0 ϖ z ω = colAlpha2 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ)) (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have e3 : ∀ ω, ageAlphaC3 F S t j M0 ϖ z ω = colAlpha3 ((M0 ω).map (fun x : ℝ => (x : ℂ))) ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ)) (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have hA1 : Measurable (ageAlphaC1 F S t j M0 ϖ z) := by
    rw [funext e1]
    have h := sd1_meas_comp _ c1 hq
    exact h
  have hA2 : Measurable (ageAlphaC2 F S t j M0 ϖ z) := by
    rw [funext e2]
    have h := sd1_meas_comp _ c2 hq
    exact h
  have hA3 : Measurable (ageAlphaC3 F S t j M0 ϖ z) := by
    rw [funext e3]
    have h := sd1_meas_comp _ c3 hq
    exact h
  have hpt : ∀ ω, ‖ageAlphaC1 F S t j M0 ϖ z ω‖ ≤ (c' * ϖ) * Wb (X ω) ∧
      ‖ageAlphaC3 F S t j M0 ϖ z ω‖ ≤ (c' * ϖ ^ 2) * Wb (X ω) ∧
      ‖ageAlphaC2 F S t j M0 ϖ z ω‖ ≤ (c' * ϖ ^ 2 / z.re) * Wb (X ω) := by
    intro ω
    have h := hc (M0 ω) (momU F.C B (X ω)) (momV F.C B (X ω)) (resid F.A (X ω)) ϖ z hϖ0 hϖ1 hs hzS
    rw [sd1_sq_eq F (X ω)] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hW0 := hWnn (X ω)
    refine ⟨h1.trans ?_, h3.trans ?_, h2.trans ?_⟩
    ·       calc _ = c * ϖ * Wb (X ω) := by simp only [hWbdef]; ring
        _ ≤ c' * ϖ * Wb (X ω) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc' hϖ0) hW0
    ·       calc _ = c * ϖ ^ 2 * Wb (X ω) := by simp only [hWbdef]; ring
        _ ≤ c' * ϖ ^ 2 * Wb (X ω) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc' (by positivity)) hW0
    ·       calc _ = c * (ϖ ^ 2 / z.re) * Wb (X ω) := by simp only [hWbdef]; ring
        _ ≤ c' * (ϖ ^ 2 / z.re) * Wb (X ω) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcc' (by positivity)) hW0
        _ = _ := by ring
  refine ⟨fun ω => ?_, ?_, ?_, ?_⟩
  · exact (eqn_app_dyn_Rebeta (M0 ω) (ϖ * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω)
      (ageBuf F S t j M0 ϖ ω) z rfl hspos hzS).2
  · obtain ⟨hi, hc⟩ := key _ (c' * ϖ) hA1 (by positivity) (fun ω => (hpt ω).1)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans_eq ?_
    ring
  · obtain ⟨hi, hc⟩ := key _ (c' * ϖ ^ 2) hA3 (by positivity) (fun ω => (hpt ω).2.1)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans_eq ?_
    ring
  · obtain ⟨hi, hc⟩ := key _ (c' * ϖ ^ 2 / z.re) hA2 (by positivity) (fun ω => (hpt ω).2.2)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans_eq ?_
    ring

/-! ## Rank, multiplier and covariance bounds over `𝕊` -/

/-- `lem:app-drift-coeffmoments` at `z ∈ 𝕊`, snapshot `cr-2026-10-23`
(`sections/05-dynamics/section.tex` ll. 849–856):
```latex
By \cref{lem:app-de-moments} the conditional norms
$\norm{\alpha_1}_{p,\mathcal G}$, $x\norm{\alpha_2}_{p,\mathcal G}$ and
$\norm{\alpha_3}_{p,\mathcal G}$ are therefore at most $C_p\varpi$,
$C_p\varpi^2$ and $C_p\varpi^2$ for $x\ge1$, and at most $C_{p,I}\varpi$,
$C_{p,I}\varpi^2$, $C_{p,I}\varpi^2$ for $x\in I$.
```
together with `Re α₂ ≥ 0` (`eqn:app-dyn-Rebeta`). Same shape as the real counterpart
`Muon.Drift.lem_app_drift_coeffmoments` (`Coefficients.lean`:1379), with `s ≥ s₀` replaced by
`z ∈ 𝕊`, `Re z ≥ s₀`, `|·|` by `‖·‖`, `s` by `x = Re z` in the `α₂` bound, and `α₂ ≥ 0` by
`Re α₂ ≥ 0`. `C` depends only on `(p, s₀, C_Σ, γ⋆)` (the source's two regimes are the cases
`s₀ = 1` and `s₀ = min I`). -/
theorem lem_app_drift_coeffmoments_sector (p : ℕ) (hp : 1 ≤ p) (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ : ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        (∀ ω, 0 ≤ (ageAlphaC2 F S t j M0 ϖ z ω).re) ∧
        (Integrable (fun ω => ‖ageAlphaC1 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC1 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ) ^ p) ∧
        (Integrable (fun ω => ‖ageAlphaC3 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC3 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ ^ 2) ^ p) ∧
        (Integrable (fun ω => ‖ageAlphaC2 F S t j M0 ϖ z ω‖ ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => ‖ageAlphaC2 F S t j M0 ϖ z ω'‖ ^ p) ω ≤ (C * ϖ ^ 2 / z.re) ^ p) := by
  exact sd1_main p hp s0 hs0 CS γ hγ

/-! ### Complex matrix norm helpers for `lem_app_drift_multiplier_i_sector` -/

private lemma sd2_opNorm_nonneg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

private lemma sd2_fro_nonneg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) : 0 ≤ fro A :=
  Real.sqrt_nonneg _

private lemma sd2_fro_sq {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) :
    fro A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]

open scoped Matrix.Norms.L2Operator in
private lemma sd2_fro_mul_le_left {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (N : Matrix (Fin q) (Fin r) ℂ) : fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, ‖(M * N) i j‖ ^ 2 ≤ opNorm M ^ 2 * ∑ k, ‖N k j‖ ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℂ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℂ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℂ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℂ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, ‖v.ofLp k‖ ^ 2 = ∑ k, ‖N k j‖ ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [sd2_fro_sq, mul_pow, sd2_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, ‖(M * N) i j‖ ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, ‖N k j‖ ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, ‖N k j‖ ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (sd2_fro_nonneg _) (mul_nonneg (sd2_opNorm_nonneg M)
    (sd2_fro_nonneg N)) two_ne_zero).mp hfro

private lemma sd2_fro_conjTranspose {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) : fro Aᴴ = fro A := by
  unfold fro
  congr 1
  simp only [Matrix.conjTranspose_apply, norm_star]
  exact Finset.sum_comm

open scoped Matrix.Norms.L2Operator in
private lemma sd2_opNorm_conjTranspose {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) :
    opNorm Aᴴ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, Matrix.l2_opNorm_conjTranspose]

private lemma sd2_fro_mul_le_right {p q r : ℕ} (M : Matrix (Fin p) (Fin q) ℂ)
    (N : Matrix (Fin q) (Fin r) ℂ) : fro (M * N) ≤ fro M * opNorm N := by
  have h := sd2_fro_mul_le_left Nᴴ Mᴴ
  rw [← Matrix.conjTranspose_mul, sd2_fro_conjTranspose, sd2_opNorm_conjTranspose,
    sd2_fro_conjTranspose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma sd2_fro_sandwich {p q r t : ℕ} (L : Matrix (Fin p) (Fin q) ℂ)
    (K : Matrix (Fin q) (Fin r) ℂ) (R : Matrix (Fin r) (Fin t) ℂ) :
    fro (L * K * R) ≤ opNorm L * fro K * opNorm R :=
  (sd2_fro_mul_le_right _ _).trans
    (mul_le_mul_of_nonneg_right (sd2_fro_mul_le_left _ _) (sd2_opNorm_nonneg _))

open scoped Matrix.Norms.Frobenius in
private lemma sd2_fro_add {k l : ℕ} (A B' : Matrix (Fin k) (Fin l) ℂ) :
    fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

section SD2B
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

/-! ## Private integrability helpers (copies of private lemmas of `Muon.DetEquiv.Gaussian`) -/

section BfCopies
open Muon.Foundations

private lemma sd2b_gmono {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r)) (stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n, (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold stdGaussianPi
  exact Integrable.fintype_prod (fun i => gaussian_integrable_pow _)

private lemma sd2b_gtwo {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := sd2b_gmono (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma sd2b_gfour {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := sd2b_gmono (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

private lemma sd2b_gfam1_memLp (m n : ℕ) (a : Fin m × Fin n) :
    MemLp (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) 2 (gaussPair m n) := by
  have hm : Measurable (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h := Integrable.mul_prod (sd2b_gtwo a.1 a.1) (sd2b_gtwo a.2 a.2)
  unfold gaussPair
  convert h using 2 with x
  ring

private lemma sd2b_gsq_memLp (d : ℕ) (a : Fin d × Fin d) :
    MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (stdGaussianPi d) := by
  have hm : Measurable (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) := by
    fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  set c : ℝ := (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2
  have e : (fun z : Vec d => (z a.1 * z a.2 - c) ^ 2)
      = fun z => z a.1 * z a.2 * z a.1 * z a.2 - (2 * c) * (z a.1 * z a.2) + c ^ 2 := by
    funext z; ring
  rw [e]
  exact ((sd2b_gfour _ _ _ _).sub ((sd2b_gtwo _ _).const_mul _)).add (integrable_const _)

private lemma sd2b_aem {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {m n : ℕ}
    (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) : AEMeasurable X P := by
  by_contra hne
  have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)
  have hd := hX.symm.trans h0
  obtain ⟨x0, hd⟩ : ∃ x0 : Vec m × Vec n, gaussPair m n = Measure.dirac x0 := ⟨_, hd⟩
  have key : ∀ c : Vec m × Vec n → ℝ, Measurable c →
      (gaussPair m n).map c = gaussianReal 0 1 → False := by
    intro c hc hmap
    have h1 : (gaussPair m n).map c {c x0} = 1 := by
      rw [Measure.map_apply hc (measurableSet_singleton _), hd, Measure.dirac_apply' _
        (hc (measurableSet_singleton _))]
      simp
    rw [hmap] at h1
    have := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [measure_singleton] at h1
    exact zero_ne_one h1
  have hfst : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  have hsnd : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hm; subst hn
      exact hne (measurable_of_subsingleton_codomain X).aemeasurable
    · refine key (fun x => x.2 ⟨0, hn⟩) ((measurable_pi_apply _).comp measurable_snd) ?_
      have := Muon.Foundations.stdGaussianPi_map_coord n ⟨0, hn⟩
      rw [← this, ← hsnd, Measure.map_map (measurable_pi_apply _) measurable_snd]
      rfl
  · refine key (fun x => x.1 ⟨0, hm⟩) ((measurable_pi_apply _).comp measurable_fst) ?_
    have := Muon.Foundations.stdGaussianPi_map_coord m ⟨0, hm⟩
    rw [← this, ← hfst, Measure.map_map (measurable_pi_apply _) measurable_fst]
    rfl

private lemma sd2b_sq_memLp {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {m n d : ℕ}
    (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d) (a : Fin d × Fin d) :
    MemLp (fun w => (π (X w)) a.1 * (π (X w)) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 P := by
  have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (Measure.map π (gaussPair m n)) := by rw [hmap]; exact sd2b_gsq_memLp d a
  have h2 := h1.comp_of_map hπ.aemeasurable
  have hg : MemLp (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 (@Measure.map Ω' (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact h2
  exact hg.comp_of_map (sd2b_aem P X hX)

end BfCopies

private lemma sd2b_memLp_sq_fst {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin m) :
    MemLp (fun ω => (X ω).1 a * (X ω).1 b - (1 : Mat m m) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  exact sd2b_sq_memLp P X hX Prod.fst measurable_fst hmap (a, b)

private lemma sd2b_memLp_sq_snd {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin n) :
    MemLp (fun ω => (X ω).2 a * (X ω).2 b - (1 : Mat n n) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  exact sd2b_sq_memLp P X hX Prod.snd measurable_snd hmap (a, b)

private lemma sd2b_memLp_cross {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => (X ω).1 a * (X ω).2 b) 2 P := by
  have hg : MemLp (fun x : Vec m × Vec n => x.1 a * x.2 b) 2
      (@Measure.map Ω' (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact sd2b_gfam1_memLp m n (a, b)
  exact hg.comp_of_map (sd2b_aem P X hX)

private lemma sd2b_integrable_mul {f g : Ω' → ℝ} {P : Measure Ω'} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg


end SD2B

private lemma sd2_fro_nonneg_real {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

section SD2D
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

/-- Complexification of a real conditional Frobenius bound via real and imaginary parts. -/
private lemma sd2_cplx_bound {k l : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω') (A : Ω' → Mat k l) (K : ℝ) (hK : 0 ≤ K) (e : Ω' → ℂ)
    (he : MemLp e 2 P)
    (hI : ∀ a b, Integrable (fun ω => (e ω).re * A ω a b) P)
    (hJ : ∀ a b, Integrable (fun ω => (e ω).im * A ω a b) P)
    (hR : ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P (fun ω => (e ω).re • A ω) ζ) ≤
        K * Real.sqrt (condExp G P (fun ω => (e ω).re ^ 2) ζ))
    (hM : ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P (fun ω => (e ω).im • A ω) ζ) ≤
        K * Real.sqrt (condExp G P (fun ω => (e ω).im ^ 2) ζ)) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω => e ω • (A ω).map (fun x : ℝ => (x : ℂ))) ζ) ≤
        K * Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ) := by
  have hf : ∀ a b, Integrable (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) P := by
    intro a b
    have h1 := (hI a b).ofReal (𝕜 := ℂ)
    have h2 := (hJ a b).ofReal (𝕜 := ℂ)
    refine (h1.add (h2.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun ω => ?_)
    apply Complex.ext <;> simp
  have hre : ∀ a b, ∀ᵐ ζ ∂P, (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).re =
      condExp G P (fun ω => (e ω).re * A ω a b) ζ := by
    intro a b
    have h1 := Complex.reCLM.comp_condExp_comm (m := G) (hf a b)
    have h2 : condExp G P (fun ω => (e ω * ((A ω a b : ℝ) : ℂ)).re) =ᵐ[P]
        condExp G P (fun ω => (e ω).re * A ω a b) :=
      condExp_congr_ae (Filter.Eventually.of_forall fun ω => by simp)
    filter_upwards [h1, h2] with ζ hζ hζ2
    have h' : (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).re =
        condExp G P (fun ω => (e ω * ((A ω a b : ℝ) : ℂ)).re) ζ := hζ
    rw [h', hζ2]
  have him : ∀ a b, ∀ᵐ ζ ∂P, (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).im =
      condExp G P (fun ω => (e ω).im * A ω a b) ζ := by
    intro a b
    have h1 := Complex.imCLM.comp_condExp_comm (m := G) (hf a b)
    have h2 : condExp G P (fun ω => (e ω * ((A ω a b : ℝ) : ℂ)).im) =ᵐ[P]
        condExp G P (fun ω => (e ω).im * A ω a b) :=
      condExp_congr_ae (Filter.Eventually.of_forall fun ω => by simp)
    filter_upwards [h1, h2] with ζ hζ hζ2
    have h' : (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).im =
        condExp G P (fun ω => (e ω * ((A ω a b : ℝ) : ℂ)).im) ζ := hζ
    rw [h', hζ2]
  have hre2 : Integrable (fun ω => (e ω).re ^ 2) P := (he.re).integrable_sq
  have him2 : Integrable (fun ω => (e ω).im ^ 2) P := (he.im).integrable_sq
  have hsum : condExp G P (fun ω => ‖e ω‖ ^ 2) =ᵐ[P]
      fun ζ => condExp G P (fun ω => (e ω).re ^ 2) ζ + condExp G P (fun ω => (e ω).im ^ 2) ζ := by
    have h1 := condExp_add hre2 him2 G
    refine (condExp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans h1
    simp only [Complex.sq_norm, Complex.normSq_apply, Pi.add_apply]
    ring
  have hn1 : 0 ≤ᵐ[P] condExp G P (fun ω => (e ω).re ^ 2) :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hn2 : 0 ≤ᵐ[P] condExp G P (fun ω => (e ω).im ^ 2) :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  have hall : ∀ᵐ ζ ∂P, ∀ a b, (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).re =
        condExp G P (fun ω => (e ω).re * A ω a b) ζ ∧
      (condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ).im =
        condExp G P (fun ω => (e ω).im * A ω a b) ζ :=
    ae_all_iff.2 fun a => ae_all_iff.2 fun b => by
      filter_upwards [hre a b, him a b] with ζ h1 h2 using ⟨h1, h2⟩
  filter_upwards [hall, hR, hM, hsum, hn1, hn2] with ζ hall hR hM hsum hn1 hn2
  have hsq : fro (condExpMatC G P (fun ω => e ω • (A ω).map (fun x : ℝ => (x : ℂ))) ζ) ^ 2 =
      fro (Muon.Foundations.condExpMat G P (fun ω => (e ω).re • A ω) ζ) ^ 2 +
      fro (Muon.Foundations.condExpMat G P (fun ω => (e ω).im • A ω) ζ) ^ 2 := by
    unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity),
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    obtain ⟨h1, h2⟩ := hall a b
    have e1 : condExpMatC G P (fun ω => e ω • (A ω).map (fun x : ℝ => (x : ℂ))) ζ a b =
        condExp G P (fun ω => e ω * ((A ω a b : ℝ) : ℂ)) ζ := rfl
    have e2 : Muon.Foundations.condExpMat G P (fun ω => (e ω).re • A ω) ζ a b =
        condExp G P (fun ω => (e ω).re * A ω a b) ζ := rfl
    have e3 : Muon.Foundations.condExpMat G P (fun ω => (e ω).im • A ω) ζ a b =
        condExp G P (fun ω => (e ω).im * A ω a b) ζ := rfl
    rw [e1, e2, e3, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, ← h1, ← h2,
      Complex.sq_norm, Complex.normSq_apply]
    ring
  have hA1 := sd2_fro_nonneg_real (Muon.Foundations.condExpMat G P (fun ω => (e ω).re • A ω) ζ)
  have hA2 := sd2_fro_nonneg_real (Muon.Foundations.condExpMat G P (fun ω => (e ω).im • A ω) ζ)
  have hC0 := sd2_fro_nonneg (condExpMatC G P (fun ω => e ω • (A ω).map (fun x : ℝ => (x : ℂ))) ζ)
  rw [hsum]
  have hs1 : Real.sqrt (condExp G P (fun ω => (e ω).re ^ 2) ζ) ^ 2 =
      condExp G P (fun ω => (e ω).re ^ 2) ζ := Real.sq_sqrt hn1
  have hs2 : Real.sqrt (condExp G P (fun ω => (e ω).im ^ 2) ζ) ^ 2 =
      condExp G P (fun ω => (e ω).im ^ 2) ζ := Real.sq_sqrt hn2
  have hs3 : Real.sqrt (condExp G P (fun ω => (e ω).re ^ 2) ζ +
      condExp G P (fun ω => (e ω).im ^ 2) ζ) ^ 2 =
      condExp G P (fun ω => (e ω).re ^ 2) ζ + condExp G P (fun ω => (e ω).im ^ 2) ζ :=
    Real.sq_sqrt (add_nonneg hn1 hn2)
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [hsq, mul_pow, hs3]
  have p1 := pow_le_pow_left₀ hA1 hR 2
  have p2 := pow_le_pow_left₀ hA2 hM 2
  rw [mul_pow, hs1] at p1
  rw [mul_pow, hs2] at p2
  nlinarith

end SD2D

section SD2E
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

/-- Vector-form integrability: `e (u_a v_b)` is integrable when `u = c R x`, `v = c' S y`. -/
private lemma sd2_int_outer {d d' : ℕ} (P : Measure Ω') (x : Ω' → Vec d) (y : Ω' → Vec d')
    (R : Mat d d) (S : Mat d' d') (c c' : ℝ) (u : Ω' → Vec d) (v : Ω' → Vec d') (e : Ω' → ℝ)
    (hu : ∀ ω, u ω = c • (R *ᵥ x ω)) (hv : ∀ ω, v ω = c' • (S *ᵥ y ω))
    (hxy : ∀ p q, Integrable (fun ω => x ω p * y ω q * e ω) P) (a : Fin d) (b : Fin d') :
    Integrable (fun ω => e ω * (u ω a * v ω b)) P := by
  have h : (fun ω => e ω * (u ω a * v ω b)) = fun ω =>
      ∑ p : Fin d, ∑ q : Fin d', (c * c' * (R a p * S b q)) * (x ω p * y ω q * e ω) := by
    funext ω
    rw [hu, hv]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [h]
  exact integrable_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ => (hxy p q).const_mul _

private lemma sd2_iuu {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω' → ℝ) (he : MemLp e 2 P)
    (p q : Fin m) : Integrable (fun ω => (X ω).1 p * (X ω).1 q * e ω) P := by
  have hI : Integrable e P := he.integrable one_le_two
  have := (sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_fst (mΩ := mΩ) P X hX p q) he).add
    (hI.const_mul ((1 : Mat m m) p q))
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

private lemma sd2_ivv {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω' → ℝ) (he : MemLp e 2 P)
    (p q : Fin n) : Integrable (fun ω => (X ω).2 p * (X ω).2 q * e ω) P := by
  have hI : Integrable e P := he.integrable one_le_two
  have := (sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_snd (mΩ := mΩ) P X hX p q) he).add
    (hI.const_mul ((1 : Mat n n) p q))
  refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

private lemma sd2_iuv {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω' → ℝ) (he : MemLp e 2 P)
    (p : Fin m) (q : Fin n) : Integrable (fun ω => (X ω).1 p * (X ω).2 q * e ω) P :=
  sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_cross (mΩ := mΩ) P X hX p q) he

private lemma sd2_ivu {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω' → ℝ) (he : MemLp e 2 P)
    (p : Fin n) (q : Fin m) : Integrable (fun ω => (X ω).2 p * (X ω).1 q * e ω) P := by
  have := sd2_iuv P X hX e he q p
  simpa only [mul_comm ((X _).2 p)] using this

/-- Integrability of the four real rank-one entries against an `L²` scalar. -/
private lemma sd2_int_uu {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℝ) (he : MemLp e 2 P) (a b : Fin m) :
    Integrable (fun ω => e ω * (momU C B (X ω) a * momU C B (X ω) b)) P :=
  sd2_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).1) (rOut C) (rOut C) _ _
    (fun ω => momU C B (X ω)) (fun ω => momU C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (sd2_iuu P X hX e he) a b

private lemma sd2_int_uv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℝ) (he : MemLp e 2 P) (a : Fin m) (b : Fin n) :
    Integrable (fun ω => e ω * (momU C B (X ω) a * momV C B (X ω) b)) P :=
  sd2_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).2) (rOut C) (rIn C) _ _
    (fun ω => momU C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (sd2_iuv P X hX e he) a b

private lemma sd2_int_vu {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℝ) (he : MemLp e 2 P) (a : Fin n) (b : Fin m) :
    Integrable (fun ω => e ω * (momV C B (X ω) a * momU C B (X ω) b)) P :=
  sd2_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).1) (rIn C) (rOut C) _ _
    (fun ω => momV C B (X ω)) (fun ω => momU C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (sd2_ivu P X hX e he) a b

private lemma sd2_int_vv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℝ) (he : MemLp e 2 P) (a b : Fin n) :
    Integrable (fun ω => e ω * (momV C B (X ω) a * momV C B (X ω) b)) P :=
  sd2_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).2) (rIn C) (rIn C) _ _
    (fun ω => momV C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (sd2_ivv P X hX e he) a b

end SD2E

private lemma sd2_opNorm_nonneg_real {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

section SD2F
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd2_bessel_uu {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (CS γ : ℝ) (hB : 0 < B) (hS : opNorm C.Sout ≤ CS)
    (hdim : (m : ℝ) ≤ γ * B)
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω')
    (hG : G ≤ mΩ) (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω' → ℂ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω' => e ω' •
        (Muon.outer (momU C B (X ω')) (momU C B (X ω'))).map (fun x : ℝ => (x : ℂ))) ζ) ≤
      CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hS
  refine sd2_cplx_bound (mΩ := mΩ) P G _ _ (by positivity) e he2
    (fun a b => sd2_int_uu (mΩ := mΩ) P C X hX _ he2.re a b) (fun a b => sd2_int_uu (mΩ := mΩ) P C X hX _ he2.im a b)
    (bessel_frob_uu (mΩ := mΩ) P C CS γ hB hS hdim X hX G hG hind (fun ω => (e ω).re)
      (Complex.measurable_re.comp he) he2.re)
    (bessel_frob_uu (mΩ := mΩ) P C CS γ hB hS hdim X hX G hG hind (fun ω => (e ω).im)
      (Complex.measurable_im.comp he) he2.im)

private lemma sd2_bessel_vv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (CS γ : ℝ) (hB : 0 < B) (hS : opNorm C.Sin ≤ CS)
    (hdim : (n : ℝ) ≤ γ * B)
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω')
    (hG : G ≤ mΩ) (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω' → ℂ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω' => e ω' •
        (Muon.outer (momV C B (X ω')) (momV C B (X ω'))).map (fun x : ℝ => (x : ℂ))) ζ) ≤
      CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hS
  refine sd2_cplx_bound (mΩ := mΩ) P G _ _ (by positivity) e he2
    (fun a b => sd2_int_vv (mΩ := mΩ) P C X hX _ he2.re a b) (fun a b => sd2_int_vv (mΩ := mΩ) P C X hX _ he2.im a b)
    (bessel_frob_vv (mΩ := mΩ) P C CS γ hB hS hdim X hX G hG hind (fun ω => (e ω).re)
      (Complex.measurable_re.comp he) he2.re)
    (bessel_frob_vv (mΩ := mΩ) P C CS γ hB hS hdim X hX G hG hind (fun ω => (e ω).im)
      (Complex.measurable_im.comp he) he2.im)

private lemma sd2_bessel_uv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (CS : ℝ) (hB : 0 < B) (hSo : opNorm C.Sout ≤ CS)
    (hSi : opNorm C.Sin ≤ CS)
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω')
    (hG : G ≤ mΩ) (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω' → ℂ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω' => e ω' •
        (Muon.outer (momU C B (X ω')) (momV C B (X ω'))).map (fun x : ℝ => (x : ℂ))) ζ) ≤
      CS / B * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) ∧
    fro (condExpMatC G P (fun ω' => e ω' •
        (Muon.outer (momV C B (X ω')) (momU C B (X ω'))).map (fun x : ℝ => (x : ℂ))) ζ) ≤
      CS / B * Real.sqrt (condExp G P (fun ω' => ‖e ω'‖ ^ 2) ζ) := by
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hSo
  have hr := bessel_frob_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind (fun ω => (e ω).re)
    (Complex.measurable_re.comp he) he2.re
  have hi := bessel_frob_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind (fun ω => (e ω).im)
    (Complex.measurable_im.comp he) he2.im
  have h1 := sd2_cplx_bound (mΩ := mΩ) P G (fun ω' => Muon.outer (momU C B (X ω')) (momV C B (X ω')))
    (CS / B) (by positivity) e he2
    (fun a b => sd2_int_uv (mΩ := mΩ) P C X hX _ he2.re a b) (fun a b => sd2_int_uv (mΩ := mΩ) P C X hX _ he2.im a b)
    (by filter_upwards [hr] with ζ h using h.1) (by filter_upwards [hi] with ζ h using h.1)
  have h2 := sd2_cplx_bound (mΩ := mΩ) P G (fun ω' => Muon.outer (momV C B (X ω')) (momU C B (X ω')))
    (CS / B) (by positivity) e he2
    (fun a b => sd2_int_vu (mΩ := mΩ) P C X hX _ he2.re a b) (fun a b => sd2_int_vu (mΩ := mΩ) P C X hX _ he2.im a b)
    (by filter_upwards [hr] with ζ h using h.2) (by filter_upwards [hi] with ζ h using h.2)
  filter_upwards [h1, h2] with ζ a b using ⟨a, b⟩

end SD2F


section SD2
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd2_mul3_apply {p q r t : ℕ} (A : Matrix (Fin p) (Fin q) ℂ)
    (B : Matrix (Fin q) (Fin r) ℂ) (C : Matrix (Fin r) (Fin t) ℂ) (i : Fin p) (j : Fin t) :
    (A * B * C) i j = ∑ x : Fin q × Fin r, (A i x.1 * C x.2 j) * B x.1 x.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Entrywise pull-out of bounded `𝒢`-measurable complex matrix factors from `condExpMatC`. -/
private lemma sd2_condExpMat_pull {p q r t : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω') (hG : G ≤ mΩ) (L : Ω' → Matrix (Fin p) (Fin q) ℂ)
    (R : Ω' → Matrix (Fin r) (Fin t) ℂ)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, ‖L ω i j‖ ≤ cL) (hRb : ∀ ω i j, ‖R ω i j‖ ≤ cR)
    (F : Ω' → Matrix (Fin q) (Fin r) ℂ) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) :
    ∀ᵐ ζ ∂P, condExpMatC G P (fun ω => L ω * F ω * R ω) ζ =
      L ζ * condExpMatC G P F ζ * R ζ := by
  have hint : ∀ i j (x : Fin q × Fin r),
      Integrable (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) P := by
    intro i j x
    refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
      (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [norm_mul]
    exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (norm_nonneg _) hcL
  have hterm : ∀ i j (x : Fin q × Fin r), ∀ᵐ ζ ∂P,
      condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
        (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ := by
    intro i j x
    have hfm : Measurable[G] (fun ω => L ω i x.1 * R ω x.2 j) := (hL i x.1).mul (hR x.2 j)
    have := condExp_bilin_of_stronglyMeasurable_left (m := G) (μ := P)
      (ContinuousLinearMap.mul ℝ ℂ)
      (f := fun ω => L ω i x.1 * R ω x.2 j) (g := fun ω => F ω x.1 x.2)
      hfm.stronglyMeasurable (by simpa using hint i j x) (hF x.1 x.2)
    filter_upwards [this] with ζ hζ
    simpa using hζ
  have hentry : ∀ i j, ∀ᵐ ζ ∂P,
      condExpMatC G P (fun ω => L ω * F ω * R ω) ζ i j =
        (L ζ * condExpMatC G P F ζ * R ζ) i j := by
    intro i j
    have h1 : condExp G P (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2)
        =ᵐ[P] ∑ x : Fin q × Fin r,
          condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
      have e : (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) =
          ∑ x : Fin q × Fin r, (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
        funext ω; simp [Finset.sum_apply]
      rw [e]
      exact condExp_finsetSum (fun x _ => hint i j x) G
    have h2 : ∀ᵐ ζ ∂P, ∀ x : Fin q × Fin r,
        condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
          (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ :=
      ae_all_iff.2 fun x => hterm i j x
    filter_upwards [h1, h2] with ζ h1ζ h2ζ
    have e2 : (fun ω => (L ω * F ω * R ω) i j) =
        fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
      funext fun ω => sd2_mul3_apply _ _ _ _ _
    show condExp G P (fun ω' => (L ω' * F ω' * R ω') i j) ζ = _
    rw [e2, h1ζ, Finset.sum_apply, sd2_mul3_apply]
    exact Finset.sum_congr rfl fun x _ => h2ζ x
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Entries of `L * F * R` are integrable under bounded `𝒢`-measurable factors. -/
private lemma sd2_int_LFR {p q r t : ℕ} (P : Measure Ω') (G : MeasurableSpace Ω') (hG : G ≤ mΩ)
    (L : Ω' → Matrix (Fin p) (Fin q) ℂ) (R : Ω' → Matrix (Fin r) (Fin t) ℂ) (cL cR : ℝ)
    (hcL : 0 ≤ cL)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, ‖L ω i j‖ ≤ cL) (hRb : ∀ ω i j, ‖R ω i j‖ ≤ cR)
    (F : Ω' → Matrix (Fin q) (Fin r) ℂ) (hF : ∀ k l, Integrable (fun ω => F ω k l) P)
    (i : Fin p) (j : Fin t) :
    Integrable (fun ω => (L ω * F ω * R ω) i j) P := by
  have e : (fun ω => (L ω * F ω * R ω) i j) =
      fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
    funext fun ω => sd2_mul3_apply _ _ _ _ _
  rw [e]
  refine integrable_finset_sum _ fun x _ => ?_
  refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
    (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (norm_nonneg _) hcL

/-- Entrywise additivity of `condExpMatC`. -/
private lemma sd2_condExpMat_add {p q : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω') (A B' : Ω' → Matrix (Fin p) (Fin q) ℂ)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) P) (hB : ∀ i j, Integrable (fun ω => B' ω i j) P) :
    ∀ᵐ ζ ∂P, condExpMatC G P (fun ω => A ω + B' ω) ζ =
      condExpMatC G P A ζ + condExpMatC G P B' ζ := by
  have hent : ∀ i j, ∀ᵐ ζ ∂P, condExpMatC G P (fun ω => A ω + B' ω) ζ i j =
      (condExpMatC G P A ζ + condExpMatC G P B' ζ) i j := by
    intro i j
    have h := condExp_add (hA i j) (hB i j) G
    filter_upwards [h] with ζ hζ
    exact hζ
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hent i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Frobenius bound for a pulled-out sandwich `L (condExp F) R` under a bound on `F`. -/
private lemma sd2_term {p q r t : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω') (hG : G ≤ mΩ) (L : Ω' → Matrix (Fin p) (Fin q) ℂ)
    (R : Ω' → Matrix (Fin r) (Fin t) ℂ)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, ‖L ω i j‖ ≤ cL) (hRb : ∀ ω i j, ‖R ω i j‖ ≤ cR)
    (F : Ω' → Matrix (Fin q) (Fin r) ℂ) (hF : ∀ k l, Integrable (fun ω => F ω k l) P)
    (aL aR K : ℝ) (haL0 : 0 ≤ aL) (haR0 : 0 ≤ aR) (hK0 : 0 ≤ K)
    (haL : ∀ ζ, opNorm (L ζ) ≤ aL) (haR : ∀ ζ, opNorm (R ζ) ≤ aR)
    (hK : ∀ᵐ ζ ∂P, fro (condExpMatC G P F ζ) ≤ K) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω => L ω * F ω * R ω) ζ) ≤ aL * K * aR := by
  filter_upwards [sd2_condExpMat_pull (mΩ := mΩ) P G hG L R cL cR hcL hcR hL hR hLb hRb F hF, hK]
    with ζ h1 h2
  rw [h1]
  refine (sd2_fro_sandwich _ _ _).trans ?_
  exact mul_le_mul (mul_le_mul (haL ζ) h2 (sd2_fro_nonneg _) haL0) (haR ζ) (sd2_opNorm_nonneg _)
    (mul_nonneg haL0 hK0)

end SD2

section SD2G
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd2_int_cplx_mul (P : Measure Ω') (e : Ω' → ℂ) (f : Ω' → ℝ)
    (hI : Integrable (fun ω => (e ω).re * f ω) P) (hJ : Integrable (fun ω => (e ω).im * f ω) P) :
    Integrable (fun ω => e ω * ((f ω : ℝ) : ℂ)) P := by
  have h1 := hI.ofReal (𝕜 := ℂ)
  have h2 := hJ.ofReal (𝕜 := ℂ)
  refine (h1.add (h2.const_mul Complex.I)).congr (Filter.Eventually.of_forall fun ω => ?_)
  apply Complex.ext <;> simp

private lemma sd2_entry_le {p q : ℕ} (K : Matrix (Fin p) (Fin q) ℂ) (i : Fin p) (j : Fin q) :
    ‖K i j‖ ≤ opNorm K := sd0_entry_le K i j

/-- Four-term conditional Frobenius bound, complex version of `cm_four`. -/
private lemma sd2_four {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P] (C : Covariances m n)
    (CS γ : ℝ) (hB : 0 < B) (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω')
    (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (R0 : Ω' → Matrix (Fin m) (Fin m) ℂ) (Rt0 : Ω' → Matrix (Fin n) (Fin n) ℂ)
    (X0 : Ω' → Matrix (Fin m) (Fin n) ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR0m : ∀ i j, Measurable[G] (fun ω => R0 ω i j))
    (hRt0m : ∀ i j, Measurable[G] (fun ω => Rt0 ω i j))
    (hX0m : ∀ i j, Measurable[G] (fun ω => X0 ω i j))
    (hR0 : ∀ ω, opNorm (R0 ω) ≤ a) (hRt0 : ∀ ω, opNorm (Rt0 ω) ≤ a)
    (hX00 : ∀ ω, opNorm (X0 ω) ≤ b)
    (e1 e2 e3 e4 : Ω' → ℂ)
    (he1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e1)
    (he2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e2)
    (he3 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e3)
    (he4 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e4)
    (hl1 : MemLp e1 2 P) (hl2 : MemLp e2 2 P) (hl3 : MemLp e3 2 P) (hl4 : MemLp e4 2 P)
    (κ1 κ2 κ3 κ4 : ℝ) (hκ1 : 0 ≤ κ1) (hκ2 : 0 ≤ κ2) (hκ3 : 0 ≤ κ3) (hκ4 : 0 ≤ κ4)
    (hk1 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => ‖e1 ω‖ ^ 2) ζ) ≤ κ1)
    (hk2 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => ‖e2 ω‖ ^ 2) ζ) ≤ κ2)
    (hk3 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => ‖e3 ω‖ ^ 2) ζ) ≤ κ3)
    (hk4 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => ‖e4 ω‖ ^ 2) ζ) ≤ κ4) :
    ∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω =>
        R0 ω * (e1 ω • (Muon.outer (momU C B (X ω)) (momU C B (X ω))).map
          (fun x : ℝ => (x : ℂ))) * X0 ω
        + R0 ω * (e2 ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
          (fun x : ℝ => (x : ℂ))) * Rt0 ω
        + X0 ω * (e3 ω • (Muon.outer (momV C B (X ω)) (momU C B (X ω))).map
          (fun x : ℝ => (x : ℂ))) * X0 ω
        + X0 ω * (e4 ω • (Muon.outer (momV C B (X ω)) (momV C B (X ω))).map
          (fun x : ℝ => (x : ℂ))) * Rt0 ω) ζ) ≤
      a * (CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * κ1) * b + a * (CS / B * κ2) * a
        + b * (CS / B * κ3) * b + b * (CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * κ4) * a := by
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hSo
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hKuu : 0 ≤ CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B := by positivity
  have hKuv : 0 ≤ CS / B := by positivity
  have hent : ∀ {d d' : ℕ} (e : Ω' → ℂ) (u : Ω' → Vec d) (v : Ω' → Vec d') (k : Fin d)
      (l : Fin d'),
      (fun ω => (e ω • (Muon.outer (u ω) (v ω)).map (fun x : ℝ => (x : ℂ))) k l) =
        fun ω => e ω * (((u ω k * v ω l : ℝ)) : ℂ) := by
    intro d d' e u v k l; funext ω; simp [Muon.outer, Matrix.vecMulVec_apply]
  have F1 : ∀ k l, Integrable (fun ω => (e1 ω • (Muon.outer (momU C B (X ω))
      (momU C B (X ω))).map (fun x : ℝ => (x : ℂ))) k l) P := by
    intro k l; rw [hent]
    exact sd2_int_cplx_mul (mΩ := mΩ) P e1 (fun ω => momU C B (X ω) k * momU C B (X ω) l)
      (sd2_int_uu (mΩ := mΩ) P C X hX _ hl1.re k l) (sd2_int_uu (mΩ := mΩ) P C X hX _ hl1.im k l)
  have F2 : ∀ k l, Integrable (fun ω => (e2 ω • (Muon.outer (momU C B (X ω))
      (momV C B (X ω))).map (fun x : ℝ => (x : ℂ))) k l) P := by
    intro k l; rw [hent]
    exact sd2_int_cplx_mul (mΩ := mΩ) P e2 (fun ω => momU C B (X ω) k * momV C B (X ω) l)
      (sd2_int_uv (mΩ := mΩ) P C X hX _ hl2.re k l) (sd2_int_uv (mΩ := mΩ) P C X hX _ hl2.im k l)
  have F3 : ∀ k l, Integrable (fun ω => (e3 ω • (Muon.outer (momV C B (X ω))
      (momU C B (X ω))).map (fun x : ℝ => (x : ℂ))) k l) P := by
    intro k l; rw [hent]
    exact sd2_int_cplx_mul (mΩ := mΩ) P e3 (fun ω => momV C B (X ω) k * momU C B (X ω) l)
      (sd2_int_vu (mΩ := mΩ) P C X hX _ hl3.re k l) (sd2_int_vu (mΩ := mΩ) P C X hX _ hl3.im k l)
  have F4 : ∀ k l, Integrable (fun ω => (e4 ω • (Muon.outer (momV C B (X ω))
      (momV C B (X ω))).map (fun x : ℝ => (x : ℂ))) k l) P := by
    intro k l; rw [hent]
    exact sd2_int_cplx_mul (mΩ := mΩ) P e4 (fun ω => momV C B (X ω) k * momV C B (X ω) l)
      (sd2_int_vv (mΩ := mΩ) P C X hX _ hl4.re k l) (sd2_int_vv (mΩ := mΩ) P C X hX _ hl4.im k l)
  have eb : ∀ {d d' : ℕ} (L : Ω' → Matrix (Fin d) (Fin d') ℂ) (c : ℝ) (h : ∀ ω, opNorm (L ω) ≤ c)
      ω i j, ‖L ω i j‖ ≤ c := fun L c h ω i j => (sd2_entry_le _ _ _).trans (h ω)
  -- Bessel bounds
  have B1 := sd2_bessel_uu (mΩ := mΩ) P C CS γ hB hSo hm X hX G hG hind e1 he1 hl1
  have B4 := sd2_bessel_vv (mΩ := mΩ) P C CS γ hB hSi hn X hX G hG hind e4 he4 hl4
  have B2 := sd2_bessel_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind e2 he2 hl2
  have B3 := sd2_bessel_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind e3 he3 hl3
  have hLI : ∀ {p q r t : ℕ} (L : Ω' → Matrix (Fin p) (Fin q) ℂ)
      (R : Ω' → Matrix (Fin r) (Fin t) ℂ) (cL cR : ℝ) (hcL : 0 ≤ cL)
      (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
      (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
      (hLb : ∀ ω i j, ‖L ω i j‖ ≤ cL) (hRb : ∀ ω i j, ‖R ω i j‖ ≤ cR)
      (F : Ω' → Matrix (Fin q) (Fin r) ℂ)
      (hF : ∀ k l, Integrable (fun ω => F ω k l) P) (i : Fin p) (j : Fin t),
      Integrable (fun ω => (L ω * F ω * R ω) i j) P :=
    fun L R cL cR hcL hL hR hLb hRb F hF i j =>
      sd2_int_LFR (mΩ := mΩ) P G hG L R cL cR hcL hL hR hLb hRb F hF i j
  have A1 := hLI R0 X0 a b ha hR0m hX0m (eb R0 a hR0) (eb X0 b hX00)
    (fun ω => e1 ω • (Muon.outer (momU C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) F1
  have A2 := hLI R0 Rt0 a a ha hR0m hRt0m (eb R0 a hR0) (eb Rt0 a hRt0)
    (fun ω => e2 ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) F2
  have A3 := hLI X0 X0 b b hb hX0m hX0m (eb X0 b hX00) (eb X0 b hX00)
    (fun ω => e3 ω • (Muon.outer (momV C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) F3
  have A4 := hLI X0 Rt0 b a hb hX0m hRt0m (eb X0 b hX00) (eb Rt0 a hRt0)
    (fun ω => e4 ω • (Muon.outer (momV C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) F4
  have S12 := sd2_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • (Muon.outer (momU C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * X0 ω)
    (fun ω => R0 ω * (e2 ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * Rt0 ω) A1 A2
  have S123 := sd2_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • (Muon.outer (momU C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * X0 ω
      + R0 ω * (e2 ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * Rt0 ω)
    (fun ω => X0 ω * (e3 ω • (Muon.outer (momV C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * X0 ω)
    (fun i j => (A1 i j).add (A2 i j)) A3
  have S1234 := sd2_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • (Muon.outer (momU C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * X0 ω
      + R0 ω * (e2 ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * Rt0 ω
      + X0 ω * (e3 ω • (Muon.outer (momV C B (X ω)) (momU C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * X0 ω)
    (fun ω => X0 ω * (e4 ω • (Muon.outer (momV C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) * Rt0 ω)
    (fun i j => ((A1 i j).add (A2 i j)).add (A3 i j)) A4
  have T1 := sd2_term (mΩ := mΩ) P G hG R0 X0 a b ha hb hR0m hX0m (eb R0 a hR0) (eb X0 b hX00)
    _ F1 a b _ ha hb (mul_nonneg hKuu hκ1) hR0 hX00
    (by filter_upwards [B1, hk1] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hKuu))
  have T2 := sd2_term (mΩ := mΩ) P G hG R0 Rt0 a a ha ha hR0m hRt0m (eb R0 a hR0) (eb Rt0 a hRt0)
    _ F2 a a _ ha ha (mul_nonneg hKuv hκ2) hR0 hRt0
    (by filter_upwards [B2, hk2] with ζ h1 h2
        exact h1.1.trans (mul_le_mul_of_nonneg_left h2 hKuv))
  have T3 := sd2_term (mΩ := mΩ) P G hG X0 X0 b b hb hb hX0m hX0m (eb X0 b hX00) (eb X0 b hX00)
    _ F3 b b _ hb hb (mul_nonneg hKuv hκ3) hX00 hX00
    (by filter_upwards [B3, hk3] with ζ h1 h2
        exact h1.2.trans (mul_le_mul_of_nonneg_left h2 hKuv))
  have T4 := sd2_term (mΩ := mΩ) P G hG X0 Rt0 b a hb ha hX0m hRt0m (eb X0 b hX00) (eb Rt0 a hRt0)
    _ F4 b a _ hb ha (mul_nonneg hKuu hκ4) hX00 hRt0
    (by filter_upwards [B4, hk4] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hKuu))
  filter_upwards [S12, S123, S1234, T1, T2, T3, T4] with ζ s12 s123 s1234 t1 t2 t3 t4
  rw [s1234, s123, s12]
  refine (sd2_fro_add _ _).trans ?_
  refine add_le_add ((sd2_fro_add _ _).trans (add_le_add ((sd2_fro_add _ _).trans
    (add_le_add t1 t2)) t3)) t4

end SD2G

section SD2H
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

/-- Conditional second moment of `e` from a pointwise bound `‖e‖ ≤ D ‖a‖` (complex version of
`cm_cond_sq`). -/
private lemma sd2_cond_sq (P : Measure Ω') [IsProbabilityMeasure P] (G : MeasurableSpace Ω')
    (e a : Ω' → ℂ) (D K : ℝ) (hD : 0 ≤ D) (hK0 : 0 ≤ K) (he : Measurable[mΩ] e)
    (hea : ∀ ω, ‖e ω‖ ≤ D * ‖a ω‖) (ha2 : Integrable (fun ω => ‖a ω‖ ^ 2) P)
    (hK : ∀ᵐ ω ∂P, condExp G P (fun ω' => ‖a ω'‖ ^ 2) ω ≤ K ^ 2) :
    ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ) ≤ D * K := by
  have hem : Measurable[mΩ] (fun ω => ‖e ω‖ ^ 2) :=
    ((continuous_norm.pow 2).measurable).comp he
  have hle : ∀ ω, ‖e ω‖ ^ 2 ≤ D ^ 2 * ‖a ω‖ ^ 2 := fun ω => by
    have := pow_le_pow_left₀ (norm_nonneg _) (hea ω) 2
    linarith [this, show (D * ‖a ω‖) ^ 2 = D ^ 2 * ‖a ω‖ ^ 2 by ring]
  have hg : Integrable (fun ω => D ^ 2 * ‖a ω‖ ^ 2) P := ha2.const_mul (D ^ 2)
  have hI : Integrable (fun ω => ‖e ω‖ ^ 2) P := by
    refine Integrable.mono' hg (Measurable.aestronglyMeasurable (m := mΩ) hem)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle ω
  have hc := condExp_mono (m := G) hI hg (Filter.Eventually.of_forall hle)
  have hsc : condExp G P (fun ω => D ^ 2 * ‖a ω‖ ^ 2) =ᵐ[P]
      fun ζ => D ^ 2 * condExp G P (fun ω => ‖a ω‖ ^ 2) ζ := by
    have := condExp_smul (μ := P) (D ^ 2) (fun ω => ‖a ω‖ ^ 2) G
    simpa [Pi.smul_def, smul_eq_mul] using this
  filter_upwards [hc, hsc, hK] with ζ h1 h2 h3
  have h4 : condExp G P (fun ω => ‖e ω‖ ^ 2) ζ ≤ D ^ 2 * K ^ 2 := by
    have h2' : condExp G P (fun ω => D ^ 2 * ‖a ω‖ ^ 2) ζ =
        D ^ 2 * condExp G P (fun ω => ‖a ω‖ ^ 2) ζ := h2
    rw [h2'] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  calc Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ) ≤ Real.sqrt (D ^ 2 * K ^ 2) :=
        Real.sqrt_le_sqrt h4
    _ = D * K := by
        rw [show D ^ 2 * K ^ 2 = (D * K) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hD hK0)]

private lemma sd2_memLp2 (P : Measure Ω') (e a : Ω' → ℂ) (D : ℝ) (he : Measurable[mΩ] e)
    (hea : ∀ ω, ‖e ω‖ ≤ D * ‖a ω‖) (ha2 : Integrable (fun ω => ‖a ω‖ ^ 2) P) :
    MemLp e 2 P := by
  have hle : ∀ ω, ‖e ω‖ ^ 2 ≤ D ^ 2 * ‖a ω‖ ^ 2 := fun ω => by
    have := pow_le_pow_left₀ (norm_nonneg _) (hea ω) 2
    linarith [this, show (D * ‖a ω‖) ^ 2 = D ^ 2 * ‖a ω‖ ^ 2 by ring]
  rw [← memLp_norm_iff he.aestronglyMeasurable]
  refine (memLp_two_iff_integrable_sq he.norm.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (ha2.const_mul (D ^ 2)) (he.norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hle ω

end SD2H

/-- Complex four-term decomposition of `g (𝖷_z(M) − 𝖷_z(M₀))` (complex `cm_decomp`). -/
private lemma sd2_decomp {m n : ℕ} (M M0 : Mat m n) (g : ℂ) (h : ℝ) (z : ℂ) (u : Vec m)
    (v : Vec n) (hM : M = M0 + h • Muon.outer u v) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    g • (XzC M z - XzC M0 z) =
      Rres M0 (-z) * ((g * colAlpha3 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ)
          (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z) •
        (Muon.outer u u).map (fun x : ℝ => (x : ℂ))) * XzC M0 z
      + Rres M0 (-z) * ((g * (z * colAlpha1 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ)
          (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z)) •
        (Muon.outer u v).map (fun x : ℝ => (x : ℂ))) * Rtil M0 (-z)
      + XzC M0 z * ((-(g * colAlpha1 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ)
          (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z)) •
        (Muon.outer v u).map (fun x : ℝ => (x : ℂ))) * XzC M0 z
      + XzC M0 z * ((-(g * (z * colAlpha2 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ)
          (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z))) •
        (Muon.outer v v).map (fun x : ℝ => (x : ℂ))) * Rtil M0 (-z) := by
  obtain ⟨hL, hdel, -, -⟩ := lem_app_de_deletion_sector M0 h u v M z hM hz hzS
  obtain ⟨-, -, -, -, hdet0, hdett0⟩ := eqn_app_dyn_sector M0 z hz hzS
  have hMc : M.map (fun x : ℝ => (x : ℂ)) = M0.map (fun x : ℝ => (x : ℂ)) +
      (h : ℂ) • vecMulVec (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) := by
    ext i j
    simp [hM, Muon.outer, Matrix.vecMulVec_apply]
  have hx := lem_app_drift_column_field_ii (K := ℂ) (M.map (fun x : ℝ => (x : ℂ)))
    (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ) z (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) hMc
    hdet0 hdett0 hL hdel
  have eX : ∀ K : Mat m n, XzC K z = colX (K.map (fun x : ℝ => (x : ℂ))) z := fun K => by
    unfold XzC colX; rw [rres_neg_eq_colR]
  have eR : Rres M0 (-z) = colR (M0.map (fun x : ℝ => (x : ℂ))) z := rres_neg_eq_colR M0 z
  have eRt : Rtil M0 (-z) = colRt (M0.map (fun x : ℝ => (x : ℂ))) z := rtil_neg_eq_colRt M0 z
  have eo : ∀ {d d' : ℕ} (a : Vec d) (b : Vec d'), (Muon.outer a b).map (fun x : ℝ => (x : ℂ)) =
      vecMulVec (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) := by
    intro d d' a b; ext i j; simp [Muon.outer, Matrix.vecMulVec_apply]
  rw [eX M, eX M0, hx, eR, eRt, eo, eo, eo, eo, ← eX M0]
  simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add, smul_smul, smul_neg]
  module

/-- Final constant bookkeeping for `lem_app_drift_multiplier_i`. -/
private lemma sd2_arith (s0 s w D ϖ CS c r2 rg : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) (hw : 1 ≤ w)
    (hD : 0 ≤ D) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hCS : 0 ≤ CS) (hc : 0 ≤ c) (hr2 : 0 ≤ r2)
    (hrg : 0 ≤ rg) :
    (1 / s) * (CS * (r2 + rg * w) / w ^ 2 * (D * (c * ϖ ^ 2))) * (1 / (2 * Real.sqrt s))
      + (1 / s) * (CS / w ^ 2 * (D * s * (c * ϖ))) * (1 / s)
      + (1 / (2 * Real.sqrt s)) * (CS / w ^ 2 * (D * (c * ϖ))) * (1 / (2 * Real.sqrt s))
      + (1 / (2 * Real.sqrt s)) * (CS * (r2 + rg * w) / w ^ 2 * (D * s * (c * ϖ ^ 2 / s))) * (1 / s)
      ≤ c * CS * ((r2 + rg) / Real.sqrt s0 + 5 / 4) * D * ϖ / (s * w) := by
  have hs' : 0 < s := lt_of_lt_of_le hs0 hs
  have hw0 : 0 < w := by linarith
  have ht0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
  have htt : Real.sqrt s0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have hts : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs'.le
  have hw2 : w ≤ w ^ 2 := by nlinarith
  have hq : (r2 + rg * w) / w ^ 2 ≤ (r2 + rg) / w := by
    rw [div_le_div_iff₀ (by positivity) hw0]
    nlinarith [mul_nonneg hr2 (sub_nonneg.2 hw), mul_nonneg hrg hw0.le, mul_nonneg hr2 hw0.le]
  have hq2 : 1 / w ^ 2 ≤ 1 / w := one_div_le_one_div_of_le hw0 hw2
  have hϖ2 : ϖ ^ 2 ≤ ϖ := by nlinarith
  have hi : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt s0) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hi0 : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
  have hi0' : 0 ≤ 1 / (2 * Real.sqrt s0) := by positivity
  have hKq : 0 ≤ (r2 + rg * w) / w ^ 2 := by positivity
  have hP : 0 ≤ CS * D * c := by positivity
  -- term 1 and 4
  have e1 : (1 / s) * (CS * (r2 + rg * w) / w ^ 2 * (D * (c * ϖ ^ 2))) * (1 / (2 * Real.sqrt s))
      = (CS * D * c) / s * ((r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))) := by
    field_simp
  have e4 : (1 / (2 * Real.sqrt s)) * (CS * (r2 + rg * w) / w ^ 2 * (D * s * (c * ϖ ^ 2 / s))) * (1 / s)
      = (CS * D * c) / s * ((r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))) := by
    field_simp
  have e2 : (1 / s) * (CS / w ^ 2 * (D * s * (c * ϖ))) * (1 / s)
      = (CS * D * c) / s * (1 / w ^ 2 * ϖ) := by
    field_simp
  have e3 : (1 / (2 * Real.sqrt s)) * (CS / w ^ 2 * (D * (c * ϖ))) * (1 / (2 * Real.sqrt s))
      = (CS * D * c) / s * (1 / w ^ 2 * ϖ * (1 / 4)) := by
    field_simp
    rw [Real.sq_sqrt hs'.le]
    ring
  have b1 : (r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))
      ≤ (r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0)) := by
    gcongr
  have b2 : 1 / w ^ 2 * ϖ ≤ 1 / w * ϖ := by gcongr
  have b3 : 1 / w ^ 2 * ϖ * (1 / 4) ≤ 1 / w * ϖ * (1 / 4) := by gcongr
  have hPs : 0 ≤ (CS * D * c) / s := by positivity
  rw [e1, e2, e3, e4]
  calc _ ≤ (CS * D * c) / s * ((r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0)))
        + (CS * D * c) / s * (1 / w * ϖ) + (CS * D * c) / s * (1 / w * ϖ * (1 / 4))
        + (CS * D * c) / s * ((r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0))) := by
        gcongr
    _ = _ := by field_simp; ring


private lemma sd2_meas_comp' {Ω' : Type*} {α β : Type*} {m' : MeasurableSpace Ω'}
    [TopologicalSpace α] [MeasurableSpace α] [OpensMeasurableSpace α] [TopologicalSpace β]
    [MeasurableSpace β] [BorelSpace β] (f : α → β) (hf : Continuous f) {q : Ω' → α}
    (hq : Measurable[m'] q) : Measurable[m'] (fun ω => f (q ω)) := hf.measurable.comp hq

private lemma sd2_norm_z_le {z : ℂ} (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    ‖z‖ ≤ 2 * z.re := by
  obtain ⟨-, -, -, hzr, -, -⟩ := eqn_app_dyn_sector (0 : Mat 0 0) z hz hzS
  have h5 : Real.sqrt 5 ≤ 3 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [div_le_iff₀ hz] at hzr
  nlinarith

set_option maxHeartbeats 1000000 in
private theorem sd2_i_main (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
        sigmaOthers F S t j] h →
      (∀ ω, ‖h ω‖ ≤ D) →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        ∀ᵐ ω ∂P, fro (condExpMatC (sigmaOthers F S t j) P
          (fun ω' => h ω' • (XzC (ageBuf F S t j M0 ϖ ω') z - XzC (M0 ω') z)) ω) ≤
          C * D * ϖ / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨Cc, hCc⟩ := lem_app_drift_coeffmoments_sector 2 (by norm_num) s0 hs0 CS γ hγ
  refine ⟨2 * (|Cc| * CS * ((Real.sqrt 2 + Real.sqrt γ) / Real.sqrt s0 + 5 / 4)), ?_⟩
  intro Ω inst m n B P _ F S t j M0 ϖ D g hCo hCi hm hn hϖ0 hϖ1 hM0 hg hD z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hzn : ‖z‖ ≤ 2 * z.re := sd2_norm_z_le hspos hzS
  have hB : 0 < B := F.hB
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hCo
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  have hindc : Indep (MeasurableSpace.comap X inferInstance) (sigmaOthers F S t j) P := hind.symm
  obtain ⟨-, ⟨i1, c1'⟩, ⟨i3, c3'⟩, ⟨i2, c2'⟩⟩ :=
    hCc Ω m n B P F S t j M0 ϖ hCo hCi hm hn hϖ0 hϖ1 hM0 z hs hzS
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hX.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hM0c : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] M0 :=
    hM0.mono le_sup_right le_rfl
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hXc
  have hVm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hXc
  have hDm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => ϖ * resid F.A (X ω)) := (hdm.comp hXc).const_mul ϖ
  have hq : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => (M0 ω, ϖ * resid F.A (X ω), momU F.C B (X ω), momV F.C B (X ω))) :=
    hM0c.prodMk (hDm.prodMk (hUm.prodMk hVm))
  obtain ⟨c1, c2, c3⟩ := sd1_alpha_cont (m := m) (n := n) z hspos hzS
  have e1 : ∀ ω, ageAlphaC1 F S t j M0 ϖ z ω = colAlpha1 ((M0 ω).map (fun x : ℝ => (x : ℂ)))
      ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ))
      (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have e2 : ∀ ω, ageAlphaC2 F S t j M0 ϖ z ω = colAlpha2 ((M0 ω).map (fun x : ℝ => (x : ℂ)))
      ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ))
      (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have e3 : ∀ ω, ageAlphaC3 F S t j M0 ϖ z ω = colAlpha3 ((M0 ω).map (fun x : ℝ => (x : ℂ)))
      ((ϖ * resid F.A (X ω) : ℝ) : ℂ) (fun i => (momU F.C B (X ω) i : ℂ))
      (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have hA1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlphaC1 F S t j M0 ϖ z) := by
    rw [funext e1]
    have h := sd2_meas_comp' _ c1 hq
    exact h
  have hA2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlphaC2 F S t j M0 ϖ z) := by
    rw [funext e2]
    have h := sd2_meas_comp' _ c2 hq
    exact h
  have hA3 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlphaC3 F S t j M0 ϖ z) := by
    rw [funext e3]
    have h := sd2_meas_comp' _ c3 hq
    exact h
  have hD0 : 0 ≤ D := by
    obtain ⟨ω0, -⟩ := (Filter.Eventually.of_forall (p := fun _ : Ω => True) (fun _ => trivial) :
      ∀ᵐ ω ∂P, True).exists
    exact (norm_nonneg _).trans (hD ω0)
  have E1m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => g ω * ageAlphaC3 F S t j M0 ϖ z ω) := hg.mul hA3
  have E2m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => g ω * (z * ageAlphaC1 F S t j M0 ϖ z ω)) := hg.mul (hA1.const_mul z)
  have E3m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => -(g ω * ageAlphaC1 F S t j M0 ϖ z ω)) := (hg.mul hA1).neg
  have E4m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => -(g ω * (z * ageAlphaC2 F S t j M0 ϖ z ω))) := (hg.mul (hA2.const_mul z)).neg
  have hD2 : 0 ≤ D * (2 * z.re) := by positivity
  have ea1 : ∀ ω, ‖g ω * ageAlphaC3 F S t j M0 ϖ z ω‖ ≤ D * ‖ageAlphaC3 F S t j M0 ϖ z ω‖ :=
    fun ω => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD ω) (norm_nonneg _)
  have ea2 : ∀ ω, ‖g ω * (z * ageAlphaC1 F S t j M0 ϖ z ω)‖ ≤
      (D * (2 * z.re)) * ‖ageAlphaC1 F S t j M0 ϖ z ω‖ := fun ω => by
    rw [norm_mul, norm_mul]
    calc _ ≤ D * ((2 * z.re) * ‖ageAlphaC1 F S t j M0 ϖ z ω‖) :=
          mul_le_mul (hD ω) (mul_le_mul_of_nonneg_right hzn (norm_nonneg _))
            (by positivity) hD0
      _ = _ := by ring
  have ea3 : ∀ ω, ‖-(g ω * ageAlphaC1 F S t j M0 ϖ z ω)‖ ≤ D * ‖ageAlphaC1 F S t j M0 ϖ z ω‖ :=
    fun ω => by rw [norm_neg, norm_mul]; exact mul_le_mul_of_nonneg_right (hD ω) (norm_nonneg _)
  have ea4 : ∀ ω, ‖-(g ω * (z * ageAlphaC2 F S t j M0 ϖ z ω))‖ ≤
      (D * (2 * z.re)) * ‖ageAlphaC2 F S t j M0 ϖ z ω‖ := fun ω => by
    rw [norm_neg, norm_mul, norm_mul]
    calc _ ≤ D * ((2 * z.re) * ‖ageAlphaC2 F S t j M0 ϖ z ω‖) :=
          mul_le_mul (hD ω) (mul_le_mul_of_nonneg_right hzn (norm_nonneg _))
            (by positivity) hD0
      _ = _ := by ring
  have L1 := sd2_memLp2 P _ _ D (E1m.mono hGc le_rfl) ea1 i3
  have L2 := sd2_memLp2 P _ _ (D * (2 * z.re)) (E2m.mono hGc le_rfl) ea2 i1
  have L3 := sd2_memLp2 P _ _ D (E3m.mono hGc le_rfl) ea3 i1
  have L4 := sd2_memLp2 P _ _ (D * (2 * z.re)) (E4m.mono hGc le_rfl) ea4 i2
  have hc0 : 0 ≤ |Cc| := abs_nonneg _
  have K1 := sd2_cond_sq P (sigmaOthers F S t j) _ _ D (|Cc| * ϖ ^ 2) hD0 (by positivity)
    (E1m.mono hGc le_rfl) ea1 i3
    (by filter_upwards [c3'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K2 := sd2_cond_sq P (sigmaOthers F S t j) _ _ (D * (2 * z.re)) (|Cc| * ϖ) hD2
    (by positivity) (E2m.mono hGc le_rfl) ea2 i1
    (by filter_upwards [c1'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K3 := sd2_cond_sq P (sigmaOthers F S t j) _ _ D (|Cc| * ϖ) hD0 (by positivity)
    (E3m.mono hGc le_rfl) ea3 i1
    (by filter_upwards [c1'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K4 := sd2_cond_sq P (sigmaOthers F S t j) _ _ (D * (2 * z.re)) (|Cc| * ϖ ^ 2 / z.re) hD2
    (by positivity) (E4m.mono hGc le_rfl) ea4 i2
    (by filter_upwards [c2'] with ω h
        exact h.trans_eq (by rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]))
  have hentm : ∀ {a b : ℕ} (Φ : Mat m n → Matrix (Fin a) (Fin b) ℂ), Continuous Φ →
      ∀ (i : Fin a) (j' : Fin b), Measurable[sigmaOthers F S t j] (fun ω => Φ (M0 ω) i j') := by
    intro a b Φ hΦ i k
    exact ((hΦ.matrix_elem i k).measurable).comp hM0
  have hcR : Continuous (fun K : Mat m n => Rres K (-z)) := sd0_cont_R z hspos
  have hcRt : Continuous (fun K : Mat m n => Rtil K (-z)) := by
    have e : (fun K : Mat m n => Rtil K (-z)) = fun K => Rres Kᵀ (-z) := by
      funext K; exact sd1_Rtil_eq K _
    rw [e]
    exact (sd0_cont_R z hspos).comp continuous_id.matrix_transpose
  have hcX : Continuous (fun K : Mat m n => XzC K z) := sd0_cont_X z hspos
  have hF := sd2_four (mΩ := inst) P F.C CS γ hB hCo hCi hm hn X hlaw (sigmaOthers F S t j) hG
    hindc
    (fun ω => Rres (M0 ω) (-z)) (fun ω => Rtil (M0 ω) (-z))
    (fun ω => XzC (M0 ω) z) (1 / z.re) (1 / (2 * Real.sqrt z.re)) (by positivity)
    (by positivity)
    (hentm _ hcR) (hentm _ hcRt) (hentm _ hcX)
    (fun ω => sd0_R_bound _ z hspos)
    (fun ω => by rw [sd1_Rtil_eq]; exact sd0_R_bound _ z hspos)
    (fun ω => sd0_X_bound _ z hspos)
    _ _ _ _ E1m E2m E3m E4m L1 L2 L3 L4
    (D * (|Cc| * ϖ ^ 2)) (D * (2 * z.re) * (|Cc| * ϖ)) (D * (|Cc| * ϖ))
    (D * (2 * z.re) * (|Cc| * ϖ ^ 2 / z.re))
    (by positivity) (by positivity) (by positivity) (by positivity) K1 K2 K3 K4
  have hfun : (fun ω' => g ω' • (XzC (ageBuf F S t j M0 ϖ ω') z - XzC (M0 ω') z)) = fun ω =>
        Rres (M0 ω) (-z) * ((g ω * ageAlphaC3 F S t j M0 ϖ z ω) •
          (Muon.outer (momU F.C B (X ω)) (momU F.C B (X ω))).map (fun x : ℝ => (x : ℂ)))
          * XzC (M0 ω) z
        + Rres (M0 ω) (-z) * ((g ω * (z * ageAlphaC1 F S t j M0 ϖ z ω)) •
          (Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))).map (fun x : ℝ => (x : ℂ)))
          * Rtil (M0 ω) (-z)
        + XzC (M0 ω) z * ((-(g ω * ageAlphaC1 F S t j M0 ϖ z ω)) •
          (Muon.outer (momV F.C B (X ω)) (momU F.C B (X ω))).map (fun x : ℝ => (x : ℂ)))
          * XzC (M0 ω) z
        + XzC (M0 ω) z * ((-(g ω * (z * ageAlphaC2 F S t j M0 ϖ z ω))) •
          (Muon.outer (momV F.C B (X ω)) (momV F.C B (X ω))).map (fun x : ℝ => (x : ℂ)))
          * Rtil (M0 ω) (-z) :=
    funext fun ω => sd2_decomp (ageBuf F S t j M0 ϖ ω) (M0 ω) (g ω) (ϖ * ageD F S t j ω) z
      (ageU F S t j ω) (ageV F S t j ω) rfl hspos hzS
  rw [hfun]
  filter_upwards [hF] with ζ hζ
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hsq : Real.sqrt (γ * (B : ℝ)) = Real.sqrt γ * Real.sqrt (B : ℝ) := Real.sqrt_mul hγ _
  rw [hsq] at hζ
  have hw1 : (1 : ℝ) ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hB)
  have hBw : (B : ℝ) = Real.sqrt (B : ℝ) ^ 2 := (Real.sq_sqrt hBpos.le).symm
  generalize Real.sqrt (B : ℝ) = w at hζ hw1 hBw ⊢
  rw [hBw] at hζ
  have hAr := sd2_arith s0 z.re w D ϖ CS |Cc| (Real.sqrt 2) (Real.sqrt γ) hs0 hs hw1 hD0 hϖ0 hϖ1
    hCS hc0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hw0 : 0 < w := by linarith
  have ht : 0 < Real.sqrt z.re := Real.sqrt_pos.2 hspos
  have hT1 : 0 ≤ (1 / z.re) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 * (D * (|Cc| * ϖ ^ 2)))
      * (1 / (2 * Real.sqrt z.re)) := by positivity
  have hT3 : 0 ≤ (1 / (2 * Real.sqrt z.re)) * (CS / w ^ 2 * (D * (|Cc| * ϖ)))
      * (1 / (2 * Real.sqrt z.re)) := by positivity
  have hEq : (1 / z.re) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 * (D * (|Cc| * ϖ ^ 2)))
        * (1 / (2 * Real.sqrt z.re))
      + (1 / z.re) * (CS / w ^ 2 * (D * (2 * z.re) * (|Cc| * ϖ))) * (1 / z.re)
      + (1 / (2 * Real.sqrt z.re)) * (CS / w ^ 2 * (D * (|Cc| * ϖ))) * (1 / (2 * Real.sqrt z.re))
      + (1 / (2 * Real.sqrt z.re)) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 *
          (D * (2 * z.re) * (|Cc| * ϖ ^ 2 / z.re))) * (1 / z.re)
      ≤ 2 * ((1 / z.re) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 *
          (D * (|Cc| * ϖ ^ 2))) * (1 / (2 * Real.sqrt z.re))
        + (1 / z.re) * (CS / w ^ 2 * (D * z.re * (|Cc| * ϖ))) * (1 / z.re)
        + (1 / (2 * Real.sqrt z.re)) * (CS / w ^ 2 * (D * (|Cc| * ϖ))) *
          (1 / (2 * Real.sqrt z.re))
        + (1 / (2 * Real.sqrt z.re)) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 *
          (D * z.re * (|Cc| * ϖ ^ 2 / z.re))) * (1 / z.re)) := by
    have e2 : (1 / z.re) * (CS / w ^ 2 * (D * (2 * z.re) * (|Cc| * ϖ))) * (1 / z.re) =
        2 * ((1 / z.re) * (CS / w ^ 2 * (D * z.re * (|Cc| * ϖ))) * (1 / z.re)) := by ring
    have e4 : (1 / (2 * Real.sqrt z.re)) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 *
          (D * (2 * z.re) * (|Cc| * ϖ ^ 2 / z.re))) * (1 / z.re) =
        2 * ((1 / (2 * Real.sqrt z.re)) * (CS * (Real.sqrt 2 + Real.sqrt γ * w) / w ^ 2 *
          (D * z.re * (|Cc| * ϖ ^ 2 / z.re))) * (1 / z.re)) := by ring
    rw [e2, e4]
    linarith [hT1, hT3]
  refine hζ.trans (hEq.trans ?_)
  calc _ ≤ 2 * (|Cc| * CS * ((Real.sqrt 2 + Real.sqrt γ) / Real.sqrt s0 + 5 / 4) * D * ϖ /
        (z.re * w)) := by linarith [hAr]
    _ = _ := by ring

/-- `lem:app-drift-multiplier`, first claim (`eqn:app-drift-multiplier`), at `z ∈ 𝕊`, snapshot
`cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 858–870):
```latex
\emph{(i), rank, deletion and covariance bounds.} The three bounds
\cref{lem:app-drift-rank,lem:app-drift-multiplier,lem:app-drift-covariance}
hold for $z\in\mathbb S$ with $s$ replaced by $x$ in their right sides. Their
proofs use only \cref{eqn:app-dyn-sector}, the inverse bound, the coefficient
moments just proved, and the low-rank structure of resolvent differences:
for $\rank(K-K')\le k$, $R_z(K)-R_z(K')=R_z(K)(K'K'^\T-KK^\T)R_z(K')$ has rank
at most $2k$ and nuclear norm at most $4k/x$, and the mixed block has rank at
most $2k$ and nuclear norm at most $2k/\sqrt x$. In the denominator
difference \cref{eqn:app-drift-delta-alpha}, the factor $z$ multiplies
$\mathsf V$ or $\mathsf U'$, and $\abs z\abs{\mathsf V}\le(\sqrt5/2)\mathsf N$ cancels it.
Complex Gaussian quadratic forms are bounded through their real and
imaginary parts.
```
Real counterpart `Muon.Drift.lem_app_drift_multiplier_i` (`Coefficients.lean`:1991), same shape.
The multiplier `h` is complex (bounded by `D` in modulus): the covariance step at complex `z`
applies this lemma with the complex martingale differences `D_l` as multipliers. -/
theorem lem_app_drift_multiplier_i_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
        sigmaOthers F S t j] h →
      (∀ ω, ‖h ω‖ ≤ D) →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        ∀ᵐ ω ∂P, fro (condExpMatC (sigmaOthers F S t j) P
          (fun ω' => h ω' • (XzC (ageBuf F S t j M0 ϖ ω') z - XzC (M0 ω') z)) ω) ≤
          C * D * ϖ / (z.re * Real.sqrt (B : ℝ)) := by
  exact sd2_i_main s0 hs0 CS γ hγ

open scoped MatrixOrder in
private lemma sd2m_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * Muon.outer z w * rIn F.C =
      Muon.outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hsym : (rIn F.C)ᵀ = rIn F.C := by
    have h : (CFC.sqrt F.C.Sin)ᴴ = CFC.sqrt F.C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F.C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, hsym]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma sd2m_sample {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) (ω : Ω) :
    (B : ℝ)⁻¹ • sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) • Muon.outer (momU F.C B (S.zw s a ω)) (momV F.C B (S.zw s a ω)) := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) •
        Muon.outer (Matrix.mulVec (rOut F.C) (S.zw s a ω).1)
          (Matrix.mulVec (rIn F.C) (S.zw s a ω).2) := by
    unfold sampleTerm
    rw [sd2m_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

private lemma sd2m_meas_del {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := sd0_hQ F
  have hzw : ∀ p : ℤ × Fin B, p ≠ (t + 1 - (j : ℤ), slotOne F.hB) →
      Measurable[sigmaOthers F S t j] (S.zw p.1 p.2) := by
    intro p hp
    have hle : MeasurableSpace.comap (S.zw p.1 p.2) inferInstance ≤ sigmaOthers F S t j :=
      le_iSup₂ (f := fun (p : ℤ × Fin B) (_ : p ≠ (t + 1 - (j : ℤ), slotOne F.hB)) =>
        MeasurableSpace.comap (S.zw p.1 p.2) inferInstance) p hp
    exact (comap_measurable (S.zw p.1 p.2)).mono hle le_rfl
  unfold delBufAge WeightedBufDel
  letI : MeasurableSpace Ω := sigmaOthers F S t j
  refine Measurable.tsum fun j' => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j')
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j' : ℤ) = t + 1 - (j : ℤ) ∧ b = slotOne F.hB
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have hne : ((t + 1 - (j' : ℤ), b) : ℤ × Fin B) ≠ (t + 1 - (j : ℤ), slotOne F.hB) := by
      intro heq; exact h ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    exact hQ.comp (hzw _ hne)

private lemma sd2m_decomp {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (w : ℕ → ℝ)
    (hw : WeightClass w) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = ageBuf F S t j (delBufAge w F S t j) (w j) ω := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) j rfl ω (hω t)
  rw [h, sd2m_sample, smul_smul]
  rfl


private lemma sd2m_resid_meas {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    Measurable (fun ω => resid F.A (S.zw s a ω)) := by
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  exact hdm.comp (S.meas s a)

private lemma sd2m_entry_int {m n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (z : ℂ)
    (hz : 0 < z.re) (X : Ω → Mat m n) (hX : Measurable X) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => XzC (X ω) z i k) P := by
  have hm : Measurable (fun ω => XzC (X ω) z i k) :=
    ((sd0_cont_X z hz).matrix_elem i k).measurable.comp hX
  refine Integrable.mono' (integrable_const (1 / (2 * Real.sqrt z.re))) hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  exact (sd0_entry_le _ i k).trans (sd0_X_bound _ z hz)

private lemma sd2m_tower {Ω' : Type*} {mΩ : MeasurableSpace Ω'} (P : Measure Ω')
    [IsProbabilityMeasure P] (G : MeasurableSpace Ω') (hG : G ≤ mΩ) {m n : ℕ}
    (F : Ω' → Matrix (Fin m) (Fin n) ℂ) :
    @meanC Ω' mΩ _ _ P F = @meanC Ω' mΩ _ _ P (condExpMatC G P F) := by
  ext i k
  simp only [meanC, Matrix.of_apply]
  exact (integral_condExp hG).symm

/-- Mean of a bounded-Frobenius complex random matrix: `‖𝔼Y‖_F ≤ K` when `‖Y‖_F ≤ K` a.s. -/
private lemma sd2m_fro_mean_le {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {m n : ℕ}
    (P : Measure Ω') [IsProbabilityMeasure P] (Y : Ω' → Matrix (Fin m) (Fin n) ℂ)
    (hY : ∀ i k, Integrable (fun ω => Y ω i k) P) (K : ℝ) (hK : ∀ᵐ ω ∂P, fro (Y ω) ≤ K) :
    fro (meanC P Y) ≤ K := by
  have hint : ∀ i k, Integrable (fun ω => (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re) P :=
    fun i k => ((hY i k).const_mul _).re
  have hfro0 : 0 ≤ fro (meanC P Y) := Real.sqrt_nonneg _
  have hsum_int : Integrable (fun ω => ∑ i, ∑ k, (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k
  have hsq : ∫ ω, ∑ i, ∑ k, (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re ∂P =
      fro (meanC P Y) ^ 2 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    have hfro2 : fro (meanC P Y) ^ 2 = ∑ i, ∑ k, ‖meanC P Y i k‖ ^ 2 := by
      unfold fro
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity)]
    rw [hfro2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun k _ => hint i k]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := integral_re (𝕜 := ℂ) ((hY i k).const_mul (starRingEnd ℂ (meanC P Y i k)))
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul]
    have : ∫ ω, Y ω i k ∂P = meanC P Y i k := rfl
    rw [this, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hpt : ∀ ω, ∑ i, ∑ k, (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re ≤
      fro (meanC P Y) * fro (Y ω) := by
    intro ω
    have e1 : ∑ i, ∑ k, (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re =
        ∑ p : Fin m × Fin n, (starRingEnd ℂ (meanC P Y p.1 p.2) * Y ω p.1 p.2).re :=
      (Fintype.sum_prod_type (fun p : Fin m × Fin n =>
        (starRingEnd ℂ (meanC P Y p.1 p.2) * Y ω p.1 p.2).re)).symm
    have eM : fro (meanC P Y) = Real.sqrt (∑ p : Fin m × Fin n, ‖meanC P Y p.1 p.2‖ ^ 2) := by
      unfold fro
      congr 1
      simp only [Fintype.sum_prod_type]
    have eY : fro (Y ω) = Real.sqrt (∑ p : Fin m × Fin n, ‖Y ω p.1 p.2‖ ^ 2) := by
      unfold fro
      congr 1
      simp only [Fintype.sum_prod_type]
    rw [e1, eM, eY]
    calc ∑ p : Fin m × Fin n, (starRingEnd ℂ (meanC P Y p.1 p.2) * Y ω p.1 p.2).re
        ≤ ∑ p : Fin m × Fin n, ‖meanC P Y p.1 p.2‖ * ‖Y ω p.1 p.2‖ :=
          Finset.sum_le_sum fun p _ => by
            refine (Complex.re_le_norm _).trans ?_
            rw [norm_mul, Complex.norm_conj]
      _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
            (fun p : Fin m × Fin n => ‖meanC P Y p.1 p.2‖)
            (fun p : Fin m × Fin n => ‖Y ω p.1 p.2‖)
  have hle : ∫ ω, ∑ i, ∑ k, (starRingEnd ℂ (meanC P Y i k) * Y ω i k).re ∂P ≤
      ∫ _ω, fro (meanC P Y) * K ∂P := by
    refine integral_mono_ae hsum_int (integrable_const _) ?_
    filter_upwards [hK] with ω hω
    exact (hpt ω).trans (mul_le_mul_of_nonneg_left hω hfro0)
  rw [hsq, integral_const, probReal_univ, one_smul] at hle
  obtain ⟨ω0, hω0⟩ := hK.exists
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hω0
  rcases hfro0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hK0
  · have h2 : fro (meanC P Y) * fro (meanC P Y) ≤ fro (meanC P Y) * K := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left h2 hpos

/-- `lem:app-drift-multiplier`, second claim (`eqn:app-drift-deletion-mean`), at `z ∈ 𝕊` and for a
general weight sequence, snapshot `cr-2026-10-23` (source as in
`lem_app_drift_multiplier_i_sector`, ll. 858–861): `‖𝓗(z) − 𝓗_j(z)‖_F ≤ C w_j/(x√B)`. Real
counterpart `Muon.Drift.lem_app_drift_multiplier_ii_weights` (`Coefficients.lean`:2211). -/
theorem lem_app_drift_multiplier_ii_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (w : ℕ → ℝ),
      WeightClass w →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        fro (HmixC w F S t z - HjC w F S t j z) ≤ C * w j / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_multiplier_i_sector s0 hs0 CS γ hγ
  refine ⟨C, fun Ω inst m n B P _ F S t j w hw hSo hSi hm hn z hs hzS => ?_⟩
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM0 : Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := sd2m_meas_del w F S t j
  have hM0' : Measurable (delBufAge w F S t j) := hM0.mono hG le_rfl
  have hdec := sd2m_decomp (P := P) w hw F S t j
  have hcm := hC Ω m n B P F S t j (delBufAge w F S t j) (w j) 1 (fun _ => (1 : ℂ))
    hSo hSi hm hn hw0 hw1 hM0 measurable_const (fun _ => by simp) z hs hzS
  simp only [one_smul, mul_one] at hcm
  have hI1' : ∀ i k, Integrable (fun ω => XzC (WeightedBuf w F S t ω) z i k) P :=
    fun i k => sd2m_entry_int z hspos _ (sd0_meas_WB w F S t) i k
  have hI0 : ∀ i k, Integrable (fun ω => XzC (delBufAge w F S t j ω) z i k) P :=
    fun i k => sd2m_entry_int z hspos _ hM0' i k
  have hkey : HmixC w F S t z - HjC w F S t j z =
      meanC P (fun ω => XzC (ageBuf F S t j (delBufAge w F S t j) (w j) ω) z -
        XzC (delBufAge w F S t j ω) z) := by
    ext i k
    simp only [HmixC, HjC, meanC, Matrix.of_apply, Matrix.sub_apply]
    rw [← integral_sub (hI1' i k) (hI0 i k)]
    refine integral_congr_ae ?_
    filter_upwards [hdec] with ω hω
    simp only [hω, Matrix.sub_apply]
  rw [hkey, sd2m_tower P (sigmaOthers F S t j) hG]
  refine sd2m_fro_mean_le P _ (fun i k => ?_) _ hcm
  exact integrable_condExp

/-! ### Helpers for `lem_app_drift_rank_sector` -/

private lemma sd3_re_mul3 {a b c d : ℕ} (P : Matrix (Fin a) (Fin b) ℂ) (Δ : Mat b c)
    (Q : Matrix (Fin c) (Fin d) ℂ) :
    (P * Δ.map (fun x : ℝ => (x : ℂ)) * Q).map Complex.re =
      P.map Complex.re * Δ * Q.map Complex.re - P.map Complex.im * Δ * Q.map Complex.im := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.sub_apply, Complex.re_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, zero_add, Finset.sum_mul, ← Finset.sum_sub_distrib]

private lemma sd3_im_mul3 {a b c d : ℕ} (P : Matrix (Fin a) (Fin b) ℂ) (Δ : Mat b c)
    (Q : Matrix (Fin c) (Fin d) ℂ) :
    (P * Δ.map (fun x : ℝ => (x : ℂ)) * Q).map Complex.im =
      P.map Complex.re * Δ * Q.map Complex.im + P.map Complex.im * Δ * Q.map Complex.re := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.add_apply, Complex.im_sum,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_sum,
    mul_zero, sub_zero, zero_add, add_zero, Finset.sum_mul, ← Finset.sum_add_distrib]

private lemma sd3_re_mul_real {a b c : ℕ} (P : Matrix (Fin a) (Fin b) ℂ) (K : Mat b c) :
    (P * K.map (fun x : ℝ => (x : ℂ))).map Complex.re = P.map Complex.re * K := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Complex.re_sum, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private lemma sd3_im_mul_real {a b c : ℕ} (P : Matrix (Fin a) (Fin b) ℂ) (K : Mat b c) :
    (P * K.map (fun x : ℝ => (x : ℂ))).map Complex.im = P.map Complex.im * K := by
  ext i j
  simp only [Matrix.map_apply, Matrix.mul_apply, Complex.im_sum, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]

private lemma sd3_rank_add {k l : ℕ} (A B : Mat k l) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rw [Matrix.mulVecLin_add]
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private lemma sd3_rank_neg {k l : ℕ} (A : Mat k l) : (-A).rank = A.rank := by
  unfold Matrix.rank
  have : Matrix.mulVecLin (-A) = -Matrix.mulVecLin A := by
    ext x i; simp
  rw [this, LinearMap.range_neg]

private lemma sd3_rank_sub {k l : ℕ} (A B : Mat k l) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg]
  have := sd3_rank_add A (-B)
  rwa [sd3_rank_neg] at this

private lemma sd3_rank_sub_comm {k l : ℕ} (A B : Mat k l) : (A - B).rank = (B - A).rank := by
  rw [← neg_sub, sd3_rank_neg]

/-- the rank of the real and imaginary parts of `P Δ Q` for real `Δ` -/
private lemma sd3_rank_re_im {a b c d : ℕ} (P : Matrix (Fin a) (Fin b) ℂ) (Δ : Mat b c)
    (Q : Matrix (Fin c) (Fin d) ℂ) (r : ℕ) (hr : Δ.rank ≤ r) :
    ((P * Δ.map (fun x : ℝ => (x : ℂ)) * Q).map Complex.re).rank ≤ 2 * r ∧
    ((P * Δ.map (fun x : ℝ => (x : ℂ)) * Q).map Complex.im).rank ≤ 2 * r := by
  have h1 : ∀ (P' : Mat a b) (Q' : Mat c d), (P' * Δ * Q').rank ≤ r := fun P' Q' =>
    ((Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)).trans hr
  have a1 := h1 (P.map Complex.re) (Q.map Complex.re)
  have a2 := h1 (P.map Complex.im) (Q.map Complex.im)
  have a3 := h1 (P.map Complex.re) (Q.map Complex.im)
  have a4 := h1 (P.map Complex.im) (Q.map Complex.re)
  rw [sd3_re_mul3, sd3_im_mul3]
  constructor
  · exact (sd3_rank_sub _ _).trans (by omega)
  · exact (sd3_rank_add _ _).trans (by omega)

/-- `rank (K'K'ᵀ − KKᵀ) ≤ 2 rank (K − K')` -/
private lemma sd3_rank_gram {a b : ℕ} (K K' : Mat a b) (k : ℕ) (hk : (K - K').rank ≤ k) :
    (K' * K'ᵀ - K * Kᵀ).rank ≤ 2 * k := by
  have e2 : K' * K'ᵀ - K * Kᵀ = (K' - K) * K'ᵀ + K * (K' - K)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e2]
  refine (sd3_rank_add _ _).trans ?_
  have r1 : ((K' - K) * K'ᵀ).rank ≤ (K - K').rank := by
    rw [sd3_rank_sub_comm]; exact Matrix.rank_mul_le_left _ _
  have r2 : (K * (K' - K)ᵀ).rank ≤ (K - K').rank := by
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    rw [Matrix.rank_transpose, sd3_rank_sub_comm]
  omega

/-- resolvent difference `R_z(K) − R_z(K') = R_z(K) (K'K'ᵀ − KKᵀ) R_z(K')` -/
private lemma sd3_res_diff {a b : ℕ} (K K' : Mat a b) (z : ℂ) (hz : 0 < z.re) :
    Rres K (-z) - Rres K' (-z) =
      Rres K (-z) * (K' * K'ᵀ - K * Kᵀ).map (fun x : ℝ => (x : ℂ)) * Rres K' (-z) := by
  have hG : IsUnit (K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ +
      z • (1 : Matrix (Fin a) (Fin a) ℂ)).det := sd0_unit K z hz
  have hG' : IsUnit (K'.map (fun x : ℝ => (x : ℂ)) * (K'.map (fun x : ℝ => (x : ℂ)))ᵀ +
      z • (1 : Matrix (Fin a) (Fin a) ℂ)).det := sd0_unit K' z hz
  have h1 := Matrix.nonsing_inv_mul _ hG
  have h2 := Matrix.mul_nonsing_inv _ hG'
  have hm1 : ∀ L : Mat a b, (L * Lᵀ).map (fun x : ℝ => (x : ℂ)) =
      L.map (fun x : ℝ => (x : ℂ)) * (L.map (fun x : ℝ => (x : ℂ)))ᵀ := fun L => by
    rw [← Matrix.transpose_map]
    exact Matrix.map_mul (f := Complex.ofRealHom)
  have hmap : (K' * K'ᵀ - K * Kᵀ).map (fun x : ℝ => (x : ℂ)) =
      K'.map (fun x : ℝ => (x : ℂ)) * (K'.map (fun x : ℝ => (x : ℂ)))ᵀ -
        K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ := by
    rw [← hm1, ← hm1]
    ext i j
    simp
  rw [hmap, sd0_Rres_eq, sd0_Rres_eq]
  set A := K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ
  set A' := K'.map (fun x : ℝ => (x : ℂ)) * (K'.map (fun x : ℝ => (x : ℂ)))ᵀ
  have h3 : A' - A = (A' + z • (1 : Matrix (Fin a) (Fin a) ℂ)) - (A + z • 1) := by abel
  rw [h3, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, h2, Matrix.mul_one, h1,
    Matrix.one_mul]

private lemma sd3_rank_D {a b : ℕ} (A A' : Mat a b) (z : ℂ) (hz : 0 < z.re) (k : ℕ)
    (hk : (A - A').rank ≤ k) :
    ((Rres A (-z) - Rres A' (-z)).map Complex.re).rank ≤ 4 * k ∧
    ((Rres A (-z) - Rres A' (-z)).map Complex.im).rank ≤ 4 * k := by
  rw [sd3_res_diff A A' z hz]
  have := sd3_rank_re_im (Rres A (-z)) (A' * A'ᵀ - A * Aᵀ) (Rres A' (-z)) (2 * k)
    (sd3_rank_gram A A' k hk)
  constructor <;> omega

private lemma sd3_rank_E {a b : ℕ} (A A' : Mat a b) (z : ℂ) (hz : 0 < z.re) (k : ℕ)
    (hk : (A - A').rank ≤ k) :
    ((XzC A z - XzC A' z).map Complex.re).rank ≤ 5 * k ∧
    ((XzC A z - XzC A' z).map Complex.im).rank ≤ 5 * k := by
  obtain ⟨hr, hi⟩ := sd3_rank_D A A' z hz k hk
  have e : XzC A z - XzC A' z =
      (Rres A (-z) - Rres A' (-z)) * A.map (fun x : ℝ => (x : ℂ)) +
        Rres A' (-z) * (A - A').map (fun x : ℝ => (x : ℂ)) := by
    unfold XzC
    have : (A - A').map (fun x : ℝ => (x : ℂ)) =
        A.map (fun x : ℝ => (x : ℂ)) - A'.map (fun x : ℝ => (x : ℂ)) := by
      ext i j; simp
    rw [this, Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e]
  have eRe : ∀ X Y : Matrix (Fin a) (Fin b) ℂ,
      (X + Y).map Complex.re = X.map Complex.re + Y.map Complex.re := fun X Y => by
    ext i j; simp
  have eIm : ∀ X Y : Matrix (Fin a) (Fin b) ℂ,
      (X + Y).map Complex.im = X.map Complex.im + Y.map Complex.im := fun X Y => by
    ext i j; simp
  rw [eRe, eIm, sd3_re_mul_real, sd3_re_mul_real, sd3_im_mul_real, sd3_im_mul_real]
  constructor
  · refine (sd3_rank_add _ _).trans ?_
    have := Matrix.rank_mul_le_left ((Rres A (-z) - Rres A' (-z)).map Complex.re) A
    have := Matrix.rank_mul_le_right ((Rres A' (-z)).map Complex.re) (A - A')
    omega
  · refine (sd3_rank_add _ _).trans ?_
    have := Matrix.rank_mul_le_left ((Rres A (-z) - Rres A' (-z)).map Complex.im) A
    have := Matrix.rank_mul_le_right ((Rres A' (-z)).map Complex.im) (A - A')
    omega

open scoped Matrix.Norms.L2Operator in
private lemma sd3_opNorm_le_real {a b : ℕ} (A : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin b → ℝ, ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (A *ᵥ x)‖ ≤
      c * ‖(EuclideanSpace.equiv (Fin b) ℝ).symm x‖) : opNorm A ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv (Fin a) ℝ).symm
      (A *ᵥ (EuclideanSpace.equiv (Fin b) ℝ x))‖ ≤ c * ‖x‖
  simpa using h (EuclideanSpace.equiv (Fin b) ℝ x)

open scoped Matrix.Norms.L2Operator in
private lemma sd3_opNorm_re_im_le {a b : ℕ} (D : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (D.map Complex.re) ≤ opNorm D ∧ opNorm (D.map Complex.im) ≤ opNorm D := by
  have hD0 := sd2_opNorm_nonneg D
  have key : ∀ x : Fin b → ℝ,
      ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (D *ᵥ fun i => (x i : ℂ))‖ ≤
        opNorm D * ‖(EuclideanSpace.equiv (Fin b) ℝ).symm x‖ := by
    intro x
    have h1 : ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (D *ᵥ fun i => (x i : ℂ))‖ ≤
        opNorm D * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm (fun i => (x i : ℂ))‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec D ((EuclideanSpace.equiv (Fin b) ℂ).symm fun i => (x i : ℂ))
    have h2 : ‖(EuclideanSpace.equiv (Fin b) ℂ).symm (fun i => (x i : ℂ))‖ =
        ‖(EuclideanSpace.equiv (Fin b) ℝ).symm x‖ := by
      rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
      congr 1
      simp
    rwa [h2] at h1
  have pw : ∀ (x : Fin b → ℝ) (f : ℂ → ℝ), (∀ w : ℂ, |f w| ≤ ‖w‖) →
      ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (fun i => f ((D *ᵥ fun i => (x i : ℂ)) i))‖ ≤
        ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (D *ᵥ fun i => (x i : ℂ))‖ := by
    intro x f hf
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    have := pow_le_pow_left₀ (abs_nonneg (f ((D *ᵥ fun i => (x i : ℂ)) i)))
      (hf ((D *ᵥ fun i => (x i : ℂ)) i)) 2
    simpa using this
  constructor
  · refine sd3_opNorm_le_real _ hD0 fun x => ?_
    have e : (D.map Complex.re) *ᵥ x = fun i => (fun w : ℂ => w.re) ((D *ᵥ fun i => (x i : ℂ)) i) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.mul_re]
    rw [e]
    exact (pw x (fun w => w.re) fun w => Complex.abs_re_le_norm w).trans (key x)
  · refine sd3_opNorm_le_real _ hD0 fun x => ?_
    have e : (D.map Complex.im) *ᵥ x = fun i => (fun w : ℂ => w.im) ((D *ᵥ fun i => (x i : ℂ)) i) := by
      ext i
      simp [Matrix.mulVec, dotProduct, Complex.im_sum, Complex.mul_im]
    rw [e]
    exact (pw x (fun w => w.im) fun w => Complex.abs_im_le_norm w).trans (key x)

open scoped Matrix.Norms.L2Operator in
private lemma sd3_opNorm_sub {a b : ℕ} (A B : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (A - B) ≤ opNorm A + opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_sub_le _ _

private lemma sd3_nuc_D {a b : ℕ} (A A' : Mat a b) (z : ℂ) (hz : 0 < z.re) (k : ℕ)
    (hk : (A - A').rank ≤ k) :
    nuc ((Rres A (-z) - Rres A' (-z)).map Complex.re) ≤ 8 * k / z.re ∧
    nuc ((Rres A (-z) - Rres A' (-z)).map Complex.im) ≤ 8 * k / z.re := by
  obtain ⟨hr, hi⟩ := sd3_rank_D A A' z hz k hk
  have ho : opNorm (Rres A (-z) - Rres A' (-z)) ≤ 2 / z.re :=
    (sd3_opNorm_sub _ _).trans (by
      have := sd0_R_bound A z hz
      have := sd0_R_bound A' z hz
      calc _ ≤ 1 / z.re + 1 / z.re := add_le_add (sd0_R_bound A z hz) (sd0_R_bound A' z hz)
        _ = 2 / z.re := by ring)
  obtain ⟨o1, o2⟩ := sd3_opNorm_re_im_le (Rres A (-z) - Rres A' (-z))
  have hxk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hx : 0 < z.re := hz
  constructor
  · refine (nuc_le_rank_mul_opNorm _).trans ?_
    have h1 : (((Rres A (-z) - Rres A' (-z)).map Complex.re).rank : ℝ) ≤ 4 * k := by
      exact_mod_cast hr
    calc _ ≤ (4 * (k : ℝ)) * (2 / z.re) :=
          mul_le_mul h1 (o1.trans ho) (by unfold opNorm; exact norm_nonneg _) (by positivity)
      _ = 8 * k / z.re := by ring
  · refine (nuc_le_rank_mul_opNorm _).trans ?_
    have h1 : (((Rres A (-z) - Rres A' (-z)).map Complex.im).rank : ℝ) ≤ 4 * k := by
      exact_mod_cast hi
    calc _ ≤ (4 * (k : ℝ)) * (2 / z.re) :=
          mul_le_mul h1 (o2.trans ho) (by unfold opNorm; exact norm_nonneg _) (by positivity)
      _ = 8 * k / z.re := by ring

private lemma sd3_nuc_Dt {a b : ℕ} (A A' : Mat a b) (z : ℂ) (hz : 0 < z.re) (k : ℕ)
    (hk : (A - A').rank ≤ k) :
    nuc ((Rtil A (-z) - Rtil A' (-z)).map Complex.re) ≤ 8 * k / z.re ∧
    nuc ((Rtil A (-z) - Rtil A' (-z)).map Complex.im) ≤ 8 * k / z.re := by
  have := sd3_nuc_D Aᵀ A'ᵀ z hz k (by rw [← Matrix.transpose_sub, Matrix.rank_transpose]; exact hk)
  rwa [sd1_Rtil_eq, sd1_Rtil_eq]

private lemma sd3_nuc_E {a b : ℕ} (A A' : Mat a b) (z : ℂ) (hz : 0 < z.re) (k : ℕ)
    (hk : (A - A').rank ≤ k) :
    nuc ((XzC A z - XzC A' z).map Complex.re) ≤ 5 * k / Real.sqrt z.re ∧
    nuc ((XzC A z - XzC A' z).map Complex.im) ≤ 5 * k / Real.sqrt z.re := by
  obtain ⟨hr, hi⟩ := sd3_rank_E A A' z hz k hk
  have hsq : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hz
  have ho : opNorm (XzC A z - XzC A' z) ≤ 1 / Real.sqrt z.re :=
    (sd3_opNorm_sub _ _).trans (by
      calc _ ≤ 1 / (2 * Real.sqrt z.re) + 1 / (2 * Real.sqrt z.re) :=
            add_le_add (sd0_X_bound A z hz) (sd0_X_bound A' z hz)
        _ = 1 / Real.sqrt z.re := by field_simp; ring)
  obtain ⟨o1, o2⟩ := sd3_opNorm_re_im_le (XzC A z - XzC A' z)
  have hxk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  constructor
  · refine (nuc_le_rank_mul_opNorm _).trans ?_
    have h1 : (((XzC A z - XzC A' z).map Complex.re).rank : ℝ) ≤ 5 * k := by
      exact_mod_cast hr
    calc _ ≤ (5 * (k : ℝ)) * (1 / Real.sqrt z.re) :=
          mul_le_mul h1 (o1.trans ho) (by unfold opNorm; exact norm_nonneg _) (by positivity)
      _ = 5 * k / Real.sqrt z.re := by ring
  · refine (nuc_le_rank_mul_opNorm _).trans ?_
    have h1 : (((XzC A z - XzC A' z).map Complex.im).rank : ℝ) ≤ 5 * k := by
      exact_mod_cast hi
    calc _ ≤ (5 * (k : ℝ)) * (1 / Real.sqrt z.re) :=
          mul_le_mul h1 (o2.trans ho) (by unfold opNorm; exact norm_nonneg _) (by positivity)
      _ = 5 * k / Real.sqrt z.re := by ring

open scoped Matrix.Norms.L2Operator in
private lemma sd3r_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]


open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- `‖r_out‖² = ‖Σ_out‖` for the regularized square root `r_out`. -/
private lemma sd3r_opNorm_rOut_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

open scoped Matrix.Norms.L2Operator MatrixOrder in
/-- The `r_in` analogue of `sd3r_opNorm_rOut_mul_self`. -/
private lemma sd3r_opNorm_rIn_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm


private lemma sd3r_opNorm_one (d : ℕ) : opNorm (1 : Mat d d) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

private lemma sd3r_fro_sq_eq_trace {k l : ℕ} (A : Mat k l) : fro A ^ 2 = (Aᵀ * A).trace := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, abs_mul_abs_self, sq]
  rw [Finset.sum_comm]

private lemma sd3r_fro_le_nuc {k l : ℕ} (A : Mat k l) : fro A ≤ nuc A := by
  have h1 := trace_mul_le_opNorm_mul_nuc Aᵀ A
  have h2 := opNorm_le_nuc A
  rw [sd3r_opNorm_transpose] at h1
  have h0 : 0 ≤ fro A := Real.sqrt_nonneg _
  have h3 : fro A ^ 2 ≤ nuc A ^ 2 := by
    rw [sd3r_fro_sq_eq_trace]
    calc _ ≤ |(Aᵀ * A).trace| := le_abs_self _
      _ ≤ opNorm A * nuc A := h1
      _ ≤ nuc A * nuc A := mul_le_mul_of_nonneg_right h2 (nuc_nonneg A)
      _ = nuc A ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ h0 (nuc_nonneg A) two_ne_zero).mp h3

private lemma sd3r_trace_le_nuc {d : ℕ} (A : Mat d d) : |A.trace| ≤ nuc A := by
  have h1 := trace_mul_le_opNorm_mul_nuc (1 : Mat d d) A
  rw [Matrix.one_mul] at h1
  exact h1.trans (by
    calc opNorm (1 : Mat d d) * nuc A ≤ 1 * nuc A :=
          mul_le_mul_of_nonneg_right (sd3r_opNorm_one d) (nuc_nonneg A)
      _ = nuc A := one_mul _)

/-- symmetrization -/
private lemma sd3r_sym_nuc {d : ℕ} (D : Mat d d) : nuc ((1 / 2 : ℝ) • (D + Dᵀ)) ≤ nuc D := by
  rw [nuc_smul]
  have := nuc_add_le D Dᵀ
  rw [nuc_transpose] at this
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  linarith

private lemma sd3r_quad_eq {d : ℕ} (D : Mat d d) (z : Vec d) :
    dotProduct z (D *ᵥ z) = dotProduct z (((1 / 2 : ℝ) • (D + Dᵀ)) *ᵥ z) := by
  have h : dotProduct z (Dᵀ *ᵥ z) = dotProduct z (D *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, h]
  simp only [smul_eq_mul]
  ring

private lemma sd3r_quad_sq {d : ℕ} (D : Mat d d) :
    Integrable (fun z : Vec d => (dotProduct z (D *ᵥ z)) ^ 2) (Muon.Foundations.stdGaussianPi d) ∧
    ∫ z, (dotProduct z (D *ᵥ z)) ^ 2 ∂(Muon.Foundations.stdGaussianPi d) ≤ 3 * nuc D ^ 2 := by
  obtain ⟨Ds, hDs⟩ : ∃ Ds : Mat d d, Ds = (1 / 2 : ℝ) • (D + Dᵀ) := ⟨_, rfl⟩
  have hsymm : Ds.IsSymm := by
    unfold Matrix.IsSymm
    rw [hDs, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hQe : ∀ z : Vec d, dotProduct z (D *ᵥ z) = dotProduct z (Ds *ᵥ z) := by
    intro z; rw [hDs]; exact sd3r_quad_eq D z
  have e : ∀ z : Vec d, dotProduct z (Ds *ᵥ z) = ∑ i, ∑ j, Ds i j * (z i * z j) := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hmem : MemLp (fun z : Vec d => dotProduct z (Ds *ᵥ z)) 2
      (Muon.Foundations.stdGaussianPi d) := by
    have e' : (fun z : Vec d => dotProduct z (Ds *ᵥ z)) =
        fun z => ∑ i, ∑ j, Ds i j * (z i * z j) := funext e
    rw [e']
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    refine MemLp.const_mul ?_ _
    have hm : Measurable (fun z : Vec d => z i * z j) := by fun_prop
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    have := sd2b_gfour i j i j
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring
  have hsq := hmem.integrable_sq
  have hQ : (fun z : Vec d => (dotProduct z (D *ᵥ z)) ^ 2) =
      fun z => (dotProduct z (Ds *ᵥ z)) ^ 2 := by
    funext z; rw [hQe]
  rw [hQ]
  refine ⟨hsq, ?_⟩
  have hvar := lem_app_de_moments_v Ds hsymm
  have hmean := lem_app_de_moments_iv Ds hsymm
  rw [variance_eq_sub hmem, hmean] at hvar
  have h1 : ∫ z, (dotProduct z (Ds *ᵥ z)) ^ 2 ∂(Muon.Foundations.stdGaussianPi d) =
      2 * fro Ds ^ 2 + Ds.trace ^ 2 := by
    have : (fun z : Vec d => dotProduct z (Ds *ᵥ z)) ^ 2 = fun z => (dotProduct z (Ds *ᵥ z)) ^ 2 := by
      funext z; simp
    rw [this] at hvar
    linarith
  rw [h1]
  have hn : nuc Ds ≤ nuc D := by rw [hDs]; exact sd3r_sym_nuc D
  have hf := sd3r_fro_le_nuc Ds
  have ht := sd3r_trace_le_nuc Ds
  have hf2 : fro Ds ^ 2 ≤ nuc D ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (hf.trans hn) 2
  have ht2 : Ds.trace ^ 2 ≤ nuc D ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (ht.trans hn) 2
  linarith

private lemma sd3r_bil_inner {m n : ℕ} (E : Mat m n) (z : Vec m) :
    ∫ w, (dotProduct z (E *ᵥ w)) ^ 2 ∂(Muon.Foundations.stdGaussianPi n) =
      ∑ j, (∑ i, z i * E i j) ^ 2 := by
  have e1 : ∀ w : Vec n, (dotProduct z (E *ᵥ w)) ^ 2 =
      ∑ j, ∑ l, w j * (Matrix.of (fun a b : Fin n => (∑ i, z i * E i a) * (∑ i, z i * E i b))) j l * w l := by
    intro w
    have h1 : dotProduct z (E *ᵥ w) = ∑ j, (∑ i, z i * E i j) * w j := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.of_apply]; ring
  simp_rw [e1]
  rw [Muon.Foundations.stdGaussianPi_quadratic_mean n]
  simp [Matrix.trace, sq]

private lemma sd3r_bil_outer {m n : ℕ} (E : Mat m n) :
    ∫ z, ∑ j, (∑ i, z i * E i j) ^ 2 ∂(Muon.Foundations.stdGaussianPi m) = fro E ^ 2 := by
  have e1 : ∀ z : Vec m, ∑ j, (∑ i, z i * E i j) ^ 2 =
      ∑ i, ∑ k, z i * (E * Eᵀ) i k * z k := by
    intro z
    simp only [sq, Finset.sum_mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e1]
  rw [Muon.Foundations.stdGaussianPi_quadratic_mean m, sd3r_fro_sq_eq_trace, Matrix.trace_mul_comm]

private lemma sd3r_bil_sq {m n : ℕ} (E : Mat m n) :
    Integrable (fun x : Vec m × Vec n => (dotProduct x.1 (E *ᵥ x.2)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct x.1 (E *ᵥ x.2)) ^ 2 ∂(gaussPair m n) ≤ nuc E ^ 2 := by
  have e : ∀ x : Vec m × Vec n, dotProduct x.1 (E *ᵥ x.2) = ∑ i, ∑ j, E i j * (x.1 i * x.2 j) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hmem : MemLp (fun x : Vec m × Vec n => dotProduct x.1 (E *ᵥ x.2)) 2 (gaussPair m n) := by
    have e' : (fun x : Vec m × Vec n => dotProduct x.1 (E *ᵥ x.2)) =
        fun x => ∑ i, ∑ j, E i j * (x.1 i * x.2 j) := funext e
    rw [e']
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    exact MemLp.const_mul (sd2b_gfam1_memLp m n (i, j)) _
  have hint := hmem.integrable_sq
  refine ⟨hint, ?_⟩
  have hprod : ∫ x, (dotProduct x.1 (E *ᵥ x.2)) ^ 2 ∂(gaussPair m n) =
      ∫ z, ∫ w, (dotProduct z (E *ᵥ w)) ^ 2 ∂(Muon.Foundations.stdGaussianPi n)
        ∂(Muon.Foundations.stdGaussianPi m) := by
    unfold gaussPair
    exact integral_prod (fun x : Vec m × Vec n => (dotProduct x.1 (E *ᵥ x.2)) ^ 2) hint
  rw [hprod]
  simp_rw [sd3r_bil_inner]
  rw [sd3r_bil_outer]
  have := sd3r_fro_le_nuc E
  have h0 : 0 ≤ fro E := Real.sqrt_nonneg _
  exact pow_le_pow_left₀ h0 this 2

private lemma sd3r_fst_map (m n : ℕ) :
    (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
  unfold gaussPair
  rw [Measure.map_fst_prod]; simp

private lemma sd3r_snd_map (m n : ℕ) :
    (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
  unfold gaussPair
  rw [Measure.map_snd_prod]; simp

private lemma sd3r_fst_transfer {m n : ℕ} (φ : Vec m → ℝ) (hφ : Measurable φ)
    (h : Integrable φ (Muon.Foundations.stdGaussianPi m)) :
    Integrable (fun x : Vec m × Vec n => φ x.1) (gaussPair m n) ∧
      ∫ x, φ x.1 ∂(gaussPair m n) = ∫ z, φ z ∂(Muon.Foundations.stdGaussianPi m) := by
  have hm : Measurable (Prod.fst : Vec m × Vec n → Vec m) := measurable_fst
  have h' : Integrable φ ((gaussPair m n).map Prod.fst) := by rw [sd3r_fst_map]; exact h
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).mp h', ?_⟩
  rw [← sd3r_fst_map m n]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

private lemma sd3r_snd_transfer {m n : ℕ} (φ : Vec n → ℝ) (hφ : Measurable φ)
    (h : Integrable φ (Muon.Foundations.stdGaussianPi n)) :
    Integrable (fun x : Vec m × Vec n => φ x.2) (gaussPair m n) ∧
      ∫ x, φ x.2 ∂(gaussPair m n) = ∫ z, φ z ∂(Muon.Foundations.stdGaussianPi n) := by
  have hm : Measurable (Prod.snd : Vec m × Vec n → Vec n) := measurable_snd
  have h' : Integrable φ ((gaussPair m n).map Prod.snd) := by rw [sd3r_snd_map]; exact h
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).mp h', ?_⟩
  rw [← sd3r_snd_map m n]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

private lemma sd3r_dot_mulVec {a b : ℕ} (R : Mat a b) (z : Vec b) (y : Vec a) :
    dotProduct (R *ᵥ z) y = dotProduct z (Rᵀ *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- scaled quadratic form: `uᵀ D u = zᵀ ((1/B) Rᵀ D R) z`. -/
private lemma sd3r_quad_scaled {a : ℕ} (c : ℝ) (R D : Mat a a) (z : Vec a) :
    dotProduct (c • (R *ᵥ z)) (D *ᵥ (c • (R *ᵥ z))) =
      dotProduct z (((c * c) • (Rᵀ * D * R)) *ᵥ z) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sd3r_dot_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [smul_eq_mul]
  ring

private lemma sd3r_nuc_scaled {a : ℕ} (c : ℝ) (R D : Mat a a) :
    nuc ((c * c) • (Rᵀ * D * R)) ≤ (c * c) * (opNorm R * opNorm R * nuc D) := by
  rw [nuc_smul, abs_of_nonneg (mul_self_nonneg c)]
  have := nuc_mul_three_le Rᵀ D R
  rw [sd3r_opNorm_transpose] at this
  exact mul_le_mul_of_nonneg_left (this.trans_eq (by ring)) (mul_self_nonneg c)

private lemma sd3r_L2U {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSo : opNorm C.Sout ≤ CS) (D : Mat m m) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2 ∂(gaussPair m n) ≤
      3 * (CS / B * nuc D) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat m m := (c * c) • ((rOut C)ᵀ * D * rOut C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2 = (dotProduct x.1 (F *ᵥ x.1)) ^ 2 := by
    intro x
    unfold momU
    rw [hF, sd3r_quad_scaled]
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := sd3r_quad_sq F
  have hmeas : Measurable (fun z : Vec m => (dotProduct z (F *ᵥ z)) ^ 2) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  obtain ⟨hI2, hV2⟩ := sd3r_fst_transfer (n := n) _ hmeas hI
  refine ⟨hI2, ?_⟩
  rw [hV2]
  refine hV.trans ?_
  have hn : nuc F ≤ CS / B * nuc D := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rOut C) * opNorm (rOut C) * nuc D) :=
      sd3r_nuc_scaled c (rOut C) D
    rw [sd3r_opNorm_rOut_mul_self, hcc] at h1
    refine h1.trans ?_
    have hD := nuc_nonneg D
    calc (B : ℝ)⁻¹ * (opNorm C.Sout * nuc D) ≤ (B : ℝ)⁻¹ * (CS * nuc D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSo hD) (by positivity)
      _ = CS / B * nuc D := by field_simp
  have h0 := nuc_nonneg F
  have := pow_le_pow_left₀ h0 hn 2
  linarith

private lemma sd3r_L2V {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSi : opNorm C.Sin ≤ CS) (D : Mat n n) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) ≤
      3 * (CS / B * nuc D) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat n n := (c * c) • ((rIn C)ᵀ * D * rIn C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2 = (dotProduct x.2 (F *ᵥ x.2)) ^ 2 := by
    intro x
    unfold momV
    rw [hF, sd3r_quad_scaled]
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := sd3r_quad_sq F
  have hmeas : Measurable (fun z : Vec n => (dotProduct z (F *ᵥ z)) ^ 2) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  obtain ⟨hI2, hV2⟩ := sd3r_snd_transfer (m := m) _ hmeas hI
  refine ⟨hI2, ?_⟩
  rw [hV2]
  refine hV.trans ?_
  have hn : nuc F ≤ CS / B * nuc D := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rIn C) * opNorm (rIn C) * nuc D) :=
      sd3r_nuc_scaled c (rIn C) D
    rw [sd3r_opNorm_rIn_mul_self, hcc] at h1
    refine h1.trans ?_
    have hD := nuc_nonneg D
    calc (B : ℝ)⁻¹ * (opNorm C.Sin * nuc D) ≤ (B : ℝ)⁻¹ * (CS * nuc D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSi hD) (by positivity)
      _ = CS / B * nuc D := by field_simp
  have h0 := nuc_nonneg F
  have := pow_le_pow_left₀ h0 hn 2
  linarith

private lemma sd3r_nuc_scaled_rect {a b : ℕ} (c : ℝ) (R : Mat a a) (E : Mat a b) (R' : Mat b b) :
    nuc ((c * c) • (Rᵀ * E * R')) ≤ (c * c) * (opNorm R * nuc E * opNorm R') := by
  rw [nuc_smul, abs_of_nonneg (mul_self_nonneg c)]
  have := nuc_mul_three_le Rᵀ E R'
  rw [sd3r_opNorm_transpose] at this
  exact mul_le_mul_of_nonneg_left this (mul_self_nonneg c)

private lemma sd3r_L2C {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS) (E : Mat m n) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) ≤
      (CS / B * nuc E) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat m n := (c * c) • ((rOut C)ᵀ * E * rIn C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2 = (dotProduct x.1 (F *ᵥ x.2)) ^ 2 := by
    intro x
    unfold momU momV
    rw [hF, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, sd3r_dot_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [smul_eq_mul]
    congr 1
    ring
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := sd3r_bil_sq F
  refine ⟨hI, hV.trans ?_⟩
  have hn : nuc F ≤ CS / B * nuc E := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rOut C) * nuc E * opNorm (rIn C)) :=
      sd3r_nuc_scaled_rect c (rOut C) E (rIn C)
    rw [hcc] at h1
    refine h1.trans ?_
    have hE := nuc_nonneg E
    have ho1 : 0 ≤ opNorm (rOut C) := by unfold opNorm; exact norm_nonneg _
    have ho2 : 0 ≤ opNorm (rIn C) := by unfold opNorm; exact norm_nonneg _
    have hCS : 0 ≤ CS := by
      have := mul_self_nonneg (opNorm (rOut C))
      rw [sd3r_opNorm_rOut_mul_self] at this
      exact le_trans (by unfold opNorm; exact norm_nonneg _) hSo
    have hprod : opNorm (rOut C) * opNorm (rIn C) ≤ CS := by
      have hsq : (opNorm (rOut C) * opNorm (rIn C)) ^ 2 ≤ CS ^ 2 := by
        have e : (opNorm (rOut C) * opNorm (rIn C)) ^ 2 =
            (opNorm (rOut C) * opNorm (rOut C)) * (opNorm (rIn C) * opNorm (rIn C)) := by ring
        rw [e, sd3r_opNorm_rOut_mul_self, sd3r_opNorm_rIn_mul_self, sq]
        exact mul_le_mul hSo hSi (by unfold opNorm; exact norm_nonneg _) hCS
      exact (pow_le_pow_iff_left₀ (mul_nonneg ho1 ho2) hCS two_ne_zero).mp hsq
    calc (B : ℝ)⁻¹ * (opNorm (rOut C) * nuc E * opNorm (rIn C))
        = (B : ℝ)⁻¹ * (opNorm (rOut C) * opNorm (rIn C)) * nuc E := by ring
      _ ≤ (B : ℝ)⁻¹ * CS * nuc E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) hE
      _ = CS / B * nuc E := by field_simp
  have h0 := nuc_nonneg F
  exact pow_le_pow_left₀ h0 hn 2


private lemma sd3_g_abs {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS)
    (Du Di : Mat m m) (Vr Vi : Mat n n) (Er Ei : Mat m n) (a e : ℝ)
    (h1 : nuc Du ≤ a) (h2 : nuc Di ≤ a) (h3 : nuc Vr ≤ a) (h4 : nuc Vi ≤ a)
    (h5 : nuc Er ≤ e) (h6 : nuc Ei ≤ e) :
    MemLp (fun x : Vec m × Vec n =>
      |dotProduct (momU C B x) (Du *ᵥ momU C B x)| + |dotProduct (momU C B x) (Di *ᵥ momU C B x)|
      + |dotProduct (momV C B x) (Vr *ᵥ momV C B x)| + |dotProduct (momV C B x) (Vi *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Er *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Ei *ᵥ momV C B x)|) 2 (gaussPair m n) ∧
    ∫ x, (|dotProduct (momU C B x) (Du *ᵥ momU C B x)| +
      |dotProduct (momU C B x) (Di *ᵥ momU C B x)|
      + |dotProduct (momV C B x) (Vr *ᵥ momV C B x)| + |dotProduct (momV C B x) (Vi *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Er *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Ei *ᵥ momV C B x)|) ^ 2 ∂(gaussPair m n) ≤
      6 * (3 * (CS / B * a) ^ 2 + 3 * (CS / B * a) ^ 2 + 3 * (CS / B * a) ^ 2 +
        3 * (CS / B * a) ^ 2 + (CS / B * e) ^ 2 + (CS / B * e) ^ 2) := by
  have hUc : Continuous (momU C B) := by unfold momU; fun_prop
  have hVc : Continuous (momV C B) := by unfold momV; fun_prop
  obtain ⟨I1, V1⟩ := sd3r_L2U C hB CS hSo Du
  obtain ⟨I2, V2⟩ := sd3r_L2U C hB CS hSo Di
  obtain ⟨I3, V3⟩ := sd3r_L2V C hB CS hSi Vr
  obtain ⟨I4, V4⟩ := sd3r_L2V C hB CS hSi Vi
  obtain ⟨I5, V5⟩ := sd3r_L2C C hB CS hSo hSi Er
  obtain ⟨I6, V6⟩ := sd3r_L2C C hB CS hSo hSi Ei
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := le_trans (by unfold opNorm; exact norm_nonneg _) hSo
  have c0 : 0 ≤ CS / B := by positivity
  have m1 : Measurable (fun x : Vec m × Vec n => dotProduct (momU C B x) (Du *ᵥ momU C B x)) := by
    have := hUc; unfold dotProduct Matrix.mulVec; fun_prop
  have m2 : Measurable (fun x : Vec m × Vec n => dotProduct (momU C B x) (Di *ᵥ momU C B x)) := by
    have := hUc; unfold dotProduct Matrix.mulVec; fun_prop
  have m3 : Measurable (fun x : Vec m × Vec n => dotProduct (momV C B x) (Vr *ᵥ momV C B x)) := by
    have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have m4 : Measurable (fun x : Vec m × Vec n => dotProduct (momV C B x) (Vi *ᵥ momV C B x)) := by
    have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have m5 : Measurable (fun x : Vec m × Vec n => dotProduct (momU C B x) (Er *ᵥ momV C B x)) := by
    have := hUc; have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have m6 : Measurable (fun x : Vec m × Vec n => dotProduct (momU C B x) (Ei *ᵥ momV C B x)) := by
    have := hUc; have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have l1 := (memLp_two_iff_integrable_sq m1.aestronglyMeasurable).mpr I1
  have l2 := (memLp_two_iff_integrable_sq m2.aestronglyMeasurable).mpr I2
  have l3 := (memLp_two_iff_integrable_sq m3.aestronglyMeasurable).mpr I3
  have l4 := (memLp_two_iff_integrable_sq m4.aestronglyMeasurable).mpr I4
  have l5 := (memLp_two_iff_integrable_sq m5.aestronglyMeasurable).mpr I5
  have l6 := (memLp_two_iff_integrable_sq m6.aestronglyMeasurable).mpr I6
  have hL := ((((l1.abs.add l2.abs).add l3.abs).add l4.abs).add l5.abs).add l6.abs
  refine ⟨hL, ?_⟩
  have key : ∀ a1 a2 a3 a4 a5 a6 : ℝ, (a1 + a2 + a3 + a4 + a5 + a6) ^ 2 ≤
      6 * (a1 ^ 2 + a2 ^ 2 + a3 ^ 2 + a4 ^ 2 + a5 ^ 2 + a6 ^ 2) := by
    intro a1 a2 a3 a4 a5 a6
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin 6)))
      (f := ![a1, a2, a3, a4, a5, a6])
    simpa [Fin.sum_univ_succ, add_assoc] using this
  have hsq : ∀ x : Vec m × Vec n,
      (|dotProduct (momU C B x) (Du *ᵥ momU C B x)| + |dotProduct (momU C B x) (Di *ᵥ momU C B x)|
      + |dotProduct (momV C B x) (Vr *ᵥ momV C B x)| + |dotProduct (momV C B x) (Vi *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Er *ᵥ momV C B x)|
      + |dotProduct (momU C B x) (Ei *ᵥ momV C B x)|) ^ 2 ≤
      6 * ((dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Er *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Ei *ᵥ momV C B x)) ^ 2) := by
    intro x
    have := key |dotProduct (momU C B x) (Du *ᵥ momU C B x)|
      |dotProduct (momU C B x) (Di *ᵥ momU C B x)| |dotProduct (momV C B x) (Vr *ᵥ momV C B x)|
      |dotProduct (momV C B x) (Vi *ᵥ momV C B x)| |dotProduct (momU C B x) (Er *ᵥ momV C B x)|
      |dotProduct (momU C B x) (Ei *ᵥ momV C B x)|
    simpa only [sq_abs] using this
  have hsumI : Integrable (fun x : Vec m × Vec n =>
      6 * ((dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Er *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Ei *ᵥ momV C B x)) ^ 2)) (gaussPair m n) :=
    (((((I1.add I2).add I3).add I4).add I5).add I6).const_mul 6
  have hgI := hL.integrable_sq
  calc _ ≤ ∫ x, 6 * ((dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Er *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) (Ei *ᵥ momV C B x)) ^ 2) ∂(gaussPair m n) :=
        integral_mono hgI hsumI hsq
    _ = 6 * (∫ x, (dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momU C B x) (Er *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momU C B x) (Ei *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n)) := by
        have hS2 : Integrable (fun x : Vec m × Vec n =>
            (dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2) (gaussPair m n) := I1.add I2
        have hS3 : Integrable (fun x : Vec m × Vec n =>
            (dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2) (gaussPair m n) := hS2.add I3
        have hS4 : Integrable (fun x : Vec m × Vec n =>
            (dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 +
            (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2) (gaussPair m n) := hS3.add I4
        have hS5 : Integrable (fun x : Vec m × Vec n =>
            (dotProduct (momU C B x) (Du *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momU C B x) (Di *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momV C B x) (Vr *ᵥ momV C B x)) ^ 2 +
            (dotProduct (momV C B x) (Vi *ᵥ momV C B x)) ^ 2 +
            (dotProduct (momU C B x) (Er *ᵥ momV C B x)) ^ 2) (gaussPair m n) := hS4.add I5
        rw [integral_const_mul, integral_add hS5 I6, integral_add hS4 I5, integral_add hS3 I4,
          integral_add hS2 I3, integral_add I1 I2]
    _ ≤ _ := by
        have b1 : 3 * (CS / B * nuc Du) ^ 2 ≤ 3 * (CS / B * a) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left h1 c0) 2) (by norm_num)
        have b2 : 3 * (CS / B * nuc Di) ^ 2 ≤ 3 * (CS / B * a) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left h2 c0) 2) (by norm_num)
        have b3 : 3 * (CS / B * nuc Vr) ^ 2 ≤ 3 * (CS / B * a) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left h3 c0) 2) (by norm_num)
        have b4 : 3 * (CS / B * nuc Vi) ^ 2 ≤ 3 * (CS / B * a) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left h4 c0) 2) (by norm_num)
        have b5 : (CS / B * nuc Er) ^ 2 ≤ (CS / B * e) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _)) (mul_le_mul_of_nonneg_left h5 c0) 2
        have b6 : (CS / B * nuc Ei) ^ 2 ≤ (CS / B * e) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _)) (mul_le_mul_of_nonneg_left h6 c0) 2
        linarith

private lemma sd3_dL (N q A a : ℝ) (h z U U' V V' C C' Λ Λ' : ℂ)
    (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hΛ : Λ = (1 + h * C) ^ 2 + z * h ^ 2 * U * V)
    (hΛ' : Λ' = (1 + h * C') ^ 2 + z * h ^ 2 * U' * V')
    (ha0 : 0 ≤ a) (hA1 : 1 ≤ A) (haA : a ≤ A) (hNA : N ≤ A) (hha : ‖h‖ ≤ a)
    (hzU' : ‖z‖ * ‖U'‖ ≤ 2 * N) (hzV : ‖z‖ * ‖V‖ ≤ 2 * N)
    (hC : ‖C‖ ≤ q * N) (hC' : ‖C'‖ ≤ q * N) :
    ‖Λ - Λ'‖ ≤ A ^ 3 * (2 + 2 * q) * (‖U - U'‖ + ‖V - V'‖ + ‖C - C'‖) := by
  have hX0 := norm_nonneg (U - U')
  have hY0 := norm_nonneg (V - V')
  have hZ0 := norm_nonneg (C - C')
  have hid2 : Λ - Λ' = h * (C - C') * (2 + h * (C + C')) +
      z * h ^ 2 * (V * (U - U') + U' * (V - V')) := by
    rw [hΛ, hΛ']; ring
  have hCC : ‖C + C'‖ ≤ 2 * q * N := by
    calc ‖C + C'‖ ≤ ‖C‖ + ‖C'‖ := norm_add_le _ _
      _ ≤ 2 * q * N := by linarith
  rw [hid2]
  have t1 : ‖h * (C - C') * (2 + h * (C + C'))‖ ≤ A * (2 + 2 * q * A ^ 2) * ‖C - C'‖ := by
    rw [norm_mul, norm_mul]
    have e1 : ‖2 + h * (C + C')‖ ≤ 2 + 2 * q * A ^ 2 := by
      calc ‖2 + h * (C + C')‖ ≤ ‖(2 : ℂ)‖ + ‖h * (C + C')‖ := norm_add_le _ _
        _ ≤ 2 + 2 * q * A ^ 2 := by
          rw [norm_mul]
          have : ‖h‖ * ‖C + C'‖ ≤ a * (2 * q * N) :=
            mul_le_mul hha hCC (norm_nonneg _) ha0
          have haN : a * N ≤ A ^ 2 := by
            have := mul_le_mul haA hNA hN (by linarith)
            rw [sq]; exact this
          have h2 : a * (2 * q * N) ≤ 2 * q * A ^ 2 := by
            calc a * (2 * q * N) = (2 * q) * (a * N) := by ring
              _ ≤ (2 * q) * A ^ 2 := mul_le_mul_of_nonneg_left haN (by positivity)
          have h3 : ‖(2 : ℂ)‖ = 2 := by simp
          rw [h3]
          linarith
    calc ‖h‖ * ‖C - C'‖ * ‖2 + h * (C + C')‖ ≤ A * ‖C - C'‖ * (2 + 2 * q * A ^ 2) := by
          apply mul_le_mul (mul_le_mul (hha.trans haA) le_rfl hZ0 (by linarith)) e1
            (norm_nonneg _) (by positivity)
      _ = A * (2 + 2 * q * A ^ 2) * ‖C - C'‖ := by ring
  have t2 : ‖z * h ^ 2 * (V * (U - U') + U' * (V - V'))‖ ≤ 2 * A ^ 3 * (‖U - U'‖ + ‖V - V'‖) := by
    have hh3 : ‖h‖ ^ 2 ≤ A ^ 2 := by
      calc ‖h‖ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hha 2
        _ ≤ A ^ 2 := pow_le_pow_left₀ ha0 haA 2
    have e2 : ‖z * h ^ 2 * (V * (U - U') + U' * (V - V'))‖ ≤
        ‖h‖ ^ 2 * (2 * N * (‖U - U'‖ + ‖V - V'‖)) := by
      calc ‖z * h ^ 2 * (V * (U - U') + U' * (V - V'))‖
          = ‖h‖ ^ 2 * ‖z * (V * (U - U') + U' * (V - V'))‖ := by
            rw [show z * h ^ 2 * (V * (U - U') + U' * (V - V')) =
              h ^ 2 * (z * (V * (U - U') + U' * (V - V'))) by ring, norm_mul, norm_pow]
        _ ≤ ‖h‖ ^ 2 * (‖z * V‖ * ‖U - U'‖ + ‖z * U'‖ * ‖V - V'‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            calc ‖z * (V * (U - U') + U' * (V - V'))‖
                = ‖z * V * (U - U') + z * U' * (V - V')‖ := by ring_nf
              _ ≤ ‖z * V * (U - U')‖ + ‖z * U' * (V - V')‖ := norm_add_le _ _
              _ = _ := by rw [norm_mul (z * V), norm_mul (z * U')]
        _ ≤ ‖h‖ ^ 2 * (2 * N * ‖U - U'‖ + 2 * N * ‖V - V'‖) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [norm_mul, norm_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hzV hX0)
              (mul_le_mul_of_nonneg_right hzU' hY0)
        _ = ‖h‖ ^ 2 * (2 * N * (‖U - U'‖ + ‖V - V'‖)) := by ring
    calc _ ≤ ‖h‖ ^ 2 * (2 * N * (‖U - U'‖ + ‖V - V'‖)) := e2
      _ ≤ A ^ 2 * (2 * N * (‖U - U'‖ + ‖V - V'‖)) :=
          mul_le_mul_of_nonneg_right hh3 (by positivity)
      _ ≤ 2 * A ^ 3 * (‖U - U'‖ + ‖V - V'‖) := by
          have : A ^ 2 * N ≤ A ^ 3 := by
            rw [pow_succ]; exact mul_le_mul_of_nonneg_left hNA (by positivity)
          calc A ^ 2 * (2 * N * (‖U - U'‖ + ‖V - V'‖)) =
              (2 * (A ^ 2 * N)) * (‖U - U'‖ + ‖V - V'‖) := by ring
            _ ≤ (2 * A ^ 3) * (‖U - U'‖ + ‖V - V'‖) :=
              mul_le_mul_of_nonneg_right (by linarith) (add_nonneg hX0 hY0)
  calc _ ≤ ‖h * (C - C') * (2 + h * (C + C'))‖ +
        ‖z * h ^ 2 * (V * (U - U') + U' * (V - V'))‖ := norm_add_le _ _
    _ ≤ A * (2 + 2 * q * A ^ 2) * ‖C - C'‖ + 2 * A ^ 3 * (‖U - U'‖ + ‖V - V'‖) := add_le_add t1 t2
    _ ≤ A ^ 3 * (2 + 2 * q) * (‖U - U'‖ + ‖V - V'‖ + ‖C - C'‖) := by
        have hA3 : A ≤ A ^ 3 := le_self_pow₀ hA1 (by norm_num)
        have hq3 : A * (2 + 2 * q * A ^ 2) ≤ A ^ 3 * (2 + 2 * q) := by
          have e1 : A * (2 + 2 * q * A ^ 2) = 2 * A + 2 * q * A ^ 3 := by ring
          have e2 : A ^ 3 * (2 + 2 * q) = 2 * A ^ 3 + 2 * q * A ^ 3 := by ring
          rw [e1, e2]; linarith
        have h1 := mul_le_mul_of_nonneg_right hq3 hZ0
        have key : A ^ 3 * (2 + 2 * q) * (‖U - U'‖ + ‖V - V'‖ + ‖C - C'‖) -
            (A ^ 3 * (2 + 2 * q) * ‖C - C'‖ + 2 * A ^ 3 * (‖U - U'‖ + ‖V - V'‖)) =
            A ^ 3 * (2 * q) * (‖U - U'‖ + ‖V - V'‖) := by ring
        have key0 : 0 ≤ A ^ 3 * (2 * q) * (‖U - U'‖ + ‖V - V'‖) := by positivity
        linarith

set_option maxHeartbeats 800000 in
private lemma sd3_alg (s0 x ϖ N q c1 a : ℝ) (h z U U' V V' C C' Λ Λ' : ℂ)
    (hs0 : 0 < s0) (hs : s0 ≤ x) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hc1 : 1 ≤ c1) (ha0 : 0 ≤ a) (hh : ‖h‖ ≤ ϖ * a)
    (hΛ : Λ = (1 + h * C) ^ 2 + z * h ^ 2 * U * V)
    (hΛ' : Λ' = (1 + h * C') ^ 2 + z * h ^ 2 * U' * V')
    (hΛ0 : Λ ≠ 0) (hΛ'0 : Λ' ≠ 0)
    (hΛi : ‖Λ‖⁻¹ ≤ (c1 * ((1 + a) * (1 + N))) ^ 2)
    (hΛ'i : ‖Λ'‖⁻¹ ≤ (c1 * ((1 + a) * (1 + N))) ^ 2)
    (hU' : x * ‖U'‖ ≤ N) (hV : x * ‖V‖ ≤ N) (hzn : ‖z‖ ≤ 2 * x)
    (hC : ‖C‖ ≤ q * N) (hC' : ‖C'‖ ≤ q * N) :
    ‖h ^ 2 * U / Λ - h ^ 2 * U' / Λ'‖ ≤
      ϖ ^ 2 * (c1 ^ 2 + c1 ^ 4 * (2 + 2 * q) / s0) * ((1 + a) * (1 + N)) ^ 10 *
        (‖U - U'‖ + ‖V - V'‖ + ‖C - C'‖) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + a) * (1 + N) := ⟨_, rfl⟩
  rw [← hA] at hΛi hΛ'i ⊢
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  have haA : a ≤ A := by rw [hA]; nlinarith
  have hNA : N ≤ A := by rw [hA]; nlinarith
  have hha : ‖h‖ ≤ a := hh.trans (mul_le_of_le_one_left ha0 hϖ1)
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = ‖U - U'‖ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = ‖V - V'‖ := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ‖C - C'‖ := ⟨_, rfl⟩
  rw [← hX, ← hY, ← hZ]
  have hX0 : 0 ≤ X := by rw [hX]; exact norm_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; exact norm_nonneg _
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact norm_nonneg _
  have hspos : 0 < x := lt_of_lt_of_le hs0 hs
  have hU'0 : ‖U'‖ ≤ N / s0 := by
    rw [le_div_iff₀ hs0]; nlinarith [norm_nonneg U']
  have hid1 : h ^ 2 * U / Λ - h ^ 2 * U' / Λ' =
      h ^ 2 * ((U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')) := by
    field_simp
    ring
  have hzU' : ‖z‖ * ‖U'‖ ≤ 2 * N := by
    calc ‖z‖ * ‖U'‖ ≤ (2 * x) * ‖U'‖ := mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ = 2 * (x * ‖U'‖) := by ring
      _ ≤ 2 * N := by linarith
  have hzV : ‖z‖ * ‖V‖ ≤ 2 * N := by
    calc ‖z‖ * ‖V‖ ≤ (2 * x) * ‖V‖ := mul_le_mul_of_nonneg_right hzn (norm_nonneg _)
      _ = 2 * (x * ‖V‖) := by ring
      _ ≤ 2 * N := by linarith
  have hdL : ‖Λ - Λ'‖ ≤ A ^ 3 * (2 + 2 * q) * (X + Y + Z) := by
    rw [hX, hY, hZ]
    exact sd3_dL N q A a h z U U' V V' C C' Λ Λ' hN hq hΛ hΛ' ha0 hA1 haA hNA hha hzU' hzV hC hC'
  rw [hid1, norm_mul, norm_pow]
  have hS0 : 0 ≤ X + Y + Z := by positivity
  have hLi0 : 0 ≤ ‖Λ‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hLi0' : 0 ≤ ‖Λ'‖⁻¹ := inv_nonneg.2 (norm_nonneg _)
  have hcA : 0 ≤ (c1 * A) ^ 2 := sq_nonneg _
  have hLp : 0 < ‖Λ‖ := norm_pos_iff.mpr hΛ0
  have hLp' : 0 < ‖Λ'‖ := norm_pos_iff.mpr hΛ'0
  have hT1 : ‖(U - U') / Λ‖ ≤ (c1 * A) ^ 2 * X := by
    rw [norm_div, div_eq_mul_inv, mul_comm, ← hX]
    exact mul_le_mul hΛi le_rfl hX0 hcA
  have hT2 : ‖U' * (Λ - Λ') / (Λ * Λ')‖ ≤ (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) := by
    rw [norm_div, div_eq_mul_inv, norm_mul, norm_mul, mul_inv]
    have : (‖Λ‖⁻¹ * ‖Λ'‖⁻¹) ≤ (c1 * A) ^ 2 * (c1 * A) ^ 2 :=
      mul_le_mul hΛi hΛ'i hLi0' hcA
    have h2 : ‖U'‖ * ‖Λ - Λ'‖ ≤ (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) :=
      mul_le_mul hU'0 hdL (norm_nonneg _) (by positivity)
    calc ‖U'‖ * ‖Λ - Λ'‖ * (‖Λ‖⁻¹ * ‖Λ'‖⁻¹) ≤
          ((N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z))) *
          ((c1 * A) ^ 2 * (c1 * A) ^ 2) :=
          mul_le_mul h2 this (by positivity) (by positivity)
      _ = _ := by ring
  have hsum : ‖(U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')‖ ≤
      (c1 * A) ^ 2 * X + (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) :=
    (norm_sub_le _ _).trans (add_le_add hT1 hT2)
  have hA8 : A ^ 2 ≤ A ^ 8 := pow_le_pow_right₀ hA1 (by norm_num)
  have hK1 : 0 ≤ c1 ^ 2 := by positivity
  have hK2 : 0 ≤ c1 ^ 4 * (2 + 2 * q) / s0 := by positivity
  have e1 : (c1 * A) ^ 2 * X ≤ c1 ^ 2 * A ^ 8 * (X + Y + Z) := by
    have : X ≤ X + Y + Z := by linarith
    calc (c1 * A) ^ 2 * X = (c1 ^ 2 * A ^ 2) * X := by ring
      _ ≤ (c1 ^ 2 * A ^ 8) * (X + Y + Z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA8 hK1) this hX0 (by positivity)
  have e2 : (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) * ((c1 * A) ^ 2 * (c1 * A) ^ 2) ≤
      (c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
    have hNA7 : N * A ^ 7 ≤ A ^ 8 := by
      rw [pow_succ A 7, mul_comm (A ^ 7) A]
      exact mul_le_mul_of_nonneg_right hNA (by positivity)
    calc (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) * ((c1 * A) ^ 2 * (c1 * A) ^ 2)
        = (c1 ^ 4 * (2 + 2 * q) / s0) * (N * A ^ 7) * (X + Y + Z) := by
          field_simp
      _ ≤ (c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
          apply mul_le_mul_of_nonneg_right _ hS0
          exact mul_le_mul_of_nonneg_left hNA7 hK2
  have hkey : (c1 * A) ^ 2 * X + (N / s0) * (A ^ 3 * (2 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) ≤
      (c1 ^ 2 + c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
    have := add_le_add e1 e2
    calc _ ≤ _ := this
      _ = _ := by ring
  have hT0 : 0 ≤ (c1 ^ 2 + c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by positivity
  calc ‖h‖ ^ 2 * ‖(U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')‖
      ≤ (ϖ ^ 2 * A ^ 2) * ((c1 ^ 2 + c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 8 * (X + Y + Z)) := by
        apply mul_le_mul _ (hsum.trans hkey) (norm_nonneg _) (by positivity)
        calc ‖h‖ ^ 2 ≤ (ϖ * a) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
          _ = ϖ ^ 2 * a ^ 2 := by ring
          _ ≤ ϖ ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 haA 2) (sq_nonneg _)
    _ = ϖ ^ 2 * (c1 ^ 2 + c1 ^ 4 * (2 + 2 * q) / s0) * A ^ 10 * (X + Y + Z) := by ring

private lemma sd3q_cast_euc_sq {k : ℕ} (u : Vec k) :
    ‖(EuclideanSpace.equiv (Fin k) ℂ).symm (fun i => (u i : ℂ))‖ ^ 2 = sqNorm u := by
  unfold sqNorm
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

private lemma sd3q_norm_dot {k : ℕ} (x y : Fin k → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖ *
      ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ := by
  calc
    ‖star x ⬝ᵥ y‖ = ‖inner ℂ ((EuclideanSpace.equiv (Fin k) ℂ).symm x)
        ((EuclideanSpace.equiv (Fin k) ℂ).symm y)‖ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    _ ≤ _ := norm_inner_le_norm _ _

open scoped Matrix.Norms.L2Operator in
private lemma sd3q_apply_bound {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (x : Fin b → ℂ) :
    ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (A *ᵥ x)‖ ≤
      opNorm A * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm x‖ := by
  rw [opNorm_eq_norm]
  exact Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin b) ℂ).symm x)

private lemma sd3q_quad_scalar_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (u : Vec k) (x : ℝ) (hx : 0 < x) (hA : opNorm A ≤ 1 / x) :
    ‖(fun i => (u i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (u i : ℂ))‖ ≤ sqNorm u / x := by
  let uc : Fin k → ℂ := fun i => (u i : ℂ)
  have hstar : star uc = uc := by funext i; simp [uc]
  have h1 := sd3q_norm_dot uc (A *ᵥ uc)
  rw [hstar] at h1
  have h2 := sd3q_apply_bound A uc
  have hnon : 0 ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖ := norm_nonneg _
  have hsq := sd3q_cast_euc_sq u
  change ‖uc ⬝ᵥ (A *ᵥ uc)‖ ≤ sqNorm u / x
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖ *
        ‖(EuclideanSpace.equiv (Fin k) ℂ).symm (A *ᵥ uc)‖ := h1
    _ ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖ *
        (opNorm A * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖) :=
      mul_le_mul_of_nonneg_left h2 hnon
    _ ≤ ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖ *
        ((1 / x) * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm uc‖) := by gcongr
    _ = sqNorm u / x := by rw [← hsq]; ring

private lemma sd3q_cross_scalar_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (u : Vec m) (v : Vec n) (x : ℝ) (hx : 0 < x)
    (hA : opNorm A ≤ 1 / (2 * Real.sqrt x)) :
    ‖(fun i => (u i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (v i : ℂ))‖ ≤
      (sqNorm u + sqNorm v) / (4 * Real.sqrt x) := by
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  have hstar : star uc = uc := by funext i; simp [uc]
  have h1 := sd3q_norm_dot uc (A *ᵥ vc)
  rw [hstar] at h1
  have h2 := sd3q_apply_bound A vc
  have heu : 0 ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ := norm_nonneg _
  have hev : 0 ≤ ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖ := norm_nonneg _
  have hsu := sd3q_cast_euc_sq u
  have hsv := sd3q_cast_euc_sq v
  have huv : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ *
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖ ≤ (sqNorm u + sqNorm v) / 2 := by
    nlinarith [sq_nonneg (‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ -
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖)]
  change ‖uc ⬝ᵥ (A *ᵥ vc)‖ ≤ _
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ *
        ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (A *ᵥ vc)‖ := h1
    _ ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ *
        (opNorm A * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖) :=
      mul_le_mul_of_nonneg_left h2 heu
    _ ≤ ‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ *
        ((1 / (2 * Real.sqrt x)) * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖) := by gcongr
    _ = (‖(EuclideanSpace.equiv (Fin m) ℂ).symm uc‖ *
        ‖(EuclideanSpace.equiv (Fin n) ℂ).symm vc‖) / (2 * Real.sqrt x) := by ring
    _ ≤ ((sqNorm u + sqNorm v) / 2) / (2 * Real.sqrt x) := by gcongr
    _ = (sqNorm u + sqNorm v) / (4 * Real.sqrt x) := by ring

private lemma sd3_pt {m n : ℕ} (K K' : Mat m n) (u : Vec m) (v : Vec n) (d ϖ : ℝ) (z : ℂ)
    (s0 : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ z.re) (hzS : |z.im| ≤ z.re / 2) (hϖ0 : 0 ≤ ϖ)
    (hϖ1 : ϖ ≤ 1) :
    ‖colAlpha2 (K.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z -
      colAlpha2 (K'.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖ ≤
    ϖ ^ 2 * ((1 + 1 / Real.sqrt s0) ^ 2 +
        (1 + 1 / Real.sqrt s0) ^ 4 * (2 + 2 * (1 / (4 * Real.sqrt s0))) / s0) *
      ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ^ 4 *
      (‖colU (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z -
          colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z‖ +
        ‖colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z -
          colV (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z‖ +
        ‖colC (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z -
          colC (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z‖) := by
  have hx : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hsqx : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hx
  have hsqle : Real.sqrt s0 ≤ Real.sqrt z.re := Real.sqrt_le_sqrt hs
  have hzn : ‖z‖ ≤ 2 * z.re := sd2_norm_z_le hx hzS
  have hNu := sd1pf_sqNorm_nonneg u
  have hNv := sd1pf_sqNorm_nonneg v
  have hN0 : 0 ≤ sqNorm u + sqNorm v := by linarith
  -- Λ nonvanishing and its inverse bound for K and K'
  have hLinv : ∀ M : Mat m n,
      colLambda (M.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z ≠ 0 ∧
      ‖colLambda (M.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖⁻¹ ≤
        (1 + 1 / Real.sqrt s0) ^ 2 * (((1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 2) := by
    intro M
    obtain ⟨hL0, -⟩ := lem_app_de_deletion_sector M (ϖ * d) u v (M + (ϖ * d) • outer u v) z rfl
      hx hzS
    refine ⟨hL0, ?_⟩
    have hinv := (eqn_app_dyn_sector_inverse M (ϖ * d) u v (M + (ϖ * d) • outer u v) z rfl hx hzS).2
    refine hinv.trans ?_
    have ha : |ϖ * d| ≤ |d| := by
      rw [abs_mul, abs_of_nonneg hϖ0]; exact mul_le_of_le_one_left (abs_nonneg d) hϖ1
    have h1 : |ϖ * d| * (sqNorm u + sqNorm v) / Real.sqrt z.re ≤
        |d| * (sqNorm u + sqNorm v) / Real.sqrt s0 := by
      calc _ ≤ |d| * (sqNorm u + sqNorm v) / Real.sqrt z.re :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ha hN0) hsqx.le
        _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hsq0 hsqle
    have h2 : 1 + |ϖ * d| * (sqNorm u + sqNorm v) / Real.sqrt z.re ≤
        (1 + 1 / Real.sqrt s0) * ((1 + |d|) * (1 + (sqNorm u + sqNorm v))) := by
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r = 1 / Real.sqrt s0 := ⟨_, rfl⟩
      have hr0 : 0 ≤ r := by rw [hr]; positivity
      have hrr : |d| * (sqNorm u + sqNorm v) / Real.sqrt s0 = r * (|d| * (sqNorm u + sqNorm v)) := by
        rw [hr]; ring
      rw [← hr]
      have e : (1 + r) * ((1 + |d|) * (1 + (sqNorm u + sqNorm v))) =
          1 + r * (|d| * (sqNorm u + sqNorm v)) +
          (r + r * (|d| + (sqNorm u + sqNorm v)) + (|d| + (sqNorm u + sqNorm v)) +
            |d| * (sqNorm u + sqNorm v)) := by ring
      have hrest : 0 ≤ r + r * (|d| + (sqNorm u + sqNorm v)) + (|d| + (sqNorm u + sqNorm v)) +
            |d| * (sqNorm u + sqNorm v) := by positivity
      rw [e]
      linarith [h1, hrr]
    have h0 : 0 ≤ 1 + |ϖ * d| * (sqNorm u + sqNorm v) / Real.sqrt z.re := by positivity
    calc (1 + |ϖ * d| * (sqNorm u + sqNorm v) / Real.sqrt z.re) ^ 2 ≤
        ((1 + 1 / Real.sqrt s0) * ((1 + |d|) * (1 + (sqNorm u + sqNorm v)))) ^ 2 :=
          pow_le_pow_left₀ h0 h2 2
      _ = _ := by ring
  have hR : ∀ M : Mat m n, opNorm (colR (M.map (fun x : ℝ => (x : ℂ))) z) ≤ 1 / z.re :=
    fun M => by rw [← rres_neg_eq_colR]; exact sd0_R_bound M z hx
  have hRt : ∀ M : Mat m n, opNorm (colRt (M.map (fun x : ℝ => (x : ℂ))) z) ≤ 1 / z.re :=
    fun M => by rw [← rtil_neg_eq_colRt, sd1_Rtil_eq]; exact sd0_R_bound _ z hx
  have hXb : ∀ M : Mat m n, opNorm (colX (M.map (fun x : ℝ => (x : ℂ))) z) ≤
      1 / (2 * Real.sqrt z.re) := fun M => by
    have := sd0_X_bound M z hx
    unfold XzC at this
    rw [rres_neg_eq_colR] at this
    exact this
  have hU' : z.re * ‖colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z‖ ≤
      sqNorm u + sqNorm v := by
    have h := sd3q_quad_scalar_bound (colR (K'.map (fun x : ℝ => (x : ℂ))) z) u z.re hx (hR K')
    have h' : ‖colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z‖ ≤ sqNorm u / z.re := h
    have := (le_div_iff₀ hx).1 (h'.trans_eq' rfl)
    nlinarith [mul_comm z.re ‖colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z‖]
  have hV : z.re * ‖colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z‖ ≤
      sqNorm u + sqNorm v := by
    have h := sd3q_quad_scalar_bound (colRt (K.map (fun x : ℝ => (x : ℂ))) z) v z.re hx (hRt K)
    have h' : ‖colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z‖ ≤ sqNorm v / z.re := h
    have := (le_div_iff₀ hx).1 h'
    nlinarith [mul_comm z.re ‖colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z‖]
  have hC : ∀ M : Mat m n, ‖colC (M.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ))
      (fun i => (v i : ℂ)) z‖ ≤ (1 / (4 * Real.sqrt s0)) * (sqNorm u + sqNorm v) := by
    intro M
    have h := sd3q_cross_scalar_bound (colX (M.map (fun x : ℝ => (x : ℂ))) z) u v z.re hx (hXb M)
    have h' : ‖colC (M.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖ ≤ (sqNorm u + sqNorm v) / (4 * Real.sqrt z.re) := h
    refine h'.trans ?_
    rw [div_eq_mul_inv, ← one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right (one_div_le_one_div_of_le (by positivity)
      (by linarith)) hN0
  obtain ⟨hL0, hLi⟩ := hLinv K
  obtain ⟨hL0', hLi'⟩ := hLinv K'
  have hq : (0 : ℝ) ≤ 1 / (4 * Real.sqrt s0) := by positivity
  have hc1 : (1 : ℝ) ≤ 1 + 1 / Real.sqrt s0 := by
    have : 0 ≤ 1 / Real.sqrt s0 := by positivity
    linarith
  have hhn : ‖((ϖ * d : ℝ) : ℂ)‖ ≤ ϖ * |d| := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hϖ0]
  have halg := sd3_alg s0 z.re ϖ (sqNorm u + sqNorm v) (1 / (4 * Real.sqrt s0))
    (1 + 1 / Real.sqrt s0) |d| ((ϖ * d : ℝ) : ℂ) z
    (colU (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z)
    (colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z)
    (colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z)
    (colV (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z)
    (colC (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z)
    (colC (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z)
    (colLambda (K.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
      (fun i => (v i : ℂ)) z)
    (colLambda (K'.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
      (fun i => (v i : ℂ)) z)
    hs0 hs hϖ0 hϖ1 hN0 hq hc1 (abs_nonneg d) hhn rfl rfl hL0 hL0'
    (by rw [mul_pow]; exact hLi) (by rw [mul_pow]; exact hLi') hU' hV hzn (hC K) (hC K')
  refine halg.trans ?_
  have hA10 : ((1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 10 ≤
      ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + |d| := by linarith [abs_nonneg d]
    have h2 : (1 : ℝ) ≤ 1 + (sqNorm u + sqNorm v) := by linarith
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    exact mul_le_mul (pow_le_pow_right₀ h1 (by norm_num)) (pow_le_pow_right₀ h2 (by norm_num))
      (by positivity) (by positivity)
  have hK0 : 0 ≤ (1 + 1 / Real.sqrt s0) ^ 2 +
      (1 + 1 / Real.sqrt s0) ^ 4 * (2 + 2 * (1 / (4 * Real.sqrt s0))) / s0 := by positivity
  have hS : 0 ≤ ‖colU (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z -
        colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z‖ +
      ‖colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z -
        colV (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z‖ +
      ‖colC (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z -
        colC (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z‖ :=
    by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA10
    (mul_nonneg (sq_nonneg ϖ) hK0)) hS

private lemma sd3_dot_re_im {a b : ℕ} (D : Matrix (Fin a) (Fin b) ℂ) (u : Vec a) (v : Vec b) :
    ((fun i => (u i : ℂ)) ⬝ᵥ (D *ᵥ fun i => (v i : ℂ))).re = u ⬝ᵥ ((D.map Complex.re) *ᵥ v) ∧
    ((fun i => (u i : ℂ)) ⬝ᵥ (D *ᵥ fun i => (v i : ℂ))).im = u ⬝ᵥ ((D.map Complex.im) *ᵥ v) := by
  constructor
  · simp [dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re, Finset.sum_mul]
  · simp [dotProduct, Matrix.mulVec, Complex.im_sum, Complex.mul_im, Finset.sum_mul]

private lemma sd3_norm_le_re_im (w : ℂ) : ‖w‖ ≤ |w.re| + |w.im| := by
  have := Complex.norm_le_abs_re_add_abs_im w
  simpa using this

private lemma sd3r_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f g : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ ∧
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by exact Real.HolderConjugate.two_two) (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two, one_div] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa using h

private lemma sd3_gbound (s x s0 CS B k : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ x) (hBr : 0 < B)
    (_hCS : 0 ≤ CS) (_hk : 0 ≤ k) :
    6 * (3 * (CS / B * (8 * k / x)) ^ 2 + 3 * (CS / B * (8 * k / x)) ^ 2 +
        3 * (CS / B * (8 * k / x)) ^ 2 + 3 * (CS / B * (8 * k / x)) ^ 2 +
        (CS / B * (5 * k / Real.sqrt x)) ^ 2 + (CS / B * (5 * k / Real.sqrt x)) ^ 2) ≤
      (Real.sqrt (6 * (768 / s0 + 50)) * CS * k / (B * Real.sqrt x)) ^ 2 := by
  have hxpos : 0 < x := lt_of_lt_of_le hs0 hs
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hxpos.le
  have hsr : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (CS / B * k / Real.sqrt x) ^ 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have ha2 : (CS / B * (8 * k / x)) ^ 2 = 64 * y / x := by
    rw [hy, div_pow, hsq]; field_simp; ring
  have hb2 : (CS / B * (5 * k / Real.sqrt x)) ^ 2 = 25 * y := by
    rw [hy]; field_simp; ring
  have hR : (Real.sqrt (6 * (768 / s0 + 50)) * CS * k / (B * Real.sqrt x)) ^ 2 =
      6 * (768 / s0 + 50) * y := by
    have h3 : 0 ≤ 6 * (768 / s0 + 50) := by positivity
    have e : Real.sqrt (6 * (768 / s0 + 50)) * CS * k / (B * Real.sqrt x) =
        Real.sqrt (6 * (768 / s0 + 50)) * (CS / B * k / Real.sqrt x) := by
      field_simp
    rw [e, mul_pow, Real.sq_sqrt h3, hy]
  rw [hR, ha2, hb2]
  have h1 : 64 * y / x ≤ 64 * y / s0 := div_le_div_of_nonneg_left (by positivity) hs0 hs
  have : 6 * (3 * (64 * y / x) + 3 * (64 * y / x) + 3 * (64 * y / x) + 3 * (64 * y / x) +
      25 * y + 25 * y) ≤ 6 * (768 / s0 + 50) * y := by
    have e : 6 * (768 / s0 + 50) * y = 6 * (12 * (64 * y / s0) + 50 * y) := by field_simp; ring
    rw [e]; nlinarith
  exact this

private lemma sd3_diff_U {m n : ℕ} (K K' : Mat m n) (u : Vec m) (z : ℂ) :
    colU (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z -
      colU (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) z =
    (fun i => (u i : ℂ)) ⬝ᵥ ((Rres K (-z) - Rres K' (-z)) *ᵥ fun i => (u i : ℂ)) := by
  unfold colU
  rw [← rres_neg_eq_colR, ← rres_neg_eq_colR, Matrix.sub_mulVec, dotProduct_sub]

private lemma sd3_diff_V {m n : ℕ} (K K' : Mat m n) (v : Vec n) (z : ℂ) :
    colV (K.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z -
      colV (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (v i : ℂ)) z =
    (fun i => (v i : ℂ)) ⬝ᵥ ((Rtil K (-z) - Rtil K' (-z)) *ᵥ fun i => (v i : ℂ)) := by
  unfold colV
  rw [← rtil_neg_eq_colRt, ← rtil_neg_eq_colRt, Matrix.sub_mulVec, dotProduct_sub]

private lemma sd3_diff_C {m n : ℕ} (K K' : Mat m n) (u : Vec m) (v : Vec n) (z : ℂ) :
    colC (K.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z -
      colC (K'.map (fun x : ℝ => (x : ℂ))) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z =
    (fun i => (u i : ℂ)) ⬝ᵥ ((XzC K z - XzC K' z) *ᵥ fun i => (v i : ℂ)) := by
  unfold colC colX XzC
  rw [← rres_neg_eq_colR, ← rres_neg_eq_colR, Matrix.sub_mulVec, dotProduct_sub]

set_option maxHeartbeats 1000000 in
private theorem sd3_main (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (F : FrozenParams m n B) (K K' : Mat m n) (ϖ : ℝ) (z : ℂ) (k : ℕ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ z.re → |z.im| ≤ z.re / 2 → Matrix.rank (K - K') ≤ k →
        ‖phiFreshC F K ϖ z - phiFreshC F K' ϖ z‖ ≤ C * ϖ ^ 2 * k / (Real.sqrt z.re * B) := by
  obtain ⟨K8, hK80, hK8⟩ := sd1_W_moment 8 (by norm_num) CS γ
  obtain ⟨K1, hK10, hK1⟩ := sd1_W_moment 1 (by norm_num) CS γ
  obtain ⟨cc, hcc⟩ := lem_app_de_coeff_sector s0 hs0
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = (1 + 1 / Real.sqrt s0) ^ 2 +
      (1 + 1 / Real.sqrt s0) ^ 4 * (2 + 2 * (1 / (4 * Real.sqrt s0))) / s0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K0 := by rw [hK0def]; positivity
  refine ⟨K0 * Real.sqrt K8 * Real.sqrt (6 * (768 / s0 + 50)) * CS, ?_⟩
  intro m n B F K K' ϖ z k hSo hSi hm hn hϖ0 hϖ1 hs hzS hrank
  have hx : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hsr : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hx
  have hB := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := le_trans (by unfold opNorm; exact norm_nonneg _) hSo
  have hfm : freshMeas m n = gaussPair m n := rfl
  have hmN : Measurable (momN F.C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV; fun_prop
  have hmr : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable (fun x : Vec m × Vec n => momU F.C B x) := by unfold momU; fun_prop
  have hVm : Measurable (fun x : Vec m × Vec n => momV F.C B x) := by unfold momV; fun_prop
  -- measurability and integrability of the integrand
  obtain ⟨-, c2, -⟩ := sd1_alpha_cont (m := m) (n := n) z hx hzS
  have hψm : ∀ M : Mat m n, Measurable (fun x : Vec m × Vec n =>
      colAlpha2 (M.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z) := by
    intro M
    have hq : Measurable (fun x : Vec m × Vec n =>
        (M, ϖ * resid F.A x, momU F.C B x, momV F.C B x)) :=
      measurable_const.prodMk ((hmr.const_mul ϖ).prodMk (hUm.prodMk hVm))
    have h := sd1_meas_comp _ c2 hq
    exact h
  obtain ⟨hWI1, -⟩ := hK1 m n B F.C ⟨hm, hn⟩ hγ ⟨hSo, hSi⟩ F.A F.hA
  have hψi : ∀ M : Mat m n, Integrable (fun x : Vec m × Vec n =>
      colAlpha2 (M.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z) (gaussPair m n) := by
    intro M
    refine Integrable.mono' (hWI1.const_mul (cc * ϖ ^ 2 / z.re)) (hψm M).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have h := (hcc M (momU F.C B x) (momV F.C B x) (resid F.A x) ϖ z hϖ0 hϖ1 hs hzS).2.1
    rw [sd1_sq_eq F x] at h
    refine h.trans (le_of_eq ?_)
    simp only [pow_one]
    ring
  have hdiff : phiFreshC F K ϖ z - phiFreshC F K' ϖ z = ∫ x, (
      colAlpha2 (K.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z -
      colAlpha2 (K'.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z) ∂(gaussPair m n) := by
    unfold phiFreshC
    rw [hfm]
    exact (integral_sub (hψi K) (hψi K')).symm
  obtain ⟨hWI, hWint⟩ := hK8 m n B F.C ⟨hm, hn⟩ hγ ⟨hSo, hSi⟩ F.A F.hA
  obtain ⟨nD1, nD2⟩ := sd3_nuc_D K K' z hx k hrank
  obtain ⟨nT1, nT2⟩ := sd3_nuc_Dt K K' z hx k hrank
  obtain ⟨nE1, nE2⟩ := sd3_nuc_E K K' z hx k hrank
  obtain ⟨hgL, hgint⟩ := sd3_g_abs F.C hB CS hSo hSi _ _ _ _ _ _ _ _ nD1 nD2 nT1 nT2 nE1 nE2
  have hpt : ∀ x : Vec m × Vec n,
      ‖colAlpha2 (K.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
          (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z -
        colAlpha2 (K'.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
          (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z‖ ≤
      (ϖ ^ 2 * K0) * ((((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4) *
        (|momU F.C B x ⬝ᵥ (((Rres K (-z) - Rres K' (-z)).map Complex.re) *ᵥ momU F.C B x)| +
         |momU F.C B x ⬝ᵥ (((Rres K (-z) - Rres K' (-z)).map Complex.im) *ᵥ momU F.C B x)| +
         |momV F.C B x ⬝ᵥ (((Rtil K (-z) - Rtil K' (-z)).map Complex.re) *ᵥ momV F.C B x)| +
         |momV F.C B x ⬝ᵥ (((Rtil K (-z) - Rtil K' (-z)).map Complex.im) *ᵥ momV F.C B x)| +
         |momU F.C B x ⬝ᵥ (((XzC K z - XzC K' z).map Complex.re) *ᵥ momV F.C B x)| +
         |momU F.C B x ⬝ᵥ (((XzC K z - XzC K' z).map Complex.im) *ᵥ momV F.C B x)|)) := by
    intro x
    have h := sd3_pt K K' (momU F.C B x) (momV F.C B x) (resid F.A x) ϖ z s0 hs0 hs hzS hϖ0 hϖ1
    rw [sd1_sq_eq F x, ← hK0def, sd3_diff_U, sd3_diff_V, sd3_diff_C] at h
    obtain ⟨u1, u2⟩ := sd3_dot_re_im (Rres K (-z) - Rres K' (-z)) (momU F.C B x) (momU F.C B x)
    obtain ⟨v1, v2⟩ := sd3_dot_re_im (Rtil K (-z) - Rtil K' (-z)) (momV F.C B x) (momV F.C B x)
    obtain ⟨c1, c2'⟩ := sd3_dot_re_im (XzC K z - XzC K' z) (momU F.C B x) (momV F.C B x)
    have bU := sd3_norm_le_re_im ((fun i => (momU F.C B x i : ℂ)) ⬝ᵥ
      ((Rres K (-z) - Rres K' (-z)) *ᵥ fun i => (momU F.C B x i : ℂ)))
    have bV := sd3_norm_le_re_im ((fun i => (momV F.C B x i : ℂ)) ⬝ᵥ
      ((Rtil K (-z) - Rtil K' (-z)) *ᵥ fun i => (momV F.C B x i : ℂ)))
    have bC := sd3_norm_le_re_im ((fun i => (momU F.C B x i : ℂ)) ⬝ᵥ
      ((XzC K z - XzC K' z) *ᵥ fun i => (momV F.C B x i : ℂ)))
    rw [u1, u2] at bU
    rw [v1, v2] at bV
    rw [c1, c2'] at bC
    refine h.trans ?_
    have hP : 0 ≤ ϖ ^ 2 * K0 * (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4) := by
      have : 0 ≤ momN F.C B x := by unfold momN; positivity
      positivity
    have hsum : ‖(fun i => (momU F.C B x i : ℂ)) ⬝ᵥ
            ((Rres K (-z) - Rres K' (-z)) *ᵥ fun i => (momU F.C B x i : ℂ))‖ +
          ‖(fun i => (momV F.C B x i : ℂ)) ⬝ᵥ
            ((Rtil K (-z) - Rtil K' (-z)) *ᵥ fun i => (momV F.C B x i : ℂ))‖ +
          ‖(fun i => (momU F.C B x i : ℂ)) ⬝ᵥ
            ((XzC K z - XzC K' z) *ᵥ fun i => (momV F.C B x i : ℂ))‖ ≤
        |momU F.C B x ⬝ᵥ (((Rres K (-z) - Rres K' (-z)).map Complex.re) *ᵥ momU F.C B x)| +
         |momU F.C B x ⬝ᵥ (((Rres K (-z) - Rres K' (-z)).map Complex.im) *ᵥ momU F.C B x)| +
         |momV F.C B x ⬝ᵥ (((Rtil K (-z) - Rtil K' (-z)).map Complex.re) *ᵥ momV F.C B x)| +
         |momV F.C B x ⬝ᵥ (((Rtil K (-z) - Rtil K' (-z)).map Complex.im) *ᵥ momV F.C B x)| +
         |momU F.C B x ⬝ᵥ (((XzC K z - XzC K' z).map Complex.re) *ᵥ momV F.C B x)| +
         |momU F.C B x ⬝ᵥ (((XzC K z - XzC K' z).map Complex.im) *ᵥ momV F.C B x)| := by
      linarith [bU, bV, bC]
    exact (mul_le_mul_of_nonneg_left hsum hP).trans (le_of_eq (by ring))
  have hNnn : ∀ x : Vec m × Vec n, 0 ≤ momN F.C B x := fun x => by unfold momN; positivity
  have hf4m : Measurable (fun x : Vec m × Vec n =>
      (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) := by fun_prop
  have hf4L : MemLp (fun x : Vec m × Vec n =>
      (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) 2 (gaussPair m n) := by
    rw [memLp_two_iff_integrable_sq hf4m.aestronglyMeasurable]
    refine hWI.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; rw [← pow_mul]
  obtain ⟨hprodI, hprod⟩ := sd3r_cs (gaussPair m n) _ _
    (fun x => by have := hNnn x; positivity)
    (fun x => by positivity) hf4L hgL
  have hdI := (hψi K).sub (hψi K')
  have hrhsI := hprodI.const_mul (ϖ ^ 2 * K0)
  have h1 := (norm_integral_le_integral_norm (μ := gaussPair m n) (fun x : Vec m × Vec n =>
      colAlpha2 (K.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z -
      colAlpha2 (K'.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z)).trans
    (integral_mono hdI.norm hrhsI hpt)
  rw [integral_const_mul] at h1
  have hW8 : ∫ x, ((((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) ^ 2
      ∂(gaussPair m n) ≤ K8 := by
    refine le_trans (le_of_eq ?_) hWint
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; rw [← pow_mul]
  have hG := hgint.trans (sd3_gbound z.re z.re s0 CS B k hs0 hs hBr hCS (Nat.cast_nonneg k))
  have h2 := hprod.trans (mul_le_mul (Real.sqrt_le_sqrt hW8) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [Real.sqrt_sq (by positivity)] at h2
  rw [hdiff]
  refine h1.trans ?_
  have hc0 : 0 ≤ ϖ ^ 2 * K0 := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hc0).trans (le_of_eq ?_)
  field_simp

/-- `lem:app-drift-rank` (`eqn:app-drift-rank`) at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (source as in
`lem_app_drift_multiplier_i_sector`, ll. 858–870): `|φ_ϖ(K) − φ_ϖ(K')| ≤ Cϖ²k/(√x B)` for
`rank(K − K') ≤ k`. Real counterpart `Muon.Drift.lem_app_drift_rank` (`Coefficients.lean`:3287). -/
theorem lem_app_drift_rank_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (F : FrozenParams m n B) (K K' : Mat m n) (ϖ : ℝ) (z : ℂ) (k : ℕ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ z.re → |z.im| ≤ z.re / 2 → Matrix.rank (K - K') ≤ k →
        ‖phiFreshC F K ϖ z - phiFreshC F K' ϖ z‖ ≤ C * ϖ ^ 2 * k / (Real.sqrt z.re * B) := by
  exact sd3_main s0 hs0 CS γ hγ

/-! ### Helpers for `lem_app_drift_covariance_sector` -/


/-- The source weight class controls its squared weights. -/
private lemma sd4_summable_sq (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (hw1 : ∀ j, w j ≤ 1) :
    Summable (fun j => w j ^ 2) := by
  exact Summable.of_nonneg_of_le (fun j => sq_nonneg (w j))
    (fun j => by nlinarith [hw0 j, hw1 j]) hw

/-- Summation of any nonnegative per-age bound with the source weights. -/
private lemma sd4_sum_of_sq_bound (w f : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (hw1 : ∀ j, w j ≤ 1) (K : ℝ)
    (hf0 : ∀ j, 0 ≤ f j) (hf : ∀ j, f j ≤ K * w j ^ 2) :
    Summable f ∧ (∑' j, f j) ≤ K * sumPow w 2 := by
  have hsq := sd4_summable_sq w hw0 hw hw1
  have hmajor := hsq.mul_left K
  have hsum := Summable.of_nonneg_of_le hf0 hf hmajor
  refine ⟨hsum, ?_⟩
  calc (∑' j, f j) ≤ ∑' j, K * w j ^ 2 := hsum.tsum_le_tsum hf hmajor
    _ = K * sumPow w 2 := by rw [tsum_mul_left]; rfl

private lemma sd4_sample_measurable {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma sd4_del_measurable {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := sd4_sample_measurable F
  have hzw : ∀ p : ℤ × Fin B, p ≠ (t + 1 - (j : ℤ), slotOne F.hB) →
      Measurable[sigmaOthers F S t j] (S.zw p.1 p.2) := by
    intro p hp
    have hle : MeasurableSpace.comap (S.zw p.1 p.2) inferInstance ≤ sigmaOthers F S t j :=
      le_iSup₂ (f := fun (p : ℤ × Fin B) (_ : p ≠ (t + 1 - (j : ℤ), slotOne F.hB)) =>
        MeasurableSpace.comap (S.zw p.1 p.2) inferInstance) p hp
    exact (comap_measurable (S.zw p.1 p.2)).mono hle le_rfl
  unfold delBufAge WeightedBufDel
  letI : MeasurableSpace Ω := sigmaOthers F S t j
  refine Measurable.tsum fun j' => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j')
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j' : ℤ) = t + 1 - (j : ℤ) ∧ b = slotOne F.hB
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have hne : ((t + 1 - (j' : ℤ), b) : ℤ × Fin B) ≠ (t + 1 - (j : ℤ), slotOne F.hB) := by
      intro heq; exact h ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    exact hQ.comp (hzw _ hne)

/-- A buffer with a set of slots deleted is measurable without any deleted slot. -/
private lemma sd4_masked_buf_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (U : Finset (ℤ × Fin B)) (p : ℤ × Fin B)
    (hp : p ∈ U) :
    Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance]
      (fun ω => ∑' k : ℕ, w k • ((B : ℝ)⁻¹ • ∑ b : Fin B,
        if (t + 1 - (k : ℤ), b) ∈ U then 0
        else sampleTerm F S (t + 1 - (k : ℤ)) b ω)) := by
  classical
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  have hzw : ∀ q : ℤ × Fin B, q ≠ p → Measurable[G] (S.zw q.1 q.2) := by
    intro q hq
    exact (comap_measurable (S.zw q.1 q.2)).mono
      (le_iSup_of_le q (le_iSup_of_le hq le_rfl)) le_rfl
  letI : MeasurableSpace Ω := G
  refine Measurable.tsum fun k => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w k)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : (t + 1 - (k : ℤ), b) ∈ U
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have hne : (t + 1 - (k : ℤ), b) ≠ p := by
      intro he; exact h (he.symm ▸ hp)
    exact (sd4_sample_measurable F).comp (hzw _ hne)

/-- Removing one further slot is a finite modification of the buffer series. -/
private lemma sd4_masked_delete {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (U : Finset (ℤ × Fin B))
    (k : ℕ) (a : Fin B) (ω : Ω) (hp : (t + 1 - (k : ℤ), a) ∉ U)
    (hsum : Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω))) :
    Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) ∧
    (∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) =
    (∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) +
      w k • ((B : ℝ)⁻¹ • sampleTerm F S (t + 1 - (k : ℤ)) a ω) := by
  classical
  let f := fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  let g := fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  let v := w k • ((B : ℝ)⁻¹ • sampleTerm F S (t + 1 - (k : ℤ)) a ω)
  have hterm : ∀ l, f l = g l + if l = k then v else 0 := by
    intro l
    by_cases hl : l = k
    · subst l
      have hbatch : (∑ b : Fin B,
          if (t + 1 - (k : ℤ), b) ∈ U then (0 : Mat m n)
          else sampleTerm F S (t + 1 - (k : ℤ)) b ω) =
          (∑ b : Fin B,
          if (t + 1 - (k : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
          else sampleTerm F S (t + 1 - (k : ℤ)) b ω) +
            sampleTerm F S (t + 1 - (k : ℤ)) a ω := by
        have he : ∀ b : Fin B,
            (if (t + 1 - (k : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U
              then (0 : Mat m n) else sampleTerm F S (t + 1 - (k : ℤ)) b ω) =
            (if (t + 1 - (k : ℤ), b) ∈ U then 0
              else sampleTerm F S (t + 1 - (k : ℤ)) b ω) -
            (if b = a then sampleTerm F S (t + 1 - (k : ℤ)) b ω else 0) := by
          intro b
          by_cases hb : b = a
          · subst b; simp [hp]
          · simp [Finset.mem_insert, Prod.mk.injEq, hb]
        simp_rw [he, Finset.sum_sub_distrib]
        simp
      change _ = _ + if k = k then v else 0
      rw [if_pos rfl]
      dsimp [f, g, v]
      rw [hbatch, smul_add, smul_add]
    · have hne : ∀ b : Fin B,
          (t + 1 - (l : ℤ), b) ≠ (t + 1 - (k : ℤ), a) := by
        intro b he; apply hl
        have he' := congrArg Prod.fst he
        omega
      simp [f, g, hl, Finset.mem_insert, hne]
  have hi : Summable (fun l : ℕ => if l = k then v else 0) :=
    (hasSum_ite_eq k v).summable
  have hg : Summable g := (hsum.sub hi).congr (fun l => by
    change f l - _ = g l
    rw [hterm l, add_sub_cancel_right])
  refine ⟨hg, ?_⟩
  change (∑' l, f l) = (∑' l, g l) + v
  rw [tsum_congr hterm, hg.tsum_add hi, tsum_ite_eq]

open scoped MatrixOrder in
private lemma sd4_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * Muon.outer z w * rIn F.C =
      Muon.outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hsym : (rIn F.C)ᵀ = rIn F.C := by
    have h : (CFC.sqrt F.C.Sin)ᴴ = CFC.sqrt F.C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F.C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, hsym]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma sd4_sample {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) (ω : Ω) :
    (B : ℝ)⁻¹ • sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) • Muon.outer (momU F.C B (S.zw s a ω)) (momV F.C B (S.zw s a ω)) := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) •
        Muon.outer (Matrix.mulVec (rOut F.C) (S.zw s a ω).1)
          (Matrix.mulVec (rIn F.C) (S.zw s a ω).2) := by
    unfold sampleTerm
    rw [sd4_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

/-- The double-deleted buffer is measurable without either removed sample, and adding the
second sample back recovers the distinguished minor almost surely. -/
private lemma sd4_double_deletion {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (hw : WeightSeq w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j k : ℕ) (a : Fin B)
    (hne : (t + 1 - (k : ℤ), a) ≠ (t + 1 - (j : ℤ), slotOne F.hB)) :
    ∃ Z : Ω → Mat m n,
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z ∧
      Measurable[sigmaOthers F S t j] Z ∧
      ∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω)) := by
  classical
  let U : Finset (ℤ × Fin B) :=
    insert (t + 1 - (k : ℤ), a) {(t + 1 - (j : ℤ), slotOne F.hB)}
  let Z : Ω → Mat m n := fun ω => ∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  refine ⟨Z, sd4_masked_buf_measurable w F S t U _ (Finset.mem_insert_self _ _), ?_, ?_⟩
  · exact sd4_masked_buf_measurable w F S t U _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · filter_upwards [weightedBuf_summable_ae w hw F S] with ω hω
    have hsum0 : Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
        if (t + 1 - (l : ℤ), b) ∈ (∅ : Finset (ℤ × Fin B)) then 0
        else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) := by
      simpa only [Finset.notMem_empty, ↓reduceIte, ← frozenBatchG_eq_sum] using hω t
    have hsum1 := (sd4_masked_delete w F S t ∅ j (slotOne F.hB) ω
      (Finset.notMem_empty _) hsum0).1
    simp only [Finset.insert_empty] at hsum1
    have hdec := (sd4_masked_delete w F S t {(t + 1 - (j : ℤ), slotOne F.hB)}
      k a ω (by simpa only [Finset.mem_singleton] using hne) hsum1).2
    have he : delBufAge w F S t j ω =
        ∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
          if (t + 1 - (l : ℤ), b) ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Finset (ℤ × Fin B)) then 0
          else sampleTerm F S (t + 1 - (l : ℤ)) b ω) := by
      simp only [delBufAge, WeightedBufDel, Finset.mem_singleton, Prod.mk.injEq]
    rw [he]
    simpa only [sd4_sample, smul_smul, Z, U] using hdec

/-- The distinguished Gaussian pair is independent of all other samples. -/
private lemma sd4_others_indep {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Indep (sigmaOthers F S t j)
      (MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance) P := by
  let X := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hind0 := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
  have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
      ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
    rw [Set.disjoint_singleton_right]; exact fun h => h rfl
  have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
  have hB' : MeasurableSpace.comap X inferInstance ≤
      ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
    le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
      (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
  exact indep_of_indep_of_le_right key hB'

/-- Every slot is independent of the sigma-field generated by all remaining slots. -/
private lemma sd4_slot_indep {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (S : FrozenSamples P m n B) (p : ℤ × Fin B) :
    Indep (⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
      (MeasurableSpace.comap (S.zw p.1 p.2) inferInstance) P := by
  have hi := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
  have hd : Disjoint {q : ℤ × Fin B | q ≠ p} ({p} : Set (ℤ × Fin B)) := by
    rw [Set.disjoint_singleton_right]
    exact fun h => h rfl
  have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hi hd
  exact indep_of_indep_of_le_right key (le_iSup_of_le p
    (le_iSup_of_le (Set.mem_singleton p) le_rfl))

/-- Samples later than the buffer time do not occur in the distinguished minor. -/
private lemma sd4_del_measurable_future {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (p : ℤ × Fin B)
    (hp : t + 1 < p.1) :
    Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] (delBufAge w F S t j) := by
  classical
  let U : Finset (ℤ × Fin B) := insert p {(t + 1 - (j : ℤ), slotOne F.hB)}
  have hm := sd4_masked_buf_measurable w F S t U p (Finset.mem_insert_self _ _)
  have hne : ∀ (k : ℕ) (a : Fin B), (t + 1 - (k : ℤ), a) ≠ p := by
    intro k a he
    have he1 := congrArg Prod.fst he
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    omega
  unfold delBufAge WeightedBufDel
  simpa only [U, Finset.mem_insert, Finset.mem_singleton, hne, false_or,
    Prod.mk.injEq] using hm

private lemma sd4_rank_add {k l : ℕ} (A B : Mat k l) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rw [Matrix.mulVecLin_add]
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private lemma sd4_rank_neg {k l : ℕ} (A : Mat k l) : (-A).rank = A.rank := by
  unfold Matrix.rank
  have : Matrix.mulVecLin (-A) = -Matrix.mulVecLin A := by
    ext x i; simp
  rw [this, LinearMap.range_neg]

private lemma sd4_rank_sub {k l : ℕ} (A B : Mat k l) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg]
  have := sd4_rank_add A (-B)
  rwa [sd4_rank_neg] at this

/-- Replacing one sample changes a matrix by rank at most two. -/
private lemma sd4_rank_replace {m n : ℕ} (K : Mat m n) (c c' : ℝ)
    (u u' : Vec m) (v v' : Vec n) :
    Matrix.rank ((K + c • Muon.outer u v) - (K + c' • Muon.outer u' v')) ≤ 2 := by
  have houter : ∀ (d : ℝ) (x : Vec m) (y : Vec n),
      Matrix.rank (d • Muon.outer x y) ≤ 1 := by
    intro d x y
    have heq : d • Muon.outer x y = Muon.outer (d • x) y := by
      ext i k
      simp only [Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact Matrix.rank_vecMulVec_le _ _
  have heq : (K + c • Muon.outer u v) - (K + c' • Muon.outer u' v') =
      c • Muon.outer u v - c' • Muon.outer u' v' := by abel
  rw [heq]
  exact (sd4_rank_sub _ _).trans (by linarith [houter c u v, houter c' u' v'])

/-- Independence factors integrals on intersections with an independent event. -/
private lemma sd4_setIntegral_inter_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G X : MeasurableSpace Ω)
    (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable[G] f)
    (a x : Set Ω) (ha : MeasurableSet[G] a) (hx : MeasurableSet[X] x) :
    (∫ ω in a ∩ x, f ω ∂P) = P.real x * ∫ ω in a, f ω ∂P := by
  have hi := hf.indicator (hG _ ha)
  have hc := condExp_indep_eq hG hX (hfm.indicator ha) hind
  calc
    _ = ∫ ω in x, a.indicator f ω ∂P := by
      rw [setIntegral_indicator (hG _ ha), Set.inter_comm]
    _ = ∫ ω in x, condExp X P (a.indicator f) ω ∂P :=
      (setIntegral_condExp hX hi hx).symm
    _ = ∫ _ω in x, (∫ ω in a, f ω ∂P) ∂P := by
      apply setIntegral_congr_ae (hX _ hx)
      filter_upwards [hc] with ω hω _
      simpa only [integral_indicator (hG _ ha)] using hω
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

/-- Revealing an independent sigma-field does not change a conditional expectation. -/
private lemma sd4_condExp_sup_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable[G] f) :
    condExp (A ⊔ X) P f =ᵐ[P] condExp A P f := by
  have hA : A ≤ mΩ := hAG.trans hG
  have hAX : A ⊔ X ≤ mΩ := sup_le hA hX
  let g := condExp A P f
  have hg : Integrable g P := integrable_condExp
  have hgm : StronglyMeasurable[G] g := stronglyMeasurable_condExp.mono hAG
  let T : Set (Set Ω) := {s | ∃ a x, MeasurableSet[A] a ∧ MeasurableSet[X] x ∧ s = a ∩ x}
  have hgen : A ⊔ X = MeasurableSpace.generateFrom T := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨a, univ, ha, MeasurableSet.univ, by simp⟩
      · intro x hx
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨univ, x, MeasurableSet.univ, hx, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨a, x, ha, hx, rfl⟩
      exact ((show A ≤ A ⊔ X from le_sup_left) _ ha).inter
        ((show X ≤ A ⊔ X from le_sup_right) _ hx)
  have hpi : IsPiSystem T := by
    rintro s ⟨a, x, ha, hx, rfl⟩ t ⟨b, y, hb, hy, rfl⟩ _
    exact ⟨a ∩ b, x ∩ y, ha.inter hb, hx.inter hy, by ext ω; simp only [mem_inter_iff]; tauto⟩
  have heq : ∀ a, MeasurableSet[A] a → ∫ ω in a, g ω ∂P = ∫ ω in a, f ω ∂P :=
    fun a ha => setIntegral_condExp hA hf ha
  have hall : ∀ s, MeasurableSet[A ⊔ X] s → ∫ ω in s, g ω ∂P = ∫ ω in s, f ω ∂P := by
    intro s hs
    induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic s hs =>
      rcases hs with ⟨a, x, ha, hx, rfl⟩
      rw [@sd4_setIntegral_inter_of_indep Ω mΩ P _ G X hG hX hind g hg hgm a x (hAG _ ha) hx,
        @sd4_setIntegral_inter_of_indep Ω mΩ P _ G X hG hX hind f hf hfm a x (hAG _ ha) hx,
        heq a ha]
    | compl s hs ih =>
      rw [setIntegral_compl (hAX _ hs) hg, setIntegral_compl (hAX _ hs) hf, ih]
      congr 1
      exact integral_condExp hA
    | iUnion u hd hu ih =>
      rw [integral_iUnion (fun k => hAX _ (hu k)) hd hg.integrableOn,
        integral_iUnion (fun k => hAX _ (hu k)) hd hf.integrableOn]
      exact tsum_congr ih
  have hgmAX : StronglyMeasurable[A ⊔ X] g :=
    (show StronglyMeasurable[A] g from stronglyMeasurable_condExp).mono le_sup_left
  exact (ae_eq_condExp_of_forall_setIntegral_eq hAX hf (fun _ _ _ => hg.integrableOn)
    (fun s hs _ => hall s hs)
    hgmAX.aestronglyMeasurable).symm

/-- Conditional expectation is self-adjoint against a bounded scalar test function. -/
private lemma sd4_integral_mul_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : MeasurableSpace Ω) (hA : A ≤ mΩ)
    (f q : Ω → ℝ) (hf : Integrable f P) (hq : Integrable q P)
    (L : ℝ) (hqb : ∀ᵐ ω ∂P, ‖q ω‖ ≤ L) :
    (∫ ω, f ω * condExp A P q ω ∂P) =
      ∫ ω, condExp A P f ω * q ω ∂P := by
  have hcb : ∀ᵐ ω ∂P, ‖condExp A P q ω‖ ≤ L :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hqb
  have hi1 : Integrable (fun ω => f ω * condExp A P q ω) P :=
    hf.mul_bdd (integrable_condExp.aestronglyMeasurable) hcb
  have hi2 : Integrable (fun ω => condExp A P f ω * q ω) P :=
    integrable_condExp.mul_bdd hq.aestronglyMeasurable hqb
  have h1 := condExp_mul_of_stronglyMeasurable_right
    (show StronglyMeasurable[A] (condExp A P q) from stronglyMeasurable_condExp) hi1 hf
  have h2 := condExp_mul_of_stronglyMeasurable_left
    (show StronglyMeasurable[A] (condExp A P f) from stronglyMeasurable_condExp) hi2 hq
  calc
    _ = ∫ ω, condExp A P (fun ω => f ω * condExp A P q ω) ω ∂P :=
      (integral_condExp hA).symm
    _ = ∫ ω, condExp A P f ω * condExp A P q ω ∂P := integral_congr_ae h1
    _ = ∫ ω, condExp A P (fun ω => condExp A P f ω * q ω) ω ∂P :=
      (integral_congr_ae h2).symm
    _ = _ := integral_condExp hA

/-- Conditioning a function of the past and the new sample on all other samples keeps only
its past conditional expectation. -/
private lemma sd4_condExp_of_sup_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (h : Ω → ℝ) (hi : Integrable h P) (hm : StronglyMeasurable[A ⊔ X] h) :
    condExp G P h =ᵐ[P] condExp A P h := by
  have hA : A ≤ mΩ := hAG.trans hG
  have hH : A ⊔ X ≤ mΩ := sup_le hA hX
  refine (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    ((show StronglyMeasurable[A] (condExp A P h) from
      stronglyMeasurable_condExp).mono hAG).aestronglyMeasurable).symm
  intro s hs _
  let q : Ω → ℝ := s.indicator (fun _ => 1)
  have hqm : StronglyMeasurable[G] q := stronglyMeasurable_const.indicator hs
  have hqi : Integrable q P := (integrable_const 1).indicator (hG _ hs)
  have hqb : ∀ᵐ ω ∂P, ‖q ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ s <;> simp [q, hω]
  have hc := @sd4_condExp_sup_of_indep Ω mΩ P _ A X G hAG hG hX hind q hqi hqm
  have hh : condExp (A ⊔ X) P h =ᵐ[P] h := (condExp_of_stronglyMeasurable hH hm hi).eventuallyEq
  have hindicator : ∀ f : Ω → ℝ, (∫ ω, f ω * q ω ∂P) = ∫ ω in s, f ω ∂P := by
    intro f
    rw [← integral_indicator (hG _ hs)]
    congr 1
    funext ω
    by_cases hω : ω ∈ s <;> simp [q, hω]
  calc
    _ = ∫ ω, condExp A P h ω * q ω ∂P := (hindicator _).symm
    _ = ∫ ω, h ω * condExp A P q ω ∂P :=
      (@sd4_integral_mul_condExp Ω mΩ P _ A hA h q hi hqi 1 hqb).symm
    _ = ∫ ω, h ω * condExp (A ⊔ X) P q ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω using congrArg (fun r => h ω * r) hω.symm
    _ = ∫ ω, condExp (A ⊔ X) P h ω * q ω ∂P :=
      @sd4_integral_mul_condExp Ω mΩ P _ (A ⊔ X) hH h q hi hqi 1 hqb
    _ = ∫ ω, h ω * q ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hh] with ω hω using congrArg (fun r => r * q ω) hω
    _ = _ := hindicator _

/-- The two conditional expectations commute when one sigma-field adds independent noise. -/
private lemma sd4_condExp_condExp_sup_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) :
    condExp G P (condExp (A ⊔ X) P f) =ᵐ[P] condExp A P f := by
  exact (@sd4_condExp_of_sup_indep Ω mΩ P _ A X G hAG hG hX hind _
    integrable_condExp stronglyMeasurable_condExp).trans
      (condExp_condExp_of_le le_sup_left (sup_le (hAG.trans hG) hX))

/-- The martingale increment has zero mean conditional on all unrevealed other samples. -/
private lemma sd4_independent_increment_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) :
    condExp G P (condExp (A ⊔ X) P f - condExp A P f) =ᵐ[P]
      fun _ => 0 := by
  have hsub := condExp_sub (m₀ := mΩ) (μ := P)
    (f := condExp (A ⊔ X) P f) (g := condExp A P f)
    integrable_condExp integrable_condExp G
  have hnew := @sd4_condExp_condExp_sup_indep Ω mΩ P _ A X G hAG hG hX hind f
  have hold : condExp G P (condExp A P f) = condExp A P f :=
    condExp_of_stronglyMeasurable hG
      ((show StronglyMeasurable[A] (condExp A P f) from
        stronglyMeasurable_condExp).mono hAG) integrable_condExp
  filter_upwards [hsub, hnew] with ω hs hn
  simpa only [Pi.sub_apply, hold, hn, sub_self] using hs

/-- Reveal the other samples in the order of their encodings; the resulting filtration exhausts
`sigmaOthers` and starts at the trivial sigma-field. -/
private lemma sd4_sample_filtration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    ∃ A : Filtration ℕ mΩ,
      (∀ l, A l = ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) ∧
      A 0 = ⊥ ∧ (⨆ l, A l) = sigmaOthers F S t j := by
  let A : Filtration ℕ mΩ := {
    seq := fun l => ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
      (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    mono' := by
      intro l l' hll'
      refine iSup_le fun q => iSup_le fun hq => iSup_le fun hql => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (lt_of_lt_of_le hql hll') le_rfl))
    le' := by
      intro l
      exact iSup_le fun q => iSup_le fun _ => iSup_le fun _ => (S.meas q.1 q.2).comap_le }
  refine ⟨A, fun _ => rfl, ?_, ?_⟩
  · change (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < 0), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) = ⊥
    simp only [Nat.not_lt_zero, iSup_of_empty, iSup_bot]
  · refine le_antisymm ?_ ?_
    · refine iSup_le fun l => ?_
      change (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) ≤ _
      refine iSup_le fun q => iSup_le fun hq => iSup_le fun _ => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
    · refine iSup_le fun q => iSup_le fun hq => ?_
      refine le_iSup_of_le (Encodable.encode q + 1) ?_
      change MeasurableSpace.comap (S.zw q.1 q.2) inferInstance ≤
        ⨆ (r : ℤ × Fin B) (_ : r ≠ (t + 1 - (j : ℤ), slotOne F.hB))
          (_ : Encodable.encode r < Encodable.encode q + 1),
          MeasurableSpace.comap (S.zw r.1 r.2) inferInstance
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (Nat.lt_succ_self _) le_rfl))

/-- An encoding step reveals exactly its single indexed sigma-field. -/
private lemma sd4_encoded_reveal {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d p : ι) (hp : p ≠ d) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p + 1), M q) =
      (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p), M q) ⊔ M p := by
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    by_cases hqp : q = p
    · subst q; exact le_sup_right
    · have hcode : Encodable.encode q ≠ Encodable.encode p :=
        fun h => hqp (Encodable.encode_injective h)
      have hlt : Encodable.encode q < Encodable.encode p := by omega
      exact le_sup_of_le_left (le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le hlt le_rfl)))
  · refine sup_le ?_ ?_
    · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))
    · exact le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le (Nat.lt_succ_self _) le_rfl))

/-- Before a slot is revealed, the filtration is contained in the sigma-field omitting it. -/
private lemma sd4_encoded_past_le {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d p : ι) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p), M q) ≤
      ⨆ (q : ι) (_ : q ≠ p), M q := by
  refine iSup_le fun q => iSup_le fun _ => iSup_le fun he => ?_
  have hqp : q ≠ p := by intro h; subst q; exact (lt_irrefl _ he)
  exact le_iSup_of_le q (le_iSup_of_le hqp le_rfl)

/-- An encoding gap (including the excluded distinguished slot) reveals no new information. -/
private lemma sd4_encoded_no_reveal {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d : ι) (l : ℕ)
    (hgap : ∀ q, q ≠ d → Encodable.encode q ≠ l) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < l + 1), M q) =
      ⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < l), M q := by
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    have hne := hgap q hq
    exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))

/-- Any finite collection of age-slot weights has mass at most `B` times the total age mass. -/
private lemma sd4_finite_slot_weight_sum {B : ℕ} (w : ℕ → ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (hw : Summable w) (U : Finset (ℕ × Fin B)) :
    (∑ p ∈ U, w p.1) ≤ (B : ℝ) * ∑' k, w k := by
  classical
  let V := U.image Prod.fst
  have hsub : U ⊆ V ×ˢ Finset.univ := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ p ∈ V ×ˢ Finset.univ, w p.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hw0 p.1)
    _ = (B : ℝ) * ∑ k ∈ V, w k := by
      simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun k _ => hw0 k)) (Nat.cast_nonneg B)

/-- Reindex any finite encoding budget by its age-slot pairs. -/
private lemma sd4_encoded_weight_budget {B : ℕ} (t : ℤ) (w : ℕ → ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (hw : Summable w) (hws : (∑' k, w k) ≤ 1)
    (f : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hzero : ∀ l, (∀ (k : ℕ) (a : Fin B),
      Encodable.encode (t + 1 - (k : ℤ), a) ≠ l) → f l = 0)
    (hslot : ∀ (k : ℕ) (a : Fin B),
      f (Encodable.encode (t + 1 - (k : ℤ), a)) ≤ K * w k) (N : ℕ) :
    (∑ l ∈ Finset.range N, f l) ≤ K * B := by
  classical
  let e : ℕ × Fin B → ℕ := fun p => Encodable.encode (t + 1 - (p.1 : ℤ), p.2)
  have he : Function.Injective e := by
    intro p q hpq
    have h := Encodable.encode_injective hpq
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · dsimp at h1
      omega
    · exact h2
  let U := (Finset.range N).preimage e he.injOn
  have hsub : U.image e ⊆ Finset.range N := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_preimage.mp hp
  have hreindex : (∑ l ∈ Finset.range N, f l) = ∑ p ∈ U, f (e p) := by
    calc
      _ = ∑ l ∈ U.image e, f l := by
        symm
        apply Finset.sum_subset hsub
        intro l hl hnot
        apply hzero
        intro k a hcode
        apply hnot
        exact Finset.mem_image.mpr ⟨(k, a), Finset.mem_preimage.mpr (by change Encodable.encode (t + 1 - (k : ℤ), a) ∈ Finset.range N; rw [hcode]; exact hl), hcode⟩
      _ = _ := Finset.sum_image he.injOn
  have hbound : (∑ p ∈ U, f (e p)) ≤ K * ∑ p ∈ U, w p.1 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hslot p.1 p.2
  have hmass : (∑ p ∈ U, w p.1) ≤ (B : ℝ) := by
    exact (sd4_finite_slot_weight_sum w hw0 hw U).trans
      (by simpa using mul_le_mul_of_nonneg_left hws (Nat.cast_nonneg B))
  rw [hreindex]
  exact hbound.trans (mul_le_mul_of_nonneg_left hmass hK)


/-! ### Complex scalar conditional expectations via real and imaginary parts -/

section SD4B
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd4_re_condExp (P : Measure Ω') (H : MeasurableSpace Ω') (f : Ω' → ℂ)
    (hf : Integrable f P) :
    (fun ω => (condExp H P f ω).re) =ᵐ[P] condExp H P (fun ω => (f ω).re) := by
  have h := Complex.reCLM.comp_condExp_comm (m := H) hf
  filter_upwards [h] with ω hω
  exact hω

private lemma sd4_im_condExp (P : Measure Ω') (H : MeasurableSpace Ω') (f : Ω' → ℂ)
    (hf : Integrable f P) :
    (fun ω => (condExp H P f ω).im) =ᵐ[P] condExp H P (fun ω => (f ω).im) := by
  have h := Complex.imCLM.comp_condExp_comm (m := H) hf
  filter_upwards [h] with ω hω
  exact hω

private lemma sd4_ae_eq_of_re_im (P : Measure Ω') (f g : Ω' → ℂ)
    (hre : (fun ω => (f ω).re) =ᵐ[P] fun ω => (g ω).re)
    (him : (fun ω => (f ω).im) =ᵐ[P] fun ω => (g ω).im) : f =ᵐ[P] g := by
  filter_upwards [hre, him] with ω h1 h2
  exact Complex.ext h1 h2

private lemma sd4_condExp_sup_of_indep_C (P : Measure Ω') [IsProbabilityMeasure P]
    (A X G : MeasurableSpace Ω') (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω' → ℂ) (hf : Integrable f P) (hfm : StronglyMeasurable[G] f) :
    condExp (A ⊔ X) P f =ᵐ[P] condExp A P f := by
  have hr := sd4_condExp_sup_of_indep (mΩ := mΩ) P A X G hAG hG hX hind (fun ω => (f ω).re) hf.re
    (Complex.continuous_re.comp_stronglyMeasurable hfm)
  have hi := sd4_condExp_sup_of_indep (mΩ := mΩ) P A X G hAG hG hX hind (fun ω => (f ω).im) hf.im
    (Complex.continuous_im.comp_stronglyMeasurable hfm)
  refine sd4_ae_eq_of_re_im (mΩ := mΩ) P _ _ ?_ ?_
  · exact (sd4_re_condExp (mΩ := mΩ) P _ f hf).trans (hr.trans (sd4_re_condExp (mΩ := mΩ) P _ f hf).symm)
  · exact (sd4_im_condExp (mΩ := mΩ) P _ f hf).trans (hi.trans (sd4_im_condExp (mΩ := mΩ) P _ f hf).symm)

private lemma sd4_independent_increment_zero_C (P : Measure Ω') [IsProbabilityMeasure P]
    (A X G : MeasurableSpace Ω') (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω' → ℂ) (hf : Integrable f P) :
    condExp G P (condExp (A ⊔ X) P f - condExp A P f) =ᵐ[P] fun _ => 0 := by
  have hu : Integrable (condExp (A ⊔ X) P f - condExp A P f) P :=
    integrable_condExp.sub integrable_condExp
  have hrz := sd4_independent_increment_zero (mΩ := mΩ) P A X G hAG hG hX hind (fun ω => (f ω).re)
  have hiz := sd4_independent_increment_zero (mΩ := mΩ) P A X G hAG hG hX hind (fun ω => (f ω).im)
  have hre_u : (fun ω => ((condExp (A ⊔ X) P f - condExp A P f) ω).re) =ᵐ[P]
      condExp (A ⊔ X) P (fun ω => (f ω).re) - condExp A P (fun ω => (f ω).re) := by
    filter_upwards [sd4_re_condExp (mΩ := mΩ) P (A ⊔ X) f hf, sd4_re_condExp (mΩ := mΩ) P A f hf] with ω h1 h2
    simp only [Pi.sub_apply, Complex.sub_re, h1, h2]
  have him_u : (fun ω => ((condExp (A ⊔ X) P f - condExp A P f) ω).im) =ᵐ[P]
      condExp (A ⊔ X) P (fun ω => (f ω).im) - condExp A P (fun ω => (f ω).im) := by
    filter_upwards [sd4_im_condExp (mΩ := mΩ) P (A ⊔ X) f hf, sd4_im_condExp (mΩ := mΩ) P A f hf] with ω h1 h2
    simp only [Pi.sub_apply, Complex.sub_im, h1, h2]
  refine sd4_ae_eq_of_re_im (mΩ := mΩ) P _ _ ?_ ?_
  · refine (sd4_re_condExp (mΩ := mΩ) P G _ hu).trans ?_
    refine (condExp_congr_ae hre_u).trans (hrz.trans ?_)
    exact Filter.EventuallyEq.of_eq (by funext ω; simp)
  · refine (sd4_im_condExp (mΩ := mΩ) P G _ hu).trans ?_
    refine (condExp_congr_ae him_u).trans (hiz.trans ?_)
    exact Filter.EventuallyEq.of_eq (by funext ω; simp)

/-- complex version of `cv_increment_bound` -/
private lemma sd4_increment_bound_C (P : Measure Ω') [IsProbabilityMeasure P]
    (G H : MeasurableSpace Ω') (f g : Ω' → ℂ) (D : ℝ)
    (hf : Integrable f P) (hg : Integrable g P)
    (hfg : ∀ᵐ ω ∂P, ‖f ω - g ω‖ ≤ D)
    (hcancel : condExp H P g =ᵐ[P] condExp G P g) :
    ∀ᵐ ω ∂P, ‖condExp H P f ω - condExp G P f ω‖ ≤ 2 * D := by
  have hb : ∀ J : MeasurableSpace Ω', ∀ᵐ ω ∂P, ‖condExp J P (f - g) ω‖ ≤ D := by
    intro J
    exact ae_bdd_norm_condExp_of_ae_bdd_norm (m := J) (μ := P) (f := f - g)
      (by simpa only [Pi.sub_apply] using hfg)
  filter_upwards [condExp_sub hf hg H, condExp_sub hf hg G, hcancel, hb H, hb G]
    with ω hH hG hc hHb hGb
  simp only [Pi.sub_apply] at hH hG
  have he : condExp H P f ω - condExp G P f ω =
      condExp H P (f - g) ω - condExp G P (f - g) ω := by
    have h1 : condExp H P (f - g) ω = condExp H P f ω - condExp H P g ω := hH
    have h2 : condExp G P (f - g) ω = condExp G P f ω - condExp G P g ω := hG
    rw [h1, h2, hc]; ring
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

end SD4B

/-! ### Complex coefficient `φ_j` -/

private lemma sd4_delAlpha_meas {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (z : ℂ) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) : Measurable (delAlphaC2 w F S t j z) := by
  have hG : sigmaOthers F S t j ≤ ‹MeasurableSpace Ω› :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM : Measurable (delBufAge w F S t j) := (sd4_del_measurable w F S t j).mono hG le_rfl
  have hX : Measurable (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) := S.meas _ _
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable (fun x : Vec m × Vec n => momU F.C B x) := by unfold momU; fun_prop
  have hVm : Measurable (fun x : Vec m × Vec n => momV F.C B x) := by unfold momV; fun_prop
  obtain ⟨-, c2, -⟩ := sd1_alpha_cont (m := m) (n := n) z hz hzS
  have hq : Measurable (fun ω => (delBufAge w F S t j ω,
      w j * resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω),
      momU F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω),
      momV F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω))) :=
    hM.prodMk (((hdm.comp hX).const_mul (w j)).prodMk ((hUm.comp hX).prodMk (hVm.comp hX)))
  have e2 : ∀ ω, delAlphaC2 w F S t j z ω = colAlpha2 ((delBufAge w F S t j ω).map
      (fun x : ℝ => (x : ℂ))) ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) : ℝ) : ℂ)
      (fun i => (momU F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) i : ℂ))
      (fun i => (momV F.C B (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) i : ℂ)) z := fun ω => rfl
  rw [funext e2]
  have h := sd1_meas_comp _ c2 hq
  exact h

/-- The covariance integrand is integrable at every `z` with positive real part. -/
private lemma sd4_integrable {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (z : ℂ) (hz : 0 < z.re) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => (phiJC w F S t j z ω - bjC w F S t j z) *
      XzC (delBufAge w F S t j ω) z i k) P := by
  have hG : sigmaOthers F S t j ≤ ‹MeasurableSpace Ω› :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM : Measurable (delBufAge w F S t j) := (sd4_del_measurable w F S t j).mono hG le_rfl
  have hm : Measurable (fun ω => XzC (delBufAge w F S t j ω) z i k) :=
    ((sd0_cont_X z hz).matrix_elem i k).measurable.comp hM
  have hphi : Integrable (phiJC w F S t j z) P := integrable_condExp
  refine (hphi.sub (integrable_const _)).mul_bdd hm.aestronglyMeasurable
    (c := 1 / (2 * Real.sqrt z.re)) (Filter.Eventually.of_forall fun ω => ?_)
  exact (sd0_entry_le _ i k).trans (sd0_X_bound _ z hz)

/-- Once the per-age estimate is supplied, all summation conclusions follow. -/
private lemma sd4_covariance_sum {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (z : ℂ) (C : ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w)
    (hw1 : ∀ j, w j ≤ 1)
    (hper : ∀ j, fro (CjC w F S t j z) ≤
      C * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ))) :
    Summable (fun j => fro (CjC w F S t j z)) ∧
      (∑' j, fro (CjC w F S t j z)) ≤
        C * sumPow w 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ)) := by
  have h := sd4_sum_of_sq_bound w (fun j => fro (CjC w F S t j z)) hw0 hw hw1
    (C / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ))) (fun _ => Real.sqrt_nonneg _)
    (fun j => by simpa only [div_mul_eq_mul_div] using hper j)
  simpa only [div_mul_eq_mul_div] using h

/-- The coefficient conditional expectation is uniformly bounded at each age. -/
private lemma sd4_phi_bound (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (w : ℕ → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ w j → w j ≤ 1 → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        ∀ᵐ ω ∂P, ‖phiJC w F S t j z ω‖ ≤ C * w j ^ 2 / z.re := by
  obtain ⟨C, hC⟩ := lem_app_drift_coeffmoments_sector 1 le_rfl s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S t j w hSo hSi hm hn hw0 hw1 z hs hzS
  have h := hC Ω m n B P F S t j (delBufAge w F S t j) (w j)
    hSo hSi hm hn hw0 hw1 (sd4_del_measurable w F S t j) z hs hzS
  have hbound : ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
      (fun ω => ‖delAlphaC2 w F S t j z ω‖) ω ≤ C * w j ^ 2 / z.re := by
    simpa only [pow_one, delAlphaC2] using h.2.2.2.2
  exact (norm_condExp_le (m := sigmaOthers F S t j) (μ := P) (delAlphaC2 w F S t j z)).trans
    hbound

/-- The actual deleted-sample coefficient has a finite first moment. -/
private lemma sd4_alpha2_integrable {Ω : Type} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (z : ℂ) (CS γ : ℝ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2)
    (hγ : 0 ≤ γ)
    (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hw0 : 0 ≤ w j) (hw1 : w j ≤ 1) :
    Integrable (delAlphaC2 w F S t j z) P := by
  obtain ⟨C, hC⟩ := lem_app_drift_coeffmoments_sector 1 le_rfl z.re hz CS γ hγ
  have h := hC Ω m n B P F S t j (delBufAge w F S t j) (w j)
    hSo hSi hm hn hw0 hw1 (sd4_del_measurable w F S t j) z le_rfl hzS
  have h1 : Integrable (fun ω => ‖delAlphaC2 w F S t j z ω‖) P := by
    simpa only [pow_one, delAlphaC2] using h.2.2.2.1
  exact (integrable_norm_iff (sd4_delAlpha_meas w F S t j z hz hzS).aestronglyMeasurable).mp h1

private lemma sd4_psi_meas {m n B : ℕ} (F : FrozenParams m n B) (M : Mat m n) (ϖ : ℝ) (z : ℂ)
    (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) : Measurable (fun x : Vec m × Vec n =>
      colAlpha2 (M.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z) := by
  obtain ⟨-, c2, -⟩ := sd1_alpha_cont (m := m) (n := n) z hz hzS
  have hmr : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable (fun x : Vec m × Vec n => momU F.C B x) := by unfold momU; fun_prop
  have hVm : Measurable (fun x : Vec m × Vec n => momV F.C B x) := by unfold momV; fun_prop
  have hq : Measurable (fun x : Vec m × Vec n =>
      (M, ϖ * resid F.A x, momU F.C B x, momV F.C B x)) :=
    measurable_const.prodMk ((hmr.const_mul ϖ).prodMk (hUm.prodMk hVm))
  have h := sd1_meas_comp _ c2 hq
  exact h

private lemma sd4_psi_integrable (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∀ (m n B : ℕ) (F : FrozenParams m n B) (M : Mat m n) (ϖ : ℝ) (z : ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      Integrable (fun x : Vec m × Vec n =>
        colAlpha2 (M.map (fun y : ℝ => (y : ℂ))) ((ϖ * resid F.A x : ℝ) : ℂ)
          (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z) (gaussPair m n) := by
  obtain ⟨K1, hK10, hK1⟩ := sd1_W_moment 1 (by norm_num) CS γ
  obtain ⟨cc, hcc⟩ := lem_app_de_coeff_sector s0 hs0
  intro m n B F M ϖ z hSo hSi hm hn hϖ0 hϖ1 hs hzS
  have hx : 0 < z.re := lt_of_lt_of_le hs0 hs
  obtain ⟨hWI1, -⟩ := hK1 m n B F.C ⟨hm, hn⟩ hγ ⟨hSo, hSi⟩ F.A F.hA
  refine Integrable.mono' (hWI1.const_mul (cc * ϖ ^ 2 / z.re))
    (sd4_psi_meas F M ϖ z hx hzS).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have h := (hcc M (momU F.C B x) (momV F.C B x) (resid F.A x) ϖ z hϖ0 hϖ1 hs hzS).2.1
  rw [sd1_sq_eq F x] at h
  refine h.trans (le_of_eq ?_)
  simp only [pow_one]
  ring

private lemma sd4_phiFresh_measurable {m n B : ℕ} (F : FrozenParams m n B)
    (ϖ : ℝ) (z : ℂ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    Measurable (fun K : Mat m n => phiFreshC F K ϖ z) := by
  obtain ⟨-, c2, -⟩ := sd1_alpha_cont (m := m) (n := n) z hz hzS
  have hc : Continuous (fun q : Mat m n × (Vec m × Vec n) =>
      (q.1, ϖ * dotProduct q.2.1 (Matrix.mulVec F.A q.2.2),
        momU F.C B q.2, momV F.C B q.2)) := by
    unfold momU momV
    fun_prop
  have hf : StronglyMeasurable (Function.uncurry (fun (K : Mat m n) (x : Vec m × Vec n) =>
      colAlpha2 (K.map (fun y : ℝ => (y : ℂ))) ((ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2) : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z)) :=
    (c2.comp hc).measurable.stronglyMeasurable
  haveI : IsProbabilityMeasure (freshMeas m n) := by
    change IsProbabilityMeasure (gaussPair m n)
    infer_instance
  exact (hf.integral_prod_right (ν := freshMeas m n)).measurable

private lemma sd4_phi_eq_fresh {Ω : Type} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (z : ℂ) (CS γ : ℝ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2)
    (hγ : 0 ≤ γ) (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B) (hw0 : 0 ≤ w j) (hw1 : w j ≤ 1)
    (hI : Integrable (delAlphaC2 w F S t j z) P) :
    phiJC w F S t j z =ᵐ[P] fun ω => phiFreshC F (delBufAge w F S t j ω) (w j) z := by
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  obtain ⟨-, c2, -⟩ := sd1_alpha_cont (m := m) (n := n) z hz hzS
  have hc : Continuous (fun q : Mat m n × (Vec m × Vec n) =>
      (q.1, w j * dotProduct q.2.1 (Matrix.mulVec F.A q.2.2),
        momU F.C B q.2, momV F.C B q.2)) := by
    unfold momU momV
    fun_prop
  have hψi := sd4_psi_integrable z.re hz CS γ hγ m n B F
  have hX := sd4_del_measurable w F S t j
  have hY := S.meas (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hind := sd4_others_indep F S t j
  have key : ∀ (L : ℂ →L[ℝ] ℝ),
      (fun ω => L (phiJC w F S t j z ω)) =ᵐ[P] fun ω => L (phiFreshC F (delBufAge w F S t j ω) (w j) z) := by
    intro L
    let f : Mat m n → Vec m × Vec n → ℝ := fun K x => L (colAlpha2 (K.map (fun y : ℝ => (y : ℂ)))
      ((w j * dotProduct x.1 (Matrix.mulVec F.A x.2) : ℝ) : ℂ)
        (fun i => (momU F.C B x i : ℂ)) (fun i => (momV F.C B x i : ℂ)) z)
    have hf : Measurable (Function.uncurry f) :=
      (L.continuous.comp (c2.comp hc)).measurable
    have hfint : Integrable (fun ω => f (delBufAge w F S t j ω)
        (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)) P := by
      exact L.integrable_comp hI
    have h := Muon.Foundations.freezing_condExp (sigmaOthers F S t j) hG hX hY hind hf hfint
    rw [S.law] at h
    have h1 : (fun ω => L (phiJC w F S t j z ω)) =ᵐ[P]
        condExp (sigmaOthers F S t j) P (fun ω => L (delAlphaC2 w F S t j z ω)) := by
      have := L.comp_condExp_comm (m := sigmaOthers F S t j) hI
      filter_upwards [this] with ω hω
      exact hω
    refine h1.trans (h.trans (Filter.Eventually.of_forall fun ω => ?_))
    simp only [f]
    have hint := hψi (delBufAge w F S t j ω) (w j) z hSo hSi hm hn hw0 hw1 le_rfl hzS
    have := L.integral_comp_comm hint
    simp only [phiFreshC]
    exact this
  exact sd4_ae_eq_of_re_im (mΩ := mΩ) P _ _ (key Complex.reCLM) (key Complex.imCLM)

private lemma sd4_one_slot_deletion (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB))
        inferInstance ⊔ sigmaOthers F S t j] h →
      (∀ ω, ‖h ω‖ ≤ D) → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        fro (meanC P (fun ω => h ω •
          (XzC (ageBuf F S t j M0 ϖ ω) z - XzC (M0 ω) z))) ≤
          C * D * ϖ / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_multiplier_i_sector s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t j M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD z hs hzS
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hbound := hC Ω m n B P F S t j M0 ϖ D h
    hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD z hs hzS
  rw [sd2m_tower P (sigmaOthers F S t j) hG]
  exact sd2m_fro_mean_le P _ (fun i k => integrable_condExp) _ hbound

private lemma sd4_one_slot_deletion_any (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (a : Fin B) (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ ω, ‖h ω‖ ≤ D) → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        fro (meanC P (fun ω => h ω •
          (XzC (M0 ω + (ϖ * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
            Muon.outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))
              (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) z - XzC (M0 ω) z))) ≤
          C * D * ϖ / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := sd4_one_slot_deletion s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t j a M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD z hs hzS
  let G := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let p0 : ℤ × Fin B := (t + 1 - (j : ℤ), slotOne F.hB)
  let p : ℤ × Fin B := (t + 1 - (j : ℤ), a)
  let e : (ℤ × Fin B) ≃ (ℤ × Fin B) := Equiv.swap p0 p
  let T : FrozenSamples P m n B := {
    zw := fun r b => S.zw (e (r, b)).1 (e (r, b)).2
    meas := fun r b => S.meas _ _
    indep := S.indep.precomp e.injective
    law := fun r b => S.law _ _ }
  have hep : e p0 = p := Equiv.swap_apply_left p0 p
  have hG : sigmaOthers F T t j = G := by
    change (⨆ (q : ℤ × Fin B) (_ : q ≠ p0),
      MeasurableSpace.comap (S.zw (e q).1 (e q).2) inferInstance) =
      ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    calc
      _ = ⨆ (q : ℤ × Fin B) (_ : e q ≠ p),
          MeasurableSpace.comap (S.zw (e q).1 (e q).2) inferInstance := by
        simp only [← hep, e.injective.ne_iff]
      _ = _ := e.iSup_comp (g := fun q : ℤ × Fin B =>
        ⨆ (_ : q ≠ p), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
  have hsample : T.zw (t + 1 - (j : ℤ)) (slotOne F.hB) =
      S.zw (t + 1 - (j : ℤ)) a := by
    change S.zw (e p0).1 (e p0).2 = _
    rw [hep]
  have hM0' : Measurable[sigmaOthers F T t j] M0 := hG.symm ▸ hM0
  have hh' : Measurable[MeasurableSpace.comap
      (T.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔ sigmaOthers F T t j] h := by
    rw [hsample, hG]
    exact hh
  have hbound := hC Ω m n B P F T t j M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0' hh' hD z hs hzS
  simpa only [ageBuf, ageD, ageU, ageV, sampleD, resid, hsample] using hbound

private lemma sd4_minor_deletion_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ ω, ‖h ω‖ ≤ D) → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      fro (meanC P (fun ω => h ω •
        (XzC (delBufAge w F S t j ω) z - XzC (Z ω) z))) ≤
        C * D * w k / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := sd4_one_slot_deletion_any s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD z hs hzS
  have he : meanC P (fun ω => h ω •
      (XzC (delBufAge w F S t j ω) z - XzC (Z ω) z)) =
      meanC P (fun ω => h ω •
        (XzC (Z ω + (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) z - XzC (Z ω) z)) := by
    ext i r
    apply integral_congr_ae
    filter_upwards [hdec] with ω hω
    simp only [hω]
  rw [he]
  exact hC Ω m n B P F S t k a Z (w k) D h hSo hSi hm hn hw0 hw1 hZ hh hD z hs hzS

private lemma sd4_minor_deletion_bound_ae (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ᵐ ω ∂P, ‖h ω‖ ≤ D) → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      fro (meanC P (fun ω => h ω •
        (XzC (delBufAge w F S t j ω) z - XzC (Z ω) z))) ≤
        C * D * w k / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := sd4_minor_deletion_bound s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD z hs hzS
  classical
  let h' : Ω → ℂ := fun ω => if ‖h ω‖ ≤ D then h ω else 0
  have hD0 : 0 ≤ D := by
    obtain ⟨ω, hω⟩ := hD.exists
    exact (norm_nonneg _).trans hω
  have he : h' =ᵐ[P] h := by
    filter_upwards [hD] with ω hω
    simp only [h', if_pos hω]
  have hh' : Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
      ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h' := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
      ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    exact Measurable.ite (measurableSet_le hh.norm measurable_const) hh measurable_const
  have hb : ∀ ω, ‖h' ω‖ ≤ D := by
    intro ω
    by_cases hω : ‖h ω‖ ≤ D
    · simpa only [h', if_pos hω] using hω
    · simpa only [h', if_neg hω, norm_zero] using hD0
  have hbnd := hC Ω m n B P F S w t j k a Z D h' hSo hSi hm hn hw0 hw1 hZ hdec hh' hb z hs hzS
  have hmean : meanC P (fun ω => h' ω •
      (XzC (delBufAge w F S t j ω) z - XzC (Z ω) z)) =
      meanC P (fun ω => h ω •
      (XzC (delBufAge w F S t j ω) z - XzC (Z ω) z)) := by
    ext i r
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    simp only [hω]
  rwa [hmean] at hbnd

private lemma sd4_phi_replace_bound (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (F : FrozenParams m n B) (K : Mat m n)
      (c c' : ℝ) (u u' : Vec m) (v v' : Vec n) (ϖ : ℝ) (z : ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        ‖phiFreshC F (K + c • Muon.outer u v) ϖ z -
          phiFreshC F (K + c' • Muon.outer u' v') ϖ z‖ ≤
          2 * C * ϖ ^ 2 / (Real.sqrt z.re * B) := by
  obtain ⟨C, hC⟩ := lem_app_drift_rank_sector s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro m n B F K c c' u u' v v' ϖ z hSo hSi hm hn hϖ0 hϖ1 hs hzS
  have h := hC m n B F (K + c • Muon.outer u v) (K + c' • Muon.outer u' v') ϖ z 2
    hSo hSi hm hn hϖ0 hϖ1 hs hzS (sd4_rank_replace K c c' u u' v v')
  convert h using 1 <;> ring

private lemma sd4_phi_minor_difference (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j : ℕ) (Z : Ω → Mat m n)
      (c : Ω → ℝ) (u : Ω → Vec m) (v : Ω → Vec n),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w j → w j ≤ 1 →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω + c ω • Muon.outer (u ω) (v ω)) →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      ∀ᵐ ω ∂P, ‖phiJC w F S t j z ω - phiFreshC F (Z ω) (w j) z‖ ≤
        2 * C * w j ^ 2 / (Real.sqrt z.re * B) := by
  obtain ⟨C, hC⟩ := sd4_phi_replace_bound s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S w t j Z c u v hSo hSi hm hn hw0 hw1 hdec z hs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hI := sd4_alpha2_integrable w F S t j z CS γ hz hzS hγ hSo hSi hm hn hw0 hw1
  have hfresh := sd4_phi_eq_fresh w F S t j z CS γ hz hzS hγ hSo hSi hm hn hw0 hw1 hI
  filter_upwards [hfresh, hdec] with ω hω hωdec
  rw [hω, hωdec]
  simpa only [zero_smul, add_zero] using
    hC m n B F (Z ω) (c ω) 0 (u ω) (u ω) (v ω) (v ω) (w j) z
      hSo hSi hm hn hw0 hw1 hs hzS

private lemma sd4_future_increment_zero {Ω : Type} (A : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (p : ℤ × Fin B) (hp : t + 1 < p.1)
    (hAG : A ≤ ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
    (z : ℂ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) (hI : Integrable (delAlphaC2 w F S t j z) P)
    (CS γ : ℝ) (hγ : 0 ≤ γ) (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B) (hw0 : 0 ≤ w j) (hw1 : w j ≤ 1) :
    (fun ω => condExp (A ⊔ MeasurableSpace.comap (S.zw p.1 p.2) inferInstance)
      P (phiJC w F S t j z) ω - condExp A P (phiJC w F S t j z) ω) =ᵐ[P] fun _ => 0 := by
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let X : MeasurableSpace Ω := MeasurableSpace.comap (S.zw p.1 p.2) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hX : X ≤ mΩ := (S.meas _ _).comap_le
  let g := fun ω => phiFreshC F (delBufAge w F S t j ω) (w j) z
  have he : phiJC w F S t j z =ᵐ[P] g :=
    sd4_phi_eq_fresh w F S t j z CS γ hz hzS hγ hSo hSi hm hn hw0 hw1 hI
  have hgm : StronglyMeasurable[G] g :=
    ((sd4_phiFresh_measurable F (w j) z hz hzS).comp
      (sd4_del_measurable_future w F S t j p hp)).stronglyMeasurable
  have hgI : Integrable g P :=
    (show Integrable (phiJC w F S t j z) P from integrable_condExp).congr he
  have hc := sd4_condExp_sup_of_indep_C (mΩ := mΩ) P A X G hAG hG hX (sd4_slot_indep S p) g hgI hgm
  have hH := condExp_congr_ae (m := A ⊔ X) he
  have hA := condExp_congr_ae (m := A) he
  filter_upwards [hc, hH, hA] with ω hcω hHω hAω
  change condExp (A ⊔ X) P (phiJC w F S t j z) ω - condExp A P (phiJC w F S t j z) ω = 0
  rw [hHω, hAω, hcω, sub_self]

private lemma sd4_phi_increment_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) (A X G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (m n B : ℕ)
      (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j : ℕ) (Z : Ω → Mat m n)
      (c : Ω → ℝ) (u : Ω → Vec m) (v : Ω → Vec n),
      A ≤ G → G ≤ mΩ → X ≤ mΩ → Indep G X P →
      Measurable[G] Z →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w j → w j ≤ 1 →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω + c ω • Muon.outer (u ω) (v ω)) →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      ∀ᵐ ω ∂P, ‖condExp (A ⊔ X) P (phiJC w F S t j z) ω -
        condExp A P (phiJC w F S t j z) ω‖ ≤
          4 * C * w j ^ 2 / (Real.sqrt z.re * B) := by
  obtain ⟨C, hC⟩ := sd4_phi_minor_difference s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω A X G mΩ m n B P _ F S w t j Z c u v hAG hG hX hind hZ
    hSo hSi hm hn hw0 hw1 hdec z hs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hs
  let f := phiJC w F S t j z
  let g := fun ω => phiFreshC F (Z ω) (w j) z
  let D := 2 * C * w j ^ 2 / (Real.sqrt z.re * B)
  have hf : Integrable f P := by
    dsimp [f, phiJC]
    exact integrable_condExp
  have hgm : StronglyMeasurable[G] g :=
    ((sd4_phiFresh_measurable F (w j) z hz hzS).comp hZ).stronglyMeasurable
  have hfg : ∀ᵐ ω ∂P, ‖f ω - g ω‖ ≤ D :=
    hC Ω m n B P F S w t j Z c u v hSo hSi hm hn hw0 hw1 hdec z hs hzS
  have hg : Integrable g P := by
    refine (hf.norm.add (integrable_const D)).mono' (hgm.mono hG).aestronglyMeasurable ?_
    filter_upwards [hfg] with ω hω
    have ht : ‖g ω‖ ≤ ‖f ω‖ + ‖f ω - g ω‖ := by
      have := norm_sub_le (f ω) (f ω - g ω)
      simpa only [sub_sub_cancel] using this
    simpa only [Pi.add_apply] using ht.trans (add_le_add_right hω ‖f ω‖)
  have hc := sd4_condExp_sup_of_indep_C (mΩ := mΩ) P A X G hAG hG hX hind g hg hgm
  have hb := sd4_increment_bound_C (mΩ := mΩ) P A (A ⊔ X) f g D hf hg hfg hc
  have hD : 2 * D = 4 * C * w j ^ 2 / (Real.sqrt z.re * B) := by dsimp [D]; ring
  simpa only [hD] using hb

private lemma sd4_deleted_mean_zero {Ω : Type*} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hG : G ≤ mΩ) (h : Ω → ℂ) (Z : Ω → Matrix (Fin m) (Fin n) ℂ)
    (hI : Integrable h P) (hZ : ∀ i k, Measurable[G] (fun ω => Z ω i k))
    (hIZ : ∀ i k, Integrable (fun ω => h ω * Z ω i k) P)
    (hz : condExp G P h =ᵐ[P] fun _ => 0) :
    @meanC Ω mΩ _ _ P (fun ω => h ω • Z ω) = 0 := by
  ext i k
  change (∫ ω, h ω * Z ω i k ∂P) = 0
  have hentry : StronglyMeasurable[G] (fun ω => Z ω i k) := (hZ i k).stronglyMeasurable
  have hpull := condExp_bilin_of_stronglyMeasurable_right (m := G) (μ := P)
    (ContinuousLinearMap.mul ℝ ℂ) (f := h) (g := fun ω => Z ω i k) hentry
    (by simpa using hIZ i k) hI
  have hzero : condExp G P (fun ω => h ω * Z ω i k) =ᵐ[P] fun _ => 0 := by
    filter_upwards [hpull, hz] with ω hω hω0
    have : condExp G P (fun ω => h ω * Z ω i k) ω = condExp G P h ω * Z ω i k := by
      simpa using hω
    rw [this, hω0, zero_mul]
  calc
    _ = ∫ ω, condExp G P (fun ω => h ω * Z ω i k) ω ∂P := (integral_condExp hG).symm
    _ = 0 := by rw [integral_congr_ae hzero, integral_zero]

private lemma sd4_deleted_term_identity {Ω : Type*} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hG : G ≤ mΩ) (h : Ω → ℂ) (X Z : Ω → Matrix (Fin m) (Fin n) ℂ)
    (hI : Integrable h P) (hZ : ∀ i k, Measurable[G] (fun ω => Z ω i k))
    (hIX : ∀ i k, Integrable (fun ω => h ω * X ω i k) P)
    (hIZ : ∀ i k, Integrable (fun ω => h ω * Z ω i k) P)
    (hz : condExp G P h =ᵐ[P] fun _ => 0) :
    @meanC Ω mΩ _ _ P (fun ω => h ω • X ω) =
      @meanC Ω mΩ _ _ P (fun ω => h ω • (X ω - Z ω)) := by
  have hzero := sd4_deleted_mean_zero G P hG h Z hI hZ hIZ hz
  ext i k
  have hentry := congrArg (fun M : Matrix (Fin m) (Fin n) ℂ => M i k) hzero
  change (∫ ω, h ω * Z ω i k ∂P) = 0 at hentry
  change (∫ ω, h ω * X ω i k ∂P) = ∫ ω, h ω * (X ω i k - Z ω i k) ∂P
  simp_rw [mul_sub]
  rw [integral_sub (hIX i k) (hIZ i k), hentry, sub_zero]

private lemma sd4_minor_covariance_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℂ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ᵐ ω ∂P, ‖h ω‖ ≤ D) → Integrable h P →
      (condExp (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) P h =ᵐ[P] fun _ => 0) →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      fro (meanC P (fun ω => h ω •
        XzC (delBufAge w F S t j ω) z)) ≤
        C * D * w k / (z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := sd4_minor_deletion_bound_ae s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD hI hz z hs hzS
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hGj : sigmaOthers F S t j ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hspos := hs0.trans_le hs
  have hc : Continuous (fun M : Mat m n => XzC M z) := sd0_cont_X z hspos
  have hXm : Measurable (fun ω => XzC (delBufAge w F S t j ω) z) :=
    hc.measurable.comp ((sd4_del_measurable w F S t j).mono hGj le_rfl)
  have hZm : ∀ i r, Measurable[G] (fun ω => XzC (Z ω) z i r) := fun i r =>
    ((hc.matrix_elem i r).measurable).comp hZ
  have hbound : ∀ M : Mat m n, ∀ i r, ‖XzC M z i r‖ ≤ 1 / (2 * Real.sqrt z.re) :=
    fun M i r => (sd0_entry_le _ i r).trans (sd0_X_bound M z hspos)
  have hIX : ∀ i r, Integrable (fun ω => h ω * XzC (delBufAge w F S t j ω) z i r) P := by
    intro i r
    exact hI.mul_bdd
      ((((measurable_pi_apply r).comp ((measurable_pi_apply i).comp hXm))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => hbound _ i r)
  have hIZ : ∀ i r, Integrable (fun ω => h ω * XzC (Z ω) z i r) P := by
    intro i r
    exact hI.mul_bdd (((hZm i r).mono hG le_rfl).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => hbound _ i r)
  rw [sd4_deleted_term_identity G P hG h _ _ hI hZm hIX hIZ hz]
  exact hC Ω m n B P F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD z hs hzS

private lemma sd4_martingale_slot_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) (A : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
      (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (hw : WeightSeq w) (t : ℤ) (j k : ℕ) (a : Fin B),
      (t + 1 - (k : ℤ), a) ≠ (t + 1 - (j : ℤ), slotOne F.hB) →
      A ≤ (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ w j → w j ≤ 1 → 0 ≤ w k → w k ≤ 1 → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      fro (meanC P (fun ω =>
        (condExp (A ⊔ MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance)
          P (phiJC w F S t j z) ω - condExp A P (phiJC w F S t j z) ω) •
          XzC (delBufAge w F S t j ω) z)) ≤
        C * w j ^ 2 * w k / (z.re * Real.sqrt z.re * B * Real.sqrt (B : ℝ)) := by
  obtain ⟨CR, hR⟩ := sd4_phi_increment_bound s0 hs0 CS γ hγ
  obtain ⟨CM, hM⟩ := sd4_minor_covariance_bound s0 hs0 CS γ hγ
  refine ⟨4 * CM * CR, ?_⟩
  intro Ω A mΩ m n B P _ F S w hw t j k a hne hAG hSo hSi hm hn hwj0 hwj1 hwk0 hwk1 z hs hzS
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let X : MeasurableSpace Ω := MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hX : X ≤ mΩ := (S.meas _ _).comap_le
  have hind : Indep G X P := sd4_slot_indep S _
  obtain ⟨Z, hZ, _, hdec⟩ := sd4_double_deletion w hw F S t j k a hne
  let f := phiJC w F S t j z
  let h : Ω → ℂ := condExp (A ⊔ X) P f - condExp A P f
  let D : ℝ := 4 * CR * w j ^ 2 / (Real.sqrt z.re * B)
  have hbd : ∀ᵐ ω ∂P, ‖h ω‖ ≤ D :=
    hR Ω A X G m n B P F S w t j Z
      (fun ω => w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω))
      (fun ω => momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
      (fun ω => momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
      hAG hG hX hind hZ hSo hSi hm hn hwj0 hwj1 hdec z hs hzS
  have hI : Integrable h P :=
    (integrable_condExp (m := A ⊔ X) (μ := P) (f := f)).sub integrable_condExp
  have hz : condExp G P h =ᵐ[P] fun _ => 0 :=
    sd4_independent_increment_zero_C (mΩ := mΩ) P A X G hAG hG hX hind f integrable_condExp
  have hhH : Measurable[A ⊔ X] h :=
    (show StronglyMeasurable[A ⊔ X] (condExp (A ⊔ X) P f) from
      stronglyMeasurable_condExp).measurable.sub
      ((show StronglyMeasurable[A] (condExp A P f) from
        stronglyMeasurable_condExp).mono le_sup_left).measurable
  have hh : Measurable[X ⊔ G] h := hhH.mono
    (sup_le (hAG.trans le_sup_right) le_sup_left) le_rfl
  have hb := hM Ω m n B P F S w t j k a Z D h hSo hSi hm hn hwk0 hwk1 hZ hdec hh hbd hI hz z hs hzS
  calc
    _ ≤ CM * D * w k / (z.re * Real.sqrt (B : ℝ)) := hb
    _ = _ := by dsimp [D]; simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

private lemma sd4_tendsto_of_re_im (g : ℕ → ℂ) (w : ℂ)
    (h1 : Tendsto (fun l => (g l).re) atTop (𝓝 w.re))
    (h2 : Tendsto (fun l => (g l).im) atTop (𝓝 w.im)) : Tendsto g atTop (𝓝 w) := by
  have e : g = fun l => ((g l).re : ℂ) + ((g l).im : ℂ) * Complex.I := by
    funext l; exact (Complex.re_add_im (g l)).symm
  have hw : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I := (Complex.re_add_im w).symm
  rw [e, hw]
  exact ((Complex.continuous_ofReal.tendsto _).comp h1).add
    (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const _)

private lemma sd4_ae_tendsto_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Filtration ℕ mΩ) (f : Ω → ℂ)
    (hf : Integrable f P) (hfm : StronglyMeasurable[⨆ l, A l] f) :
    ∀ᵐ ω ∂P, Tendsto (fun l => condExp (A l) P f ω) atTop (𝓝 (f ω)) := by
  have hr := hf.re.tendsto_ae_condExp (ℱ := A)
    (Complex.continuous_re.comp_stronglyMeasurable hfm)
  have hi := hf.im.tendsto_ae_condExp (ℱ := A)
    (Complex.continuous_im.comp_stronglyMeasurable hfm)
  have hre : ∀ l, ∀ᵐ ω ∂P, (condExp (A l) P f ω).re = condExp (A l) P (fun ω => (f ω).re) ω :=
    fun l => sd4_re_condExp (mΩ := mΩ) P (A l) f hf
  have him : ∀ l, ∀ᵐ ω ∂P, (condExp (A l) P f ω).im = condExp (A l) P (fun ω => (f ω).im) ω :=
    fun l => sd4_im_condExp (mΩ := mΩ) P (A l) f hf
  rw [← ae_all_iff] at hre him
  filter_upwards [hr, hi, hre, him] with ω h1 h2 h3 h4
  refine sd4_tendsto_of_re_im _ _ ?_ ?_
  · simp only [h3]; exact h1
  · simp only [h4]; exact h2

private lemma sd4_martingale_expansion {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Filtration ℕ mΩ)
    (hA0 : A 0 = ⊥) (f X : Ω → ℂ) (K L : ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable[⨆ l, A l] f)
    (hfbd : ∀ᵐ ω ∂P, ‖f ω‖ ≤ K) (hXm : Measurable X) (hXbd : ∀ ω, ‖X ω‖ ≤ L) :
    Tendsto (fun N => ∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P f ω - condExp (A l) P f ω) * X ω ∂P)
      atTop (𝓝 (∫ ω, (f ω - ∫ ζ, f ζ ∂P) * X ω ∂P)) := by
  have hcb : ∀ l, ∀ᵐ ω ∂P, ‖condExp (A l) P f ω‖ ≤ K := by
    intro l
    exact ae_bdd_norm_condExp_of_ae_bdd_norm (m := A l) (μ := P) (f := f) (R := K) hfbd
  have hprod : ∀ l, Integrable (fun ω => condExp (A l) P f ω * X ω) P := by
    intro l
    exact integrable_condExp.mul_bdd hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hXbd ω)
  have hfprod : Integrable (fun ω => f ω * X ω) P :=
    hf.mul_bdd hXm.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => hXbd ω)
  have hcprod : Integrable (fun ω => (∫ ζ, f ζ ∂P) * X ω) P :=
    (integrable_const _).mul_bdd hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hXbd ω)
  have hconv : Tendsto (fun N => ∫ ω, condExp (A N) P f ω * X ω ∂P)
      atTop (𝓝 (∫ ω, f ω * X ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K * L)
      (fun l => (hprod l).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro l
      filter_upwards [hcb l] with ω hω
      rw [norm_mul]
      exact mul_le_mul hω (hXbd ω) (norm_nonneg _) ((norm_nonneg _).trans hω)
    · filter_upwards [sd4_ae_tendsto_condExp P A f hf hfm] with ω hω
      exact hω.mul_const (X ω)
  have hsum : ∀ N, (∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P f ω - condExp (A l) P f ω) * X ω ∂P) =
      (∫ ω, condExp (A N) P f ω * X ω ∂P) -
        ∫ ω, condExp (A 0) P f ω * X ω ∂P := by
    intro N
    calc
      _ = ∑ l ∈ Finset.range N, ((∫ ω, condExp (A (l + 1)) P f ω * X ω ∂P) -
          ∫ ω, condExp (A l) P f ω * X ω ∂P) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp_rw [sub_mul]
        exact integral_sub (hprod (l + 1)) (hprod l)
      _ = _ := Finset.sum_range_sub (fun l => ∫ ω, condExp (A l) P f ω * X ω ∂P) N
  have hbot : condExp (A 0) P f = fun _ => ∫ ζ, f ζ ∂P := by
    rw [hA0, condExp_bot]
  have hfinal := hconv.sub_const (∫ ω, (∫ ζ, f ζ ∂P) * X ω ∂P)
  simp_rw [hsum, hbot]
  have heq : (∫ ω, (f ω - ∫ ζ, f ζ ∂P) * X ω ∂P) =
      (∫ ω, f ω * X ω ∂P) - ∫ ω, (∫ ζ, f ζ ∂P) * X ω ∂P := by
    simp_rw [sub_mul]
    exact integral_sub hfprod hcprod
  rw [heq]
  exact hfinal

private lemma sd4_Cj_expansion {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (z : ℂ) (hz : 0 < z.re) (K : ℝ)
    (hphi : ∀ᵐ ω ∂P, ‖phiJC w F S t j z ω‖ ≤ K)
    (A : Filtration ℕ mΩ) (hA0 : A 0 = ⊥) (hAe : (⨆ l, A l) = sigmaOthers F S t j)
    (i : Fin m) (k : Fin n) :
    Tendsto (fun N => ∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P (phiJC w F S t j z) ω -
        condExp (A l) P (phiJC w F S t j z) ω) *
        XzC (delBufAge w F S t j ω) z i k ∂P)
      atTop (𝓝 (CjC w F S t j z i k)) := by
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM : Measurable (delBufAge w F S t j) :=
    (sd4_del_measurable w F S t j).mono hG le_rfl
  have hX : Measurable (fun ω => XzC (delBufAge w F S t j ω) z i k) :=
    ((sd0_cont_X z hz).matrix_elem i k).measurable.comp hM
  have hfm : StronglyMeasurable[⨆ l, A l] (phiJC w F S t j z) := by
    rw [hAe]
    exact stronglyMeasurable_condExp
  have hbound : ∀ ω, ‖XzC (delBufAge w F S t j ω) z i k‖ ≤ 1 / (2 * Real.sqrt z.re) :=
    fun ω => (sd0_entry_le _ i k).trans (sd0_X_bound _ z hz)
  have h := sd4_martingale_expansion P A hA0 (phiJC w F S t j z)
    (fun ω => XzC (delBufAge w F S t j ω) z i k) K (1 / (2 * Real.sqrt z.re))
    integrable_condExp hfm hphi hX hbound
  simpa only [CjC, bjC, meanC, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul] using h

open scoped Matrix.Norms.Frobenius in
private lemma sd4_fro_sum_le {m n ι : Type*} [Fintype m] [Fintype n]
    (Y : ι → Matrix m n ℂ) (U : Finset ι) :
    Real.sqrt (∑ i, ∑ k, ‖(∑ l ∈ U, Y l) i k‖ ^ 2) ≤
      ∑ l ∈ U, Real.sqrt (∑ i, ∑ k, ‖Y l i k‖ ^ 2) := by
  simpa only [Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow] using
    (norm_sum_le U Y)

private lemma sd4_Cj_bound_of_finite_slot_budget {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (z : ℂ) (hz : 0 < z.re) (L K : ℝ)
    (hphi : ∀ᵐ ω ∂P, ‖phiJC w F S t j z ω‖ ≤ L)
    (A : Filtration ℕ mΩ) (hA0 : A 0 = ⊥) (hAe : (⨆ l, A l) = sigmaOthers F S t j)
    (hbudget : ∀ N, (∑ l ∈ Finset.range N, fro (meanC P (fun ω =>
      (condExp (A (l + 1)) P (phiJC w F S t j z) ω -
        condExp (A l) P (phiJC w F S t j z) ω) •
        XzC (delBufAge w F S t j ω) z))) ≤ K) :
    fro (CjC w F S t j z) ≤ K := by
  let Y : ℕ → Matrix (Fin m) (Fin n) ℂ := fun l => meanC P (fun ω =>
    (condExp (A (l + 1)) P (phiJC w F S t j z) ω -
      condExp (A l) P (phiJC w F S t j z) ω) • XzC (delBufAge w F S t j ω) z)
  have hlim : Tendsto (fun N => ∑ l ∈ Finset.range N, Y l) atTop (𝓝 (CjC w F S t j z)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => ?_
    simpa only [Y, meanC, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.sum_apply] using
      sd4_Cj_expansion w F S t j z hz L hphi A hA0 hAe i k
  have hc : Continuous (fun M : Matrix (Fin m) (Fin n) ℂ => fro M) := by unfold fro; fun_prop
  refine le_of_tendsto (hc.continuousAt.tendsto.comp hlim) (Eventually.of_forall fun N => ?_)
  exact (sd4_fro_sum_le Y (Finset.range N)).trans (hbudget N)

private lemma sd4_fro_mean_smul_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n : ℕ} (P : Measure Ω) (h : Ω → ℂ) (X : Ω → Matrix (Fin m) (Fin n) ℂ)
    (hz : h =ᵐ[P] fun _ => 0) : fro (@meanC Ω mΩ _ _ P (fun ω => h ω • X ω)) = 0 := by
  have he : @meanC Ω mΩ _ _ P (fun ω => h ω • X ω) = 0 := by
    ext i k
    change (∫ ω, h ω * X ω i k ∂P) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with ω hω
    simp [hω]
  rw [he]
  simp [fro]

private lemma sd4_covariance_per_age (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (w : ℕ → ℝ),
      ((∀ k, 0 ≤ w k) ∧ Summable w ∧ (∀ k, w k ≤ 1) ∧ (∑' k, w k) ≤ 1) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 → ∀ j,
      fro (CjC w F S t j z) ≤ C * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C0, hslot⟩ := sd4_martingale_slot_bound s0 hs0 CS γ hγ
  obtain ⟨L, hL⟩ := sd4_phi_bound s0 hs0 CS γ hγ
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t w hw hSo hSi hm hn z hs hzS j
  obtain ⟨hw0, hw, hw1, hws⟩ := hw
  have hsp : 0 < z.re := hs0.trans_le hs
  have hB : 0 < (B : ℝ) := by exact_mod_cast F.hB
  have hphi := hL Ω m n B P F S t j w hSo hSi hm hn (hw0 j) (hw1 j) z hs hzS
  by_cases hwne : ∃ k, w k ≠ 0
  · have hW : WeightSeq w := ⟨hw0, hw, hwne⟩
    have hI := sd4_alpha2_integrable w F S t j z CS γ hsp hzS hγ hSo hSi hm hn (hw0 j) (hw1 j)
    obtain ⟨A, hA, hA0, hAe⟩ := sd4_sample_filtration F S t j
    let M : ℤ × Fin B → MeasurableSpace Ω := fun p =>
      MeasurableSpace.comap (S.zw p.1 p.2) inferInstance
    let d : ℤ × Fin B := (t + 1 - (j : ℤ), slotOne F.hB)
    let f : ℕ → ℝ := fun l => fro (meanC P (fun ω =>
      (condExp (A (l + 1)) P (phiJC w F S t j z) ω -
        condExp (A l) P (phiJC w F S t j z) ω) • XzC (delBufAge w F S t j ω) z))
    let K := C * w j ^ 2 / (z.re * Real.sqrt z.re * B * Real.sqrt (B : ℝ))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hreveal : ∀ p, p ≠ d → A (Encodable.encode p + 1) = A (Encodable.encode p) ⊔ M p := by
      intro p hp
      rw [hA, hA]
      exact sd4_encoded_reveal M d p hp
    have hpast : ∀ p, A (Encodable.encode p) ≤ ⨆ (q : ℤ × Fin B) (_ : q ≠ p), M q := by
      intro p
      rw [hA]
      exact sd4_encoded_past_le M d p
    have hgap : ∀ l, (∀ p, p ≠ d → Encodable.encode p ≠ l) → f l = 0 := by
      intro l hg
      have he : A (l + 1) = A l := by
        rw [hA, hA]
        exact sd4_encoded_no_reveal M d l hg
      apply sd4_fro_mean_smul_zero
      rw [he]
      exact Eventually.of_forall fun _ => sub_self _
    have hzero : ∀ l, (∀ (k : ℕ) (a : Fin B),
        Encodable.encode (t + 1 - (k : ℤ), a) ≠ l) → f l = 0 := by
      intro l hl
      by_cases hr : ∃ p : ℤ × Fin B, p ≠ d ∧ Encodable.encode p = l
      · obtain ⟨p, hp, hcode⟩ := hr
        have hfuture : t + 1 < p.1 := by
          by_contra hnot
          have ht : p.1 ≤ t + 1 := le_of_not_gt hnot
          have he : (t + 1 - (((t + 1 - p.1).toNat : ℕ) : ℤ), p.2) = p := by
            apply Prod.ext
            · dsimp
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr ht)]
              ring
            · rfl
          apply hl (t + 1 - p.1).toNat p.2
          rw [he]
          exact hcode
        subst l
        apply sd4_fro_mean_smul_zero
        rw [hreveal p hp]
        exact sd4_future_increment_zero (A (Encodable.encode p)) w F S t j p hfuture
          (hpast p) z hsp hzS hI CS γ hγ hSo hSi hm hn (hw0 j) (hw1 j)
      · apply hgap l
        intro p hp he
        exact hr ⟨p, hp, he⟩
    have hper : ∀ (k : ℕ) (a : Fin B),
        f (Encodable.encode (t + 1 - (k : ℤ), a)) ≤ K * w k := by
      intro k a
      let p : ℤ × Fin B := (t + 1 - (k : ℤ), a)
      by_cases hp : p = d
      · have he : f (Encodable.encode p) = 0 := hgap _ (by
          intro q hq hcode
          exact hq ((Encodable.encode_injective hcode).trans hp))
        change f (Encodable.encode p) ≤ K * w k
        rw [he]
        exact mul_nonneg hK (hw0 k)
      · have hb : f (Encodable.encode p) ≤
            C0 * w j ^ 2 * w k / (z.re * Real.sqrt z.re * B * Real.sqrt (B : ℝ)) := by
          simpa only [f, hreveal p hp] using
            hslot Ω (A (Encodable.encode p)) m n B P F S w hW t j k a hp
              (hpast p) hSo hSi hm hn (hw0 j) (hw1 j) (hw0 k) (hw1 k) z hs hzS
        calc
          _ ≤ C0 * w j ^ 2 * w k / (z.re * Real.sqrt z.re * B * Real.sqrt (B : ℝ)) := hb
          _ ≤ C * w j ^ 2 * w k / (z.re * Real.sqrt z.re * B * Real.sqrt (B : ℝ)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C0 0) (sq_nonneg (w j))) (hw0 k)
          _ = K * w k := by dsimp [K]; ring
    apply sd4_Cj_bound_of_finite_slot_budget w F S t j z hsp (L * w j ^ 2 / z.re)
      (C * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ))) hphi A hA0 hAe
    intro N
    have hb := sd4_encoded_weight_budget t w hw0 hw hws f K hK hzero hper N
    have he : K * B = C * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ)) := by
      dsimp [K]
      field_simp
      <;> ring
    exact hb.trans_eq he
  · have hwj : w j = 0 := by by_contra hj; exact hwne ⟨j, hj⟩
    have hz0 : phiJC w F S t j z =ᵐ[P] fun _ => 0 := by
      filter_upwards [hphi] with ω hω
      have : ‖phiJC w F S t j z ω‖ ≤ 0 := by simpa [hwj] using hω
      exact norm_le_zero_iff.mp this
    have hbj : bjC w F S t j z = 0 := by
      unfold bjC
      rw [integral_congr_ae hz0]
      simp
    have he : fro (CjC w F S t j z) = 0 := by
      apply sd4_fro_mean_smul_zero (h := fun ω => phiJC w F S t j z ω - bjC w F S t j z)
      filter_upwards [hz0] with ω hω
      simp [hω, hbj]
    rw [he, hwj]
    simp


/-- `lem:app-drift-covariance` (`eqn:app-drift-covariance`) at `z ∈ 𝕊`, snapshot `cr-2026-10-23`
(source as in `lem_app_drift_multiplier_i_sector`, ll. 858–861): `‖𝒞_j‖_F ≤ C w_j²/(x^{3/2}√B)` and
the summed bound. Real counterpart `Muon.Drift.lem_app_drift_covariance_weights`
(`Covariance.lean`:1715), same shape and weight hypotheses. -/
theorem lem_app_drift_covariance_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (w : ℕ → ℝ),
      ((∀ j, 0 ≤ w j) ∧ Summable w ∧ (∀ j, w j ≤ 1) ∧ (∑' j, w j) ≤ 1) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        (∀ (j : ℕ) (i : Fin m) (k : Fin n),
            Integrable (fun ω => (phiJC w F S t j z ω - bjC w F S t j z) *
              XzC (delBufAge w F S t j ω) z i k) P) ∧
        (∀ j : ℕ, fro (CjC w F S t j z) ≤
          C * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ))) ∧
        Summable (fun j : ℕ => fro (CjC w F S t j z)) ∧
        (∑' j : ℕ, fro (CjC w F S t j z)) ≤
          C * sumPow w 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := sd4_covariance_per_age s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S t w hw hSo hSi hm hn z hs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hper := hC Ω m n B P F S t w hw hSo hSi hm hn z hs hzS
  exact ⟨fun j i k => sd4_integrable w F S t j z hz i k, hper,
    sd4_covariance_sum w F S t z C hw.1 hw.2.1 hw.2.2.1 hper⟩

/-! ## Exact identity and assembly over `𝕊` -/

/-! ### Helpers for `lem_app_drift_exact_sector` (task P-E.15.P3) -/

private lemma sd5_coord_le {b : ℕ} (x : Vec b) (i : Fin b) : |x i| ≤ eucNorm x := by
  have h1 : x i ^ 2 ≤ ∑ k, x k ^ 2 :=
    Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  exact Real.abs_le_sqrt h1

private lemma sd5_L1 [IsProbabilityMeasure P]
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig) (s' : ℤ) (a : Fin B) :
    Integrable (fun ω => |resid F.A (S.zw s' a ω)| * eucNorm (momU F.C B (S.zw s' a ω)) *
      eucNorm (momV F.C B (S.zw s' a ω))) P ∧
    ∫ ω, |resid F.A (S.zw s' a ω)| * eucNorm (momU F.C B (S.zw s' a ω)) *
      eucNorm (momV F.C B (S.zw s' a ω)) ∂P ≤ 7 * CSig * γ := by
  set q : Vec m × Vec n → ℝ := fun x => |resid F.A x| * eucNorm (momU F.C B x) *
    eucNorm (momV F.C B x) with hq
  have hqm : Measurable q := by
    simp only [hq, resid, eucNorm, momU, momV]
    fun_prop
  have hq2 := lem_app_de_moments_iii F.C B γ CSig hdim hγ hC F.A F.hA
  have hmem : MemLp q 2 (gaussPair m n) := lt_of_le_of_lt hq2.1 ENNReal.ofReal_lt_top
  have hzw : P.map (S.zw s' a) = gaussPair m n := S.law s' a
  have hqz : MemLp (fun ω => q (S.zw s' a ω)) 2 P := by
    exact MemLp.comp_of_map (g := q) (by rw [hzw]; exact hmem) (S.meas s' a).aemeasurable
  have hint : Integrable (fun ω => q (S.zw s' a ω)) P := hqz.integrable one_le_two
  refine ⟨hint, ?_⟩
  have h1 : ∫ ω, q (S.zw s' a ω) ∂P = ∫ x, q x ∂(gaussPair m n) := by
    rw [← hzw, integral_map (S.meas s' a).aemeasurable hqm.aestronglyMeasurable]
  show ∫ ω, q (S.zw s' a ω) ∂P ≤ _
  rw [h1]
  have hq0 : ∀ x, 0 ≤ q x := fun x =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hl1 : eLpNorm q 1 (gaussPair m n) ≤ ENNReal.ofReal (7 * CSig * γ) := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le one_le_two).trans ?_
    exact hq2.1.trans (ENNReal.ofReal_le_ofReal hq2.2)
  have hCS0 : 0 ≤ CSig := (sd2_opNorm_nonneg_real _).trans hC.1
  have hnn : 0 ≤ 7 * CSig * γ := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hq0) hqm.aestronglyMeasurable]
  have h2 : ∫⁻ x, ENNReal.ofReal (q x) ∂(gaussPair m n) = eLpNorm q 1 (gaussPair m n) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hq0 x)]
    all_goals exact hqm.aestronglyMeasurable
  rw [h2]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl1).trans_eq (ENNReal.toReal_ofReal hnn)

private lemma sd5_decomp [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (a : Fin B) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = WeightedBufDel w F S t (t + 1 - (j : ℤ)) a ω +
      (w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) a j rfl ω (hω t)
  rw [h, sd4_sample, smul_smul]

private lemma sd5_term_eq {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (M : Mat m n) (z : ℂ) (j : ℕ) (t : ℤ) (ω : Ω) :
    Rres M (-z) * ((w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω).map (fun x : ℝ => (x : ℂ))) =
      ∑ a : Fin B, vecMulVec ((((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) : ℝ) : ℂ)) •
        (Rres M (-z) *ᵥ (fun i => (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ))))
        (fun i => (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ)) := by
  have h1 : w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω = ∑ a : Fin B,
      (w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
    rw [frozenBatchG_eq_sum, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sd4_sample, smul_smul]
  rw [h1]
  have h2 : (∑ a : Fin B, (w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))).map
        (fun x : ℝ => (x : ℂ)) = ∑ a : Fin B, vecMulVec ((((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) : ℝ) : ℂ)) •
          (fun i => (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ)))
        (fun i => (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ)) := by
    ext i k
    simp [Matrix.sum_apply, Muon.outer, Matrix.vecMulVec_apply]
  rw [h2, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Matrix.mul_vecMulVec, Matrix.mulVec_smul]

private lemma sd5_series [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) :
    ∀ᵐ ω ∂P, HasSum (fun j : ℕ => ∑ a : Fin B,
      vecMulVec ((((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) : ℝ) : ℂ)) •
        (Rres (WeightedBuf w F S t ω) (-z) *ᵥ
          (fun i => (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ))))
        (fun i => (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω) i : ℂ)))
      (XzC (WeightedBuf w F S t ω) z) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h1 : HasSum (fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
      (WeightedBuf w F S t ω) := (hω t).hasSum
  let f : Mat m n →+ Matrix (Fin m) (Fin n) ℂ :=
    { toFun := fun N => Rres (WeightedBuf w F S t ω) (-z) * N.map (fun x : ℝ => (x : ℂ))
      map_zero' := by simp
      map_add' := fun N N' => by
        have : (N + N').map (fun x : ℝ => (x : ℂ)) =
            N.map (fun x : ℝ => (x : ℂ)) + N'.map (fun x : ℝ => (x : ℂ)) := by
          ext i k; simp
        rw [this, Matrix.mul_add] }
  have hcont : Continuous f := by
    show Continuous (fun N : Mat m n => Rres (WeightedBuf w F S t ω) (-z) *
      N.map (fun x : ℝ => (x : ℂ)))
    exact continuous_const.matrix_mul (Continuous.matrix_map continuous_id Complex.continuous_ofReal)
  have h2 := h1.map f hcont
  have h3 : HasSum (fun j : ℕ => Rres (WeightedBuf w F S t ω) (-z) *
      ((w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω).map (fun x : ℝ => (x : ℂ))))
      (XzC (WeightedBuf w F S t ω) z) := h2
  simp only [sd5_term_eq] at h3
  exact h3

private lemma sd5_pt_bound {m n : ℕ} (K : Mat m n) (z : ℂ) (hz : 0 < z.re) (c : ℝ) (u : Vec m)
    (v : Vec n) (i : Fin m) (k : Fin n) :
    ‖vecMulVec ((c : ℂ) • (Rres K (-z) *ᵥ (fun l => (u l : ℂ)))) (fun l => (v l : ℂ)) i k‖ ≤
      |c| / z.re * (eucNorm u * eucNorm v) := by
  have hu : ‖(EuclideanSpace.equiv (Fin m) ℂ).symm (fun l => (u l : ℂ))‖ = eucNorm u := by
    have h1 := sd3q_cast_euc_sq u
    have h2 := sd1pf_eucNorm_sq u
    exact (sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp (h1.trans h2.symm)
  have hR := sd0_R_bound K z hz
  have h1 : ‖(Rres K (-z) *ᵥ (fun l => (u l : ℂ))) i‖ ≤ 1 / z.re * eucNorm u := by
    have e1 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin m) ℂ).symm
      (Rres K (-z) *ᵥ (fun l => (u l : ℂ)))) i
    have e2 := sd3q_apply_bound (Rres K (-z)) (fun l => (u l : ℂ))
    rw [hu] at e2
    exact e1.trans (e2.trans (mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg _)))
  have h2 : ‖(fun l => (v l : ℂ)) k‖ ≤ eucNorm v := by
    simpa [Complex.norm_real] using sd5_coord_le v k
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, norm_mul]
  have hc : ‖(c : ℂ)‖ = |c| := Complex.norm_real c
  rw [hc]
  calc |c| * ‖(Rres K (-z) *ᵥ fun l => (u l : ℂ)) i‖ * ‖(v k : ℂ)‖
      ≤ |c| * (1 / z.re * eucNorm u) * eucNorm v := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 (abs_nonneg _)) ?_ (norm_nonneg _)
          (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (Real.sqrt_nonneg _)))
        simpa using h2
    _ = |c| / z.re * (eucNorm u * eucNorm v) := by ring

private lemma sd5_Psi_meas {α : Type*} [MeasurableSpace α] {m n B : ℕ} (F : FrozenParams m n B)
    (c : ℝ) (z : ℂ) (hz : 0 < z.re) (i : Fin m) (k : Fin n)
    (K : α → Mat m n) (x : α → Vec m × Vec n) (hK : Measurable K) (hx : Measurable x) :
    Measurable (fun q : α =>
      vecMulVec ((((c * resid F.A (x q) : ℝ)) : ℂ) • (Rres (K q) (-z) *ᵥ
        (fun l => (momU F.C B (x q) l : ℂ)))) (fun l => (momV F.C B (x q) l : ℂ)) i k) := by
  have hd : Measurable (fun q : α => resid F.A (x q)) :=
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp hx
  have hu : Measurable (fun q : α => momU F.C B (x q)) :=
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp hx
  have hv : Measurable (fun q : α => momV F.C B (x q)) :=
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp hx
  have hR : Measurable (fun q : α => Rres (K q) (-z)) :=
    (sd0_cont_R z hz).measurable.comp hK
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
  refine (Complex.measurable_ofReal.comp ((measurable_const.mul hd))).mul ?_ |>.mul ?_
  · refine Finset.measurable_sum _ fun l _ => ?_
    exact ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hR)).mul
      (Complex.measurable_ofReal.comp ((measurable_pi_apply l).comp hu))
  · exact Complex.measurable_ofReal.comp ((measurable_pi_apply k).comp hv)

private lemma sd5_col {m n : ℕ} (M0 : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n) (z : ℂ)
    (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    vecMulVec ((h : ℂ) • (Rres (M0 + h • outer u v) (-z) *ᵥ (fun l => (u l : ℂ))))
        (fun l => (v l : ℂ)) =
      colAlpha1 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun l => (u l : ℂ)) (fun l => (v l : ℂ)) z •
          (Rres M0 (-z) * vecMulVec (fun l => (u l : ℂ)) (fun l => (v l : ℂ)))
        - colAlpha2 (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun l => (u l : ℂ))
            (fun l => (v l : ℂ)) z •
          (XzC M0 z * vecMulVec (fun l => (v l : ℂ)) (fun l => (v l : ℂ))) := by
  obtain ⟨hL, hdel, -⟩ := lem_app_de_deletion_sector M0 h u v (M0 + h • outer u v) z rfl hz hzS
  have hcol := lem_app_drift_column_field_i ((M0 + h • outer u v).map (fun x : ℝ => (x : ℂ)))
    (M0.map (fun x : ℝ => (x : ℂ))) (h : ℂ) z (fun l => (u l : ℂ)) (fun l => (v l : ℂ)) hL hdel
  rw [rres_neg_eq_colR, rres_neg_eq_colR, hcol]
  unfold XzC
  rw [rres_neg_eq_colR]
  ext i k
  simp [Matrix.mul_vecMulVec, vecMulVec_apply, colX, sub_mul]
  ring

private lemma sd5_meas_del {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s : ℤ) (a : Fin B) :
    Measurable (WeightedBufDel w F S t s a) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := sd0_hQ F
  unfold WeightedBufDel
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact hQ.comp (S.meas _ _)

private lemma sd5_shift_meas {m n B : ℕ} (F : FrozenParams m n B) (c : ℝ) :
    Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      q.1 + (c * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) := by
  have hd : Measurable (fun q : Mat m n × (Vec m × Vec n) => resid F.A q.2) :=
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp measurable_snd
  have hu : Measurable (fun q : Mat m n × (Vec m × Vec n) => momU F.C B q.2) :=
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp measurable_snd
  have hv : Measurable (fun q : Mat m n × (Vec m × Vec n) => momV F.C B q.2) :=
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp measurable_snd
  refine measurable_pi_iff.2 fun i' => measurable_pi_iff.2 fun k' => ?_
  simp only [Matrix.add_apply, Matrix.smul_apply, Muon.outer, Matrix.vecMulVec_apply, smul_eq_mul]
  have h1 : Measurable (fun q : Mat m n × (Vec m × Vec n) => q.1 i' k') :=
    (measurable_pi_apply k').comp ((measurable_pi_apply i').comp measurable_fst)
  have h2 : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      c * resid F.A q.2 * (momU F.C B q.2 i' * momV F.C B q.2 k')) :=
    ((measurable_const (a := c)).mul hd).mul
      (((measurable_pi_apply i').comp hu).mul ((measurable_pi_apply k').comp hv))
  exact h1.add h2

private lemma sd5_slot [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) (j : ℕ) (a : Fin B) (i : Fin m) (k : Fin n) :
    ∫ ω, vecMulVec ((((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) : ℝ) : ℂ)) •
        (Rres (WeightedBuf w F S t ω) (-z) *ᵥ
          (fun l => (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω) l : ℂ))))
        (fun l => (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω) l : ℂ)) i k ∂P =
      ∫ ω, (delAlphaC1 w F S t j z ω • (Rres (delBufAge w F S t j ω) (-z) *
              vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))
          - delAlphaC2 w F S t j z ω • (XzC (delBufAge w F S t j ω) z *
              vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) i k ∂P := by
  set s' : ℤ := t + 1 - (j : ℤ) with hs'
  set Φ : Mat m n × (Vec m × Vec n) → ℂ := fun q =>
    vecMulVec ((((w j * resid F.A q.2 : ℝ)) : ℂ) •
      (Rres (q.1 + (w j * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) (-z) *ᵥ
        (fun l => (momU F.C B q.2 l : ℂ)))) (fun l => (momV F.C B q.2 l : ℂ)) i k with hΦ
  have hΦm : Measurable Φ :=
    sd5_Psi_meas F (w j) z hz i k _ _ (sd5_shift_meas F (w j)) measurable_snd
  have hpair : ∀ b : Fin B, Measurable (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω)) :=
    fun b => (sd5_meas_del w F S t s' b).prodMk (S.meas _ _)
  have step1 : ∀ b : Fin B, ∫ ω, vecMulVec ((((w j * resid F.A (S.zw s' b ω) : ℝ) : ℂ)) •
        (Rres (WeightedBuf w F S t ω) (-z) *ᵥ
          (fun l => (momU F.C B (S.zw s' b ω) l : ℂ))))
        (fun l => (momV F.C B (S.zw s' b ω) l : ℂ)) i k ∂P =
      ∫ ω, Φ (WeightedBufDel w F S t s' b ω, S.zw s' b ω) ∂P := by
    intro b
    refine integral_congr_ae ?_
    filter_upwards [sd5_decomp w hw F S t j b] with ω hω
    simp only [hΦ]
    rw [hω]
  have step2 : ∀ b : Fin B, ∫ ω, Φ (WeightedBufDel w F S t s' b ω, S.zw s' b ω) ∂P =
      ∫ q, Φ q ∂(P.map (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω))) := by
    intro b
    rw [integral_map (hpair b).aemeasurable hΦm.aestronglyMeasurable]
  have step3 : ∫ ω, Φ (WeightedBufDel w F S t s' (slotOne F.hB) ω,
      S.zw s' (slotOne F.hB) ω) ∂P = ∫ ω, (delAlphaC1 w F S t j z ω •
            (Rres (delBufAge w F S t j ω) (-z) *
              vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))
          - delAlphaC2 w F S t j z ω • (XzC (delBufAge w F S t j ω) z *
              vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) i k ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hc := sd5_col (delBufAge w F S t j ω) (w j * resid F.A (S.zw s' (slotOne F.hB) ω))
      (momU F.C B (S.zw s' (slotOne F.hB) ω)) (momV F.C B (S.zw s' (slotOne F.hB) ω)) z hz hzS
    exact congrArg (fun X : Matrix (Fin m) (Fin n) ℂ => X i k) hc
  rw [step1 a, step2 a, weightedBufDel_law_slot_invariant w hw F S t s' a (slotOne F.hB),
    ← step2 (slotOne F.hB), step3]

/-- `lem:app-drift-exact` at `z ∈ 𝕊` for a general weight sequence, snapshot `cr-2026-10-23`
(`sections/05-dynamics/section.tex` ll. 871–872: "The exact identity `lem:app-drift-exact` holds for
`z ∈ 𝕊` by the same derivation from the column identity"):
`𝓗(z) = B ∑_j 𝔼[α_{1,j} R_0^{(j)}(𝗎_j⊗𝗏_j) − α_{2,j} 𝖷_0^{(j)}(𝗏_j⊗𝗏_j)]`, the series as `HasSum`.
Real counterpart `Muon.Drift.lem_app_drift_exact_weights` (`Tail.lean`:536). -/
theorem lem_app_drift_exact_sector {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (z : ℂ) (hz : 0 < z.re) (hzS : |z.im| ≤ z.re / 2) :
    HasSum (fun j : ℕ => (B : ℂ) • meanC P (fun ω =>
        delAlphaC1 w F S t j z ω • (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))
          - delAlphaC2 w F S t j z ω • (XzC (delBufAge w F S t j ω) z *
            vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))))
      (HmixC w F S t z) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  set γ : ℝ := ((m : ℝ) + n) / B with hγdef
  set CSig : ℝ := opNorm F.C.Sout + opNorm F.C.Sin with hCdef
  have hγ : 0 ≤ γ := by positivity
  have hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ) := by
    have : γ * (B : ℝ) = (m : ℝ) + n := by rw [hγdef]; field_simp
    rw [this]
    exact ⟨by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)], by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]⟩
  have hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig :=
    ⟨by linarith [sd2_opNorm_nonneg_real F.C.Sin], by linarith [sd2_opNorm_nonneg_real F.C.Sout]⟩
  have hCS0 : 0 ≤ CSig := add_nonneg (sd2_opNorm_nonneg_real _) (sd2_opNorm_nonneg_real _)
  have hw0 := hw.1.1
  refine Pi.hasSum.2 fun i => Pi.hasSum.2 fun k => ?_
  set Tm : ℕ → Fin B → Ω → ℂ := fun j a ω => vecMulVec
    ((((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) : ℝ) : ℂ)) •
      (Rres (WeightedBuf w F S t ω) (-z) *ᵥ
        (fun l => (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω) l : ℂ))))
      (fun l => (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω) l : ℂ)) i k with hTm
  set qa : ℕ → Fin B → Ω → ℝ := fun j a ω =>
    |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * eucNorm (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) *
      eucNorm (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) with hqa
  have hL1 := fun j a => sd5_L1 F S γ CSig hdim hγ hC (t + 1 - (j : ℤ)) a
  have hpt : ∀ j a ω, ‖Tm j a ω‖ ≤ w j / z.re * qa j a ω := by
    intro j a ω
    refine (sd5_pt_bound _ z hz _ _ _ i k).trans (le_of_eq ?_)
    simp only [hqa]
    rw [abs_mul, abs_of_nonneg (hw0 j)]
    ring
  have hTint : ∀ j a, Integrable (Tm j a) P := fun j a => by
    refine ((hL1 j a).1.const_mul (w j / z.re)).mono'
      (sd5_Psi_meas F (w j) z hz i k _ _ (sd0_meas_WB w F S t) (S.meas _ _)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => hpt j a ω)
  have hFint : ∀ j, Integrable (fun ω => ∑ a : Fin B, Tm j a ω) P := fun j =>
    integrable_finsetSum _ fun a _ => hTint j a
  have hgi : ∀ j, Integrable (fun ω => ∑ a : Fin B, w j / z.re * qa j a ω) P := fun j =>
    integrable_finsetSum _ fun a _ => (hL1 j a).1.const_mul _
  have hnormle : ∀ j, ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P ≤ (B * (7 * CSig * γ) / z.re) * w j := by
    intro j
    calc ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P ≤ ∫ ω, ∑ a : Fin B, w j / z.re * qa j a ω ∂P :=
          integral_mono (hFint j).norm (hgi j) fun ω =>
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => hpt j a ω)
      _ = ∑ a : Fin B, w j / z.re * (∫ ω, qa j a ω ∂P) := by
          rw [integral_finsetSum _ fun a _ => (hL1 j a).1.const_mul _]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_const_mul]
      _ ≤ ∑ a : Fin B, w j / z.re * (7 * CSig * γ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (hL1 j a).2 (div_nonneg (hw0 j) hz.le)
      _ = (B * (7 * CSig * γ) / z.re) * w j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsum : Summable fun j => ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => norm_nonneg _) hnormle
      (hw.1.2.1.mul_left _)
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsum
  have hE : ∫ ω, ∑' j, ∑ a : Fin B, Tm j a ω ∂P = HmixC w F S t z i k := by
    unfold HmixC meanC
    simp only [Matrix.of_apply]
    refine integral_congr_ae ?_
    filter_upwards [sd5_series w hw F S t z] with ω hω
    have h' : HasSum (fun j => ∑ a : Fin B, Tm j a ω) (XzC (WeightedBuf w F S t ω) z i k) := by
      have h2 := Pi.hasSum.1 (Pi.hasSum.1 hω i) k
      simp only [Matrix.sum_apply] at h2
      exact h2
    exact h'.tsum_eq
  rw [hE] at hHS
  convert hHS using 1
  funext j
  simp only [Matrix.smul_apply, smul_eq_mul, meanC, Matrix.of_apply]
  rw [integral_finsetSum _ fun a _ => hTint j a]
  rw [Finset.sum_congr rfl fun a _ => sd5_slot w hw F S t z hz hzS j a i k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-! ### Helpers for `tl_S_sector`, `tl_Q_sector` (task P-E.15.P3) -/

section SD6
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd6_meanC_congr (P : Measure Ω') {m n : ℕ} (F F' : Ω' → Matrix (Fin m) (Fin n) ℂ)
    (h : ∀ᵐ ω ∂P, F ω = F' ω) : meanC P F = meanC P F' := by
  ext i k
  simp only [meanC, Matrix.of_apply]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

private lemma sd6_meanC_smul (P : Measure Ω') {m n : ℕ} (c : ℂ)
    (F : Ω' → Matrix (Fin m) (Fin n) ℂ) :
    meanC P (fun ω => c • F ω) = c • meanC P F := by
  ext i k
  simp only [meanC, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

private lemma sd6_meanC_add (P : Measure Ω') {m n : ℕ} (F F' : Ω' → Matrix (Fin m) (Fin n) ℂ)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    meanC P (fun ω => F ω + F' ω) = meanC P F + meanC P F' := by
  ext i k
  simp only [meanC, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hF i k) (hF' i k)

private lemma sd6_meanC_sub (P : Measure Ω') {m n : ℕ} (F F' : Ω' → Matrix (Fin m) (Fin n) ℂ)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    meanC P (fun ω => F ω - F' ω) = meanC P F - meanC P F' := by
  ext i k
  simp only [meanC, Matrix.of_apply, Matrix.sub_apply]
  exact integral_sub (hF i k) (hF' i k)

private lemma sd6_meanC_mul_right (P : Measure Ω') {m n r : ℕ}
    (F : Ω' → Matrix (Fin m) (Fin n) ℂ) (A : Matrix (Fin n) (Fin r) ℂ)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) :
    meanC P (fun ω => F ω * A) = meanC P F * A := by
  ext i k
  simp only [meanC, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun l _ => (hF i l).mul_const _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact integral_mul_const _ _

open scoped Matrix.Norms.Frobenius in
private lemma sd6_fro_smul {k l : ℕ} (c : ℂ) (A : Matrix (Fin k) (Fin l) ℂ) :
    fro (c • A) = ‖c‖ * fro A := by
  rw [fro_eq_norm, fro_eq_norm]; exact norm_smul _ _

private lemma sd6_opNorm_one (d : ℕ) : opNorm (1 : Matrix (Fin d) (Fin d) ℂ) ≤ 1 := by
  refine sd0_opNorm_le _ zero_le_one fun x => ?_
  simp

private lemma sd6_one_entry (d : ℕ) (i k : Fin d) : ‖(1 : Matrix (Fin d) (Fin d) ℂ) i k‖ ≤ 1 := by
  by_cases h : i = k <;> simp [Matrix.one_apply, h]

private lemma sd6_indep {m n B : ℕ} {P : Measure Ω'} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    sigmaOthers F S t j ≤ mΩ ∧
    Indep (MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance)
      (sigmaOthers F S t j) P := by
  set X : Ω' → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hG : sigmaOthers F S t j ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  refine ⟨hG, ?_⟩
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  exact hind.symm

private lemma sd6_int_uv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℂ) (he : MemLp e 2 P) (a : Fin m) (b : Fin n) :
    Integrable (fun ω => (e ω • (Muon.outer (momU C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) a b) P := by
  have h := sd2_int_cplx_mul P e (fun ω => momU C B (X ω) a * momV C B (X ω) b)
    (sd2_int_uv (mΩ := mΩ) P C X hX _ he.re a b) (sd2_int_uv (mΩ := mΩ) P C X hX _ he.im a b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Muon.outer, Matrix.vecMulVec_apply]

private lemma sd6_int_vv {m n B : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (C : Covariances m n) (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℂ) (he : MemLp e 2 P) (a b : Fin n) :
    Integrable (fun ω => (e ω • (Muon.outer (momV C B (X ω)) (momV C B (X ω))).map
      (fun x : ℝ => (x : ℂ))) a b) P := by
  have h := sd2_int_cplx_mul P e (fun ω => momV C B (X ω) a * momV C B (X ω) b)
    (sd2_int_vv (mΩ := mΩ) P C X hX _ he.re a b) (sd2_int_vv (mΩ := mΩ) P C X hX _ he.im a b)
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp [Muon.outer, Matrix.vecMulVec_apply]

end SD6

private lemma sd6_facts (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlphaC1 w F S t j z) ∧
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlphaC2 w F S t j z) ∧
        MemLp (delAlphaC1 w F S t j z) 2 P ∧ MemLp (delAlphaC2 w F S t j z) 2 P ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => ‖delAlphaC1 w F S t j z ω‖ ^ 2) ζ) ≤ Cc * w j) ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => ‖delAlphaC2 w F S t j z ω‖ ^ 2) ζ) ≤ Cc * w j ^ 2 / z.re) := by
  obtain ⟨C2, hC2⟩ := lem_app_drift_coeffmoments_sector 2 (by norm_num) s0 hs0 CS γ hγ
  refine ⟨|C2|, abs_nonneg _, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hM0 := sd4_del_measurable w F S t j
  obtain ⟨-, ⟨i1, c1⟩, -, ⟨i2, c2⟩⟩ :=
    hC2 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1 hM0 z hs hzS
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  obtain ⟨hG, -⟩ := sd6_indep F S t j
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hX.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hM0c : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delBufAge w F S t j) := hM0.mono le_sup_right le_rfl
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hXc
  have hVm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hXc
  have hDm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => w j * resid F.A (X ω)) := (hdm.comp hXc).const_mul (w j)
  have hq : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => (delBufAge w F S t j ω, w j * resid F.A (X ω), momU F.C B (X ω),
        momV F.C B (X ω))) :=
    hM0c.prodMk (hDm.prodMk (hUm.prodMk hVm))
  obtain ⟨c1', c2', -⟩ := sd1_alpha_cont (m := m) (n := n) z hspos hzS
  have e1 : ∀ ω, delAlphaC1 w F S t j z ω = colAlpha1 ((delBufAge w F S t j ω).map
      (fun x : ℝ => (x : ℂ))) ((w j * resid F.A (X ω) : ℝ) : ℂ)
      (fun i => (momU F.C B (X ω) i : ℂ)) (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have e2 : ∀ ω, delAlphaC2 w F S t j z ω = colAlpha2 ((delBufAge w F S t j ω).map
      (fun x : ℝ => (x : ℂ))) ((w j * resid F.A (X ω) : ℝ) : ℂ)
      (fun i => (momU F.C B (X ω) i : ℂ)) (fun i => (momV F.C B (X ω) i : ℂ)) z := fun ω => rfl
  have hA1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlphaC1 w F S t j z) := by
    rw [funext e1]
    have h := sd2_meas_comp' _ c1' hq
    exact h
  have hA2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlphaC2 w F S t j z) := by
    rw [funext e2]
    have h := sd2_meas_comp' _ c2' hq
    exact h
  have L1 : MemLp (delAlphaC1 w F S t j z) 2 P :=
    sd2_memLp2 P _ (delAlphaC1 w F S t j z) 1 (hA1.mono hGc le_rfl)
      (fun ω => by rw [one_mul]) i1
  have L2 : MemLp (delAlphaC2 w F S t j z) 2 P :=
    sd2_memLp2 P _ (delAlphaC2 w F S t j z) 1 (hA2.mono hGc le_rfl)
      (fun ω => by rw [one_mul]) i2
  refine ⟨hA1, hA2, L1, L2, ?_, ?_⟩
  · have := sd2_cond_sq P (sigmaOthers F S t j) (delAlphaC1 w F S t j z)
      (delAlphaC1 w F S t j z) 1 (|C2| * w j) zero_le_one (by positivity)
      (hA1.mono hGc le_rfl) (fun ω => by rw [one_mul]) i1
      (by filter_upwards [c1] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
    simpa using this
  · have := sd2_cond_sq P (sigmaOthers F S t j) (delAlphaC2 w F S t j z)
      (delAlphaC2 w F S t j z) 1 (|C2| * w j ^ 2 / z.re) zero_le_one (by positivity)
      (hA2.mono hGc le_rfl) (fun ω => by rw [one_mul]) i2
      (by filter_upwards [c2] with ω h
          exact h.trans_eq (by rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]))
    simpa using this

/-- Source term per age at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 875–878, first display): `‖B 𝔼[α_{1,j} R_0^{(j)}(𝗎_j⊗𝗏_j)]‖_F ≤ K w_j/x`, the per-age form of
```latex
\Big\|B\sum_j\EE\big[\alpha_{1,j}R_0^{(j)}(\mathsf u_j\tensor\mathsf v_j)\big]\Big\|_\F\le\frac Cx,
```
for `Re z ≥ s₀`. Real counterpart `Muon.Drift.tl_S` (`Tail.lean`:1406, there `s ≥ 1`). -/
theorem tl_S_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        (∀ i k, Integrable (fun ω => (delAlphaC1 w F S t j z ω •
            (Rres (delBufAge w F S t j ω) (-z) *
              vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) i k) P) ∧
        fro ((B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
            (Rres (delBufAge w F S t j ω) (-z) *
              vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ))))) ≤
          K * w j / z.re := by
  obtain ⟨Cc, hCc0, hCc⟩ := sd6_facts s0 hs0 CS γ hγ
  refine ⟨CS * Cc, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hCo
  obtain ⟨e1m, -, L1, -, k1, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := sd6_indep F S t j
  have hM0 := sd4_del_measurable w F S t j
  have hR0m : ∀ i k, Measurable[sigmaOthers F S t j]
      (fun ω => Rres (delBufAge w F S t j ω) (-z) i k) :=
    fun i k => ((sd0_cont_R (m := m) (n := n) z hspos).matrix_elem i k).measurable.comp hM0
  have hRb : ∀ ω, opNorm (Rres (delBufAge w F S t j ω) (-z)) ≤ 1 / z.re :=
    fun ω => sd0_R_bound _ z hspos
  have hF' := sd6_int_uv (B := B) P F.C X hlaw _ L1
  have hmeas1 : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => (1 : Matrix (Fin n) (Fin n) ℂ) i k) :=
    fun i k => measurable_const
  have hb1 : ∀ (ω : Ω) i k, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i k‖ ≤ 1 := fun ω i k =>
    sd6_one_entry n i k
  have hLb : ∀ ω i k, ‖Rres (delBufAge w F S t j ω) (-z) i k‖ ≤ 1 / z.re :=
    fun ω i k => (sd0_entry_le _ i k).trans (hRb ω)
  have hrew' : ∀ ω, delAlphaC1 w F S t j z ω •
      (Rres (delBufAge w F S t j ω) (-z) *
        vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ))) =
      Rres (delBufAge w F S t j ω) (-z) * (delAlphaC1 w F S t j z ω •
        (Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))).map (fun x : ℝ => (x : ℂ))) *
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro ω
    rw [Matrix.mul_one, Matrix.mul_smul]
    congr 2
    ext i k
    simp [Muon.outer, Matrix.vecMulVec_apply, ageU, ageV, hXdef]
  have hrew := funext hrew'
  have hint := sd2_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Rres (delBufAge w F S t j ω) (-z)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
    (1 / z.re) 1 (by positivity) hR0m hmeas1 hLb hb1 _ hF'
  refine ⟨fun i k => ?_, ?_⟩
  · exact (hint i k).congr (Filter.Eventually.of_forall fun ω => by dsimp only; rw [hrew' ω])
  · rw [hrew]
    have hK := sd2_bessel_uv (mΩ := inst) P F.C CS hB hCo hCi X hlaw (sigmaOthers F S t j) hG
      hindc _ e1m L1
    have hT := sd2_term (mΩ := inst) P (sigmaOthers F S t j) hG
      (fun ω => Rres (delBufAge w F S t j ω) (-z)) (fun _ => (1 : Matrix (Fin n) (Fin n) ℂ))
      (1 / z.re) 1 (by positivity) zero_le_one hR0m hmeas1 hLb hb1 _ hF' (1 / z.re) 1
      (CS / B * (Cc * w j)) (by positivity) zero_le_one (by positivity) hRb
      (fun _ => sd6_opNorm_one n)
      (by
        filter_upwards [hK.mono fun ζ h => h.1, k1] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    rw [sd6_fro_smul, Complex.norm_natCast, sd2m_tower (mΩ := inst) P (sigmaOthers F S t j) hG]
    have hc := sd2m_fro_mean_le (mΩ := inst) P _ (fun i k => integrable_condExp) _ hT
    calc (B : ℝ) * _ ≤ (B : ℝ) * (1 / z.re * (CS / B * (Cc * w j)) * 1) :=
          mul_le_mul_of_nonneg_left hc hBr.le
      _ = _ := by field_simp

section SD6Q
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

open scoped MatrixOrder in
private lemma sd6_rIn_symm {m n : ℕ} (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

open scoped MatrixOrder in
private lemma sd6_rIn_sq {m n : ℕ} (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma sd6_B_outer_vv {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B)
    (x : Vec m × Vec n) :
    (B : ℝ) • Muon.outer (momV C B x) (momV C B x) = rIn C * Muon.outer x.2 x.2 * rIn C := by
  have hv : Matrix.vecMul x.2 (rIn C) = Matrix.mulVec (rIn C) x.2 := by
    rw [← Matrix.vecMul_transpose, sd6_rIn_symm]
  have h1 : rIn C * Muon.outer x.2 x.2 * rIn C =
      Muon.outer (Matrix.mulVec (rIn C) x.2) (Matrix.mulVec (rIn C) x.2) := by
    rw [Muon.outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
  rw [h1]
  unfold momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have haa : (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hBr.le]; exact mul_inv_cancel₀ hBr.ne'
  calc (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) i * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) k))
      = ((B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹)) *
        ((rIn C *ᵥ x.2) i * (rIn C *ᵥ x.2) k) := by ring
    _ = _ := by rw [haa, one_mul]

private lemma sd6_gram_cond {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω')
    (hG : G ≤ mΩ) (hind : Indep (MeasurableSpace.comap X inferInstance) G P) (e : Ω' → ℂ)
    (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e) (he2 : MemLp e 2 P) :
    (∀ᵐ ζ ∂P, condExpMatC G P
        (fun ω => e ω • (Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ))) ζ =
      condExp G P e ζ • (1 : Matrix (Fin n) (Fin n) ℂ) +
        condExpMatC G P (fun ω => e ω • ((Muon.outer (X ω).2 (X ω).2).map
          (fun x : ℝ => (x : ℂ)) - 1)) ζ) ∧
    (∀ᵐ ζ ∂P, fro (condExpMatC G P (fun ω => e ω • ((Muon.outer (X ω).2 (X ω).2).map
        (fun x : ℝ => (x : ℂ)) - 1)) ζ) ≤
      Real.sqrt 2 * Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ)) := by
  have hei : Integrable e P := he2.integrable one_le_two
  have hi1 : ∀ i k : Fin n, Integrable
      (fun ω => ((((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k : ℝ)) : ℂ) * e ω) P := by
    intro i k
    have h := sd2_int_cplx_mul (mΩ := mΩ) P e (fun ω => (X ω).2 i * (X ω).2 k - (1 : Mat n n) i k)
      (by
        have := sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_snd (mΩ := mΩ) P X hX i k) he2.re
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only [RCLike.re_to_complex, RCLike.im_to_complex]; ring)
      (by
        have := sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_snd (mΩ := mΩ) P X hX i k) he2.im
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        simp only [RCLike.re_to_complex, RCLike.im_to_complex]; ring)
    exact h.congr (Filter.Eventually.of_forall fun ω => by simp only; ring)
  have hone : ∀ i k : Fin n, ((1 : Mat n n) i k : ℂ) = (1 : Matrix (Fin n) (Fin n) ℂ) i k := by
    intro i k
    by_cases h : i = k <;> simp [Matrix.one_apply, h]
  have hent : ∀ i k : Fin n, (fun ω => (e ω • ((Muon.outer (X ω).2 (X ω).2).map
      (fun x : ℝ => (x : ℂ)) - 1)) i k) =
      fun ω => ((((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k : ℝ)) : ℂ) * e ω := by
    intro i k; funext ω
    simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, smul_eq_mul, Muon.outer,
      Matrix.vecMulVec_apply]
    rw [← hone]
    push_cast
    ring
  have hent2 : ∀ i k : Fin n, (fun ω => (e ω • (Muon.outer (X ω).2 (X ω).2).map
      (fun x : ℝ => (x : ℂ))) i k) =
      fun ω => ((((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k : ℝ)) : ℂ) * e ω +
        ((1 : Mat n n) i k : ℂ) * e ω := by
    intro i k; funext ω
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Muon.outer,
      Matrix.vecMulVec_apply]
    push_cast
    ring
  constructor
  · have hall : ∀ i k : Fin n, ∀ᵐ ζ ∂P,
        condExpMatC G P (fun ω => e ω • (Muon.outer (X ω).2 (X ω).2).map
          (fun x : ℝ => (x : ℂ))) ζ i k =
        ((condExp G P e ζ • (1 : Matrix (Fin n) (Fin n) ℂ) +
          condExpMatC G P (fun ω => e ω • ((Muon.outer (X ω).2 (X ω).2).map
            (fun x : ℝ => (x : ℂ)) - 1)) ζ : Matrix (Fin n) (Fin n) ℂ)) i k := by
      intro i k
      have h1 : condExp G P (fun ω => ((((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k : ℝ)) : ℂ) *
          e ω + ((1 : Mat n n) i k : ℂ) * e ω) =ᵐ[P]
          (condExp G P (fun ω => ((((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k : ℝ)) : ℂ) * e ω) +
            condExp G P (fun ω => ((1 : Mat n n) i k : ℂ) * e ω)) :=
        condExp_add (hi1 i k) (hei.const_mul _) G
      have h2 := condExp_smul (μ := P) (((1 : Mat n n) i k : ℂ)) e G
      filter_upwards [h1, h2] with ζ h1ζ h2ζ
      show condExp G P (fun ω' => (e ω' • (Muon.outer (X ω').2 (X ω').2).map
          (fun x : ℝ => (x : ℂ))) i k) ζ = _
      rw [hent2 i k, Matrix.add_apply, Matrix.smul_apply]
      show _ = _ + condExp G P (fun ω' => (e ω' • ((Muon.outer (X ω').2 (X ω').2).map
          (fun x : ℝ => (x : ℂ)) - 1)) i k) ζ
      rw [hent i k]
      have h2' : condExp G P (fun ω => ((1 : Mat n n) i k : ℂ) * e ω) ζ =
          ((1 : Mat n n) i k : ℂ) * condExp G P e ζ := h2ζ
      have h1ζ' := h1ζ
      simp only [Pi.add_apply] at h1ζ'
      rw [h1ζ', h2', hone]
      simp only [smul_eq_mul]
      ring
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun k => hall i k] with ζ hζ
    ext i k
    exact hζ i k
  · have hb := lem_app_de_bessel_iii (𝕜 := ℂ) (mΩ := mΩ) P X hX G hG hind e he he2
    filter_upwards [hb] with ζ hζ
    unfold fro
    have e1 : ∀ i k : Fin n, condExpMatC G P (fun ω => e ω • ((Muon.outer (X ω).2 (X ω).2).map
        (fun x : ℝ => (x : ℂ)) - 1)) ζ i k = condExp G P
        (fun ω' => ((((X ω').2 i * (X ω').2 k - (1 : Mat n n) i k : ℝ)) : ℂ) * e ω') ζ := by
      intro i k
      show condExp G P (fun ω' => (e ω' • ((Muon.outer (X ω').2 (X ω').2).map
          (fun x : ℝ => (x : ℂ)) - 1)) i k) ζ = _
      rw [hent i k]
    simp only [e1]
    exact hζ

end SD6Q

open scoped Matrix.Norms.L2Operator in
private lemma sd6_opNorm_cast {a b : ℕ} (A : Mat a b) :
    opNorm (A.map (fun x : ℝ => (x : ℂ))) ≤ opNorm A := by
  refine sd0_opNorm_le _ (sd2_opNorm_nonneg_real A) fun x => ?_
  set xr : Fin b → ℝ := fun i => (x i).re with hxr
  set xi : Fin b → ℝ := fun i => (x i).im with hxi
  have hr : ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (A *ᵥ xr)‖ ≤
      opNorm A * ‖(EuclideanSpace.equiv (Fin b) ℝ).symm xr‖ := by
    rw [opNorm_eq_norm]
    exact Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin b) ℝ).symm xr)
  have hi : ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (A *ᵥ xi)‖ ≤
      opNorm A * ‖(EuclideanSpace.equiv (Fin b) ℝ).symm xi‖ := by
    rw [opNorm_eq_norm]
    exact Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin b) ℝ).symm xi)
  have hy : ∀ i, ‖((A.map (fun x : ℝ => (x : ℂ))) *ᵥ x) i‖ ^ 2 =
      (A *ᵥ xr) i ^ 2 + (A *ᵥ xi) i ^ 2 := by
    intro i
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum, hxr, hxi]
    ring
  have hn1 : ‖(EuclideanSpace.equiv (Fin a) ℂ).symm ((A.map (fun x : ℝ => (x : ℂ))) *ᵥ x)‖ ^ 2 =
      ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (A *ᵥ xr)‖ ^ 2 +
        ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (A *ᵥ xi)‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs]
    exact hy i
  have hn2 : ‖(EuclideanSpace.equiv (Fin b) ℂ).symm x‖ ^ 2 =
      ‖(EuclideanSpace.equiv (Fin b) ℝ).symm xr‖ ^ 2 +
        ‖(EuclideanSpace.equiv (Fin b) ℝ).symm xi‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Real.norm_eq_abs, sq_abs]
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [hxr, hxi]
    ring
  have h0 := sd2_opNorm_nonneg_real A
  have hsq : ‖(EuclideanSpace.equiv (Fin a) ℂ).symm ((A.map (fun x : ℝ => (x : ℂ))) *ᵥ x)‖ ^ 2 ≤
      (opNorm A * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm x‖) ^ 2 := by
    rw [hn1, mul_pow, hn2]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) hr 2
    have h2 := pow_le_pow_left₀ (norm_nonneg _) hi 2
    rw [mul_pow] at h1 h2
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg h0 (norm_nonneg _))
    two_ne_zero).mp hsq

section SD6Q2
variable {Ω' : Type*} [mΩ : MeasurableSpace Ω']

private lemma sd6_int_ww {m n : ℕ} (P : Measure Ω') [IsProbabilityMeasure P]
    (X : Ω' → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (e : Ω' → ℂ) (he2 : MemLp e 2 P) (a b : Fin n) :
    Integrable (fun ω => (e ω • (Muon.outer (X ω).2 (X ω).2).map
      (fun x : ℝ => (x : ℂ))) a b) P := by
  have hei : Integrable e P := he2.integrable one_le_two
  have h := sd2_int_cplx_mul (mΩ := mΩ) P e (fun ω => (X ω).2 a * (X ω).2 b - (1 : Mat n n) a b)
    (by
      have := sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_snd (mΩ := mΩ) P X hX a b) he2.re
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [RCLike.re_to_complex, RCLike.im_to_complex]; ring)
    (by
      have := sd2b_integrable_mul (mΩ := mΩ) (sd2b_memLp_sq_snd (mΩ := mΩ) P X hX a b) he2.im
      refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [RCLike.re_to_complex, RCLike.im_to_complex]; ring)
  have h2 := h.add (hei.const_mul (((1 : Mat n n) a b : ℝ) : ℂ))
  refine h2.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Muon.outer,
    Matrix.vecMulVec_apply]
  push_cast
  ring

private lemma sd6_map_mul {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    (A * B).map (fun x : ℝ => (x : ℂ)) =
      A.map (fun x : ℝ => (x : ℂ)) * B.map (fun x : ℝ => (x : ℂ)) :=
  Matrix.map_mul (f := Complex.ofRealHom)

open scoped Matrix.Norms.L2Operator MatrixOrder in
private lemma sd6_opNorm_rInC {m n : ℕ} (C : Covariances m n) :
    opNorm ((rIn C).map (fun x : ℝ => (x : ℂ))) * opNorm ((rIn C).map (fun x : ℝ => (x : ℂ))) ≤
      opNorm C.Sin := by
  have hh : ((rIn C).map (fun x : ℝ => (x : ℂ)))ᴴ = (rIn C).map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    have := congrFun (congrFun (sd6_rIn_symm C) i) j
    simp only [Matrix.transpose_apply] at this
    simp [Matrix.conjTranspose_apply, this]
  have hsq : (rIn C).map (fun x : ℝ => (x : ℂ)) * (rIn C).map (fun x : ℝ => (x : ℂ)) =
      C.Sin.map (fun x : ℝ => (x : ℂ)) := by
    rw [← sd6_map_mul, sd6_rIn_sq]
  have := Matrix.l2_opNorm_conjTranspose_mul_self ((rIn C).map (fun x : ℝ => (x : ℂ)))
  rw [hh, hsq] at this
  have h2 : opNorm (C.Sin.map (fun x : ℝ => (x : ℂ))) =
      opNorm ((rIn C).map (fun x : ℝ => (x : ℂ))) * opNorm ((rIn C).map (fun x : ℝ => (x : ℂ))) := by
    rw [opNorm_eq_norm, opNorm_eq_norm]
    exact this
  rw [← h2]
  exact sd6_opNorm_cast _

private lemma sd6_hV {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (x : Vec m × Vec n) :
    (B : ℂ) • vecMulVec (fun i => (momV C B x i : ℂ)) (fun i => (momV C B x i : ℂ)) =
      (rIn C).map (fun y : ℝ => (y : ℂ)) * (Muon.outer x.2 x.2).map (fun y : ℝ => (y : ℂ)) *
        (rIn C).map (fun y : ℝ => (y : ℂ)) := by
  have h := congrArg (fun A : Mat n n => A.map (fun y : ℝ => (y : ℂ))) (sd6_B_outer_vv C B hB x)
  rw [sd6_map_mul, sd6_map_mul] at h
  rw [← h]
  ext i k
  simp [Muon.outer, Matrix.vecMulVec_apply]

end SD6Q2

/-- Gram term per age at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 873–881): "The Gram term is split as in the proof of `thm:app-drift-mixed`(ii), with
`𝔼_𝒢[(w_j⊗w_j)α_{2,j}] = φ_j Id + Γ_j`":
`B 𝔼[α_{2,j} 𝖷_0^{(j)}(𝗏_j⊗𝗏_j)] = (b_j 𝓗_j(z) + 𝒞_j) Σ_in + Err`, `‖Err‖_F ≤ K w_j²/x`, for
`Re z ≥ s₀`. Real counterpart `Muon.Drift.tl_Q` (`Tail.lean`:1571, there `s ≥ 1`). -/
theorem tl_Q_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        (∀ i k, Integrable (fun ω => (delAlphaC2 w F S t j z ω •
            (XzC (delBufAge w F S t j ω) z *
              vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) i k) P) ∧
        ∃ Err : Matrix (Fin m) (Fin n) ℂ, fro Err ≤ K * w j ^ 2 / z.re ∧
          (B : ℂ) • meanC P (fun ω => delAlphaC2 w F S t j z ω •
            (XzC (delBufAge w F S t j ω) z *
              vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) =
          (bjC w F S t j z • HjC w F S t j z + CjC w F S t j z) * SinC F + Err := by
  obtain ⟨Cc, hCc0, hCc⟩ := sd6_facts s0 hs0 CS γ hγ
  refine ⟨CS * Cc * (Real.sqrt 2 / (2 * Real.sqrt s0)), ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hBc : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hCo
  obtain ⟨-, e2m, -, L2, -, k2⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := sd6_indep F S t j
  have hM0 := sd4_del_measurable w F S t j
  set e2 := delAlphaC2 w F S t j z with he2def
  set rC : Matrix (Fin n) (Fin n) ℂ := (rIn F.C).map (fun x : ℝ => (x : ℂ)) with hrCdef
  set r := opNorm rC with hrdef
  have hr0 : 0 ≤ r := sd2_opNorm_nonneg _
  have hrr : r * r ≤ CS := (sd6_opNorm_rInC F.C).trans hCi
  have hsq0 : 0 < Real.sqrt z.re := Real.sqrt_pos.2 hspos
  have hs2 : 0 < 1 / (2 * Real.sqrt z.re) := by positivity
  have hXm : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => XzC (delBufAge w F S t j ω) z i k) :=
    fun i k => ((sd0_cont_X (m := m) (n := n) z hspos).matrix_elem i k).measurable.comp hM0
  have hLm : ∀ i k, Measurable[sigmaOthers F S t j]
      (fun ω => (XzC (delBufAge w F S t j ω) z * rC) i k) :=
    fun i k => (((sd0_cont_X (m := m) (n := n) z hspos).matrix_mul
      (continuous_const (y := rC))).matrix_elem i k).measurable.comp hM0
  have hRm : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω : Ω => rC i k) :=
    fun i k => measurable_const
  have hXb : ∀ ω, opNorm (XzC (delBufAge w F S t j ω) z) ≤ 1 / (2 * Real.sqrt z.re) :=
    fun ω => sd0_X_bound _ z hspos
  have hLb' : ∀ ω, opNorm (XzC (delBufAge w F S t j ω) z * rC) ≤
      1 / (2 * Real.sqrt z.re) * r :=
    fun ω => (sd0_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right (hXb ω) hr0)
  have hLb : ∀ ω i k, ‖(XzC (delBufAge w F S t j ω) z * rC) i k‖ ≤
      1 / (2 * Real.sqrt z.re) * r :=
    fun ω i k => (sd0_entry_le _ i k).trans (hLb' ω)
  have hRb : ∀ (ω : Ω) i k, ‖rC i k‖ ≤ r := fun ω i k => sd0_entry_le _ i k
  have hXbd : ∀ ω i k, ‖XzC (delBufAge w F S t j ω) z i k‖ ≤ 1 / (2 * Real.sqrt z.re) :=
    fun ω i k => (sd0_entry_le _ i k).trans (hXb ω)
  have hW := sd6_int_ww (n := n) (m := m) P X hlaw e2 L2
  have hint := sd2_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => XzC (delBufAge w F S t j ω) z * rC) (fun _ => rC)
    (1 / (2 * Real.sqrt z.re) * r) r (by positivity) hLm hRm hLb hRb _ hW
  have hpt : ∀ ω, (B : ℂ) • (e2 ω • (XzC (delBufAge w F S t j ω) z *
      vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) =
      (XzC (delBufAge w F S t j ω) z * rC) *
        (e2 ω • (Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ))) * rC := by
    intro ω
    have h := sd6_hV F.C hB (X ω)
    have h2 : (B : ℂ) • (e2 ω • (XzC (delBufAge w F S t j ω) z *
        vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) =
        e2 ω • (XzC (delBufAge w F S t j ω) z *
          ((B : ℂ) • vecMulVec (fun i => (momV F.C B (X ω) i : ℂ))
            (fun i => (momV F.C B (X ω) i : ℂ)))) := by
      rw [Matrix.mul_smul, smul_comm]; rfl
    rw [h2, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rfl
  have hsum_int : ∀ i k, Integrable (fun ω => (e2 ω • (XzC (delBufAge w F S t j ω) z *
      vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) i k) P := by
    intro i k
    refine ((hint i k).const_mul ((B : ℂ)⁻¹)).congr (Filter.Eventually.of_forall fun ω => ?_)
    have := congrFun (congrFun (hpt ω) i) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    field_simp
  refine ⟨hsum_int, ?_⟩
  have hmean : (B : ℂ) • meanC P (fun ω => e2 ω • (XzC (delBufAge w F S t j ω) z *
      vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) =
      meanC P (fun ω => (XzC (delBufAge w F S t j ω) z * rC) *
        (e2 ω • (Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ))) * rC) := by
    rw [← sd6_meanC_smul]
    exact congrArg _ (funext hpt)
  rw [hmean, sd2m_tower (mΩ := inst) P (sigmaOthers F S t j) hG]
  obtain ⟨hK, hΓb⟩ := sd6_gram_cond P X hlaw (sigmaOthers F S t j) hG hindc e2 e2m L2
  set Γ : Ω → Matrix (Fin n) (Fin n) ℂ := condExpMatC (sigmaOthers F S t j) P
    (fun ω => e2 ω • ((Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ)) - 1)) with hΓdef
  have hΓint : ∀ i k, Integrable (fun ζ => Γ ζ i k) P := fun i k => integrable_condExp
  have hφ : Integrable (condExp (sigmaOthers F S t j) P e2) P := integrable_condExp
  have hpull := sd2_condExpMat_pull (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => XzC (delBufAge w F S t j ω) z * rC) (fun _ => rC)
    (1 / (2 * Real.sqrt z.re) * r) r (by positivity) hr0 hLm hRm hLb hRb
    (fun ω => e2 ω • (Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ))) hW
  have hRsq : rC * rC = SinC F := by
    rw [hrCdef, ← sd6_map_mul, sd6_rIn_sq]
  have halg : ∀ (X0 : Matrix (Fin m) (Fin n) ℂ) (φ : ℂ) (Γ' : Matrix (Fin n) (Fin n) ℂ),
      (X0 * rC) * (φ • (1 : Matrix (Fin n) (Fin n) ℂ) + Γ') * rC =
        (φ • X0) * SinC F + (X0 * rC) * Γ' * rC := by
    intro X0 φ Γ'
    rw [← hRsq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  have hae : ∀ᵐ ζ ∂P, condExpMatC (sigmaOthers F S t j) P
      (fun ω => (XzC (delBufAge w F S t j ω) z * rC) *
        (e2 ω • (Muon.outer (X ω).2 (X ω).2).map (fun x : ℝ => (x : ℂ))) * rC) ζ =
      (condExp (sigmaOthers F S t j) P e2 ζ • XzC (delBufAge w F S t j ζ) z) * SinC F +
        (XzC (delBufAge w F S t j ζ) z * rC) * Γ ζ * rC := by
    filter_upwards [hpull, hK] with ζ h1 h2
    rw [h1, h2]
    exact halg _ _ _
  rw [sd6_meanC_congr P _ _ hae]
  have hX0int : ∀ i k, Integrable (fun ζ => XzC (delBufAge w F S t j ζ) z i k) P := fun i k =>
    Integrable.of_bound (((hXm i k).mono hG le_rfl).aestronglyMeasurable) (1 / (2 * Real.sqrt z.re))
      (Filter.Eventually.of_forall fun ζ => hXbd ζ i k)
  have hφX : ∀ i k, Integrable (fun ζ => (condExp (sigmaOthers F S t j) P e2 ζ •
      XzC (delBufAge w F S t j ζ) z) i k) P := by
    intro i k
    have := Integrable.mul_bdd (c := 1 / (2 * Real.sqrt z.re)) hφ
      (((hXm i k).mono hG le_rfl).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => hXbd ζ i k)
    exact this
  have hφXS : ∀ i k, Integrable (fun ζ => ((condExp (sigmaOthers F S t j) P e2 ζ •
      XzC (delBufAge w F S t j ζ) z) * SinC F) i k) P := by
    intro i k
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ => (hφX i l).mul_const _
  have hLΓR := sd2_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => XzC (delBufAge w F S t j ω) z * rC) (fun _ => rC)
    (1 / (2 * Real.sqrt z.re) * r) r (by positivity) hLm hRm hLb hRb Γ hΓint
  rw [sd6_meanC_add P _ _ hφXS hLΓR, sd6_meanC_mul_right P _ (SinC F) hφX]
  refine ⟨meanC P (fun ζ => (XzC (delBufAge w F S t j ζ) z * rC) * Γ ζ * rC), ?_, ?_⟩
  · have hbd := sd2m_fro_mean_le (mΩ := inst) P
      (fun ζ => (XzC (delBufAge w F S t j ζ) z * rC) * Γ ζ * rC)
      hLΓR (1 / (2 * Real.sqrt z.re) * r * (Real.sqrt 2 * (Cc * w j ^ 2 / z.re)) * r) (by
        filter_upwards [hΓb, k2] with ζ h1 h2
        refine (sd2_fro_sandwich _ _ _).trans ?_
        have h3 : fro (Γ ζ) ≤ Real.sqrt 2 * (Cc * w j ^ 2 / z.re) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
        exact mul_le_mul (mul_le_mul (hLb' ζ) h3 (sd2_fro_nonneg _) (by positivity)) le_rfl hr0
          (by positivity))
    refine hbd.trans ?_
    have hsq1 : Real.sqrt s0 ≤ Real.sqrt z.re := Real.sqrt_le_sqrt hs
    have hq : 1 / (2 * Real.sqrt z.re) * Real.sqrt 2 ≤ Real.sqrt 2 / (2 * Real.sqrt s0) := by
      rw [show 1 / (2 * Real.sqrt z.re) * Real.sqrt 2 = Real.sqrt 2 / (2 * Real.sqrt z.re) by ring]
      exact div_le_div_of_nonneg_left (Real.sqrt_nonneg 2) (by positivity) (by linarith)
    have hcc : 0 ≤ Cc * w j ^ 2 / z.re := by positivity
    calc 1 / (2 * Real.sqrt z.re) * r * (Real.sqrt 2 * (Cc * w j ^ 2 / z.re)) * r
        = (r * r) * ((1 / (2 * Real.sqrt z.re) * Real.sqrt 2) * (Cc * w j ^ 2 / z.re)) := by ring
      _ ≤ CS * ((Real.sqrt 2 / (2 * Real.sqrt s0)) * (Cc * w j ^ 2 / z.re)) :=
          mul_le_mul hrr (mul_le_mul_of_nonneg_right hq hcc) (by positivity) hCS
      _ = _ := by ring
  · have hC : CjC w F S t j z = meanC P (fun ω =>
        (condExp (sigmaOthers F S t j) P e2 ω - bjC w F S t j z) •
          XzC (delBufAge w F S t j ω) z) := rfl
    have hH : HjC w F S t j z = meanC P (fun ω => XzC (delBufAge w F S t j ω) z) := rfl
    have hsub : meanC P (fun ω =>
        (condExp (sigmaOthers F S t j) P e2 ω - bjC w F S t j z) •
          XzC (delBufAge w F S t j ω) z) =
        meanC P (fun ω => condExp (sigmaOthers F S t j) P e2 ω • XzC (delBufAge w F S t j ω) z) -
          bjC w F S t j z • meanC P (fun ω => XzC (delBufAge w F S t j ω) z) := by
      rw [← sd6_meanC_smul]
      rw [← sd6_meanC_sub P _ _ hφX (fun i k => by
        simp only [Matrix.smul_apply, smul_eq_mul]; exact (hX0int i k).const_mul _)]
      exact congrArg _ (funext fun ω => sub_smul _ _ _)
    rw [hC, hH, hsub]
    congr 2
    abel

/-- `b_j` at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 883–889):
`Re b_j ≥ 0` (from `eqn:app-dyn-Rebeta`) and `|b_j| ≤ K w_j²/x` for `Re z ≥ s₀`. Real counterpart
`Muon.Drift.tl_b` (`Tail.lean`:1786, there `s ≥ 1` and `0 ≤ b_j`). -/
theorem tl_b_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        0 ≤ (bjC w F S t j z).re ∧ ‖bjC w F S t j z‖ ≤ K * w j ^ 2 / z.re := by
  obtain ⟨C, hC⟩ := sd4_phi_bound s0 hs0 CS γ hγ
  obtain ⟨C1, hC1⟩ := lem_app_drift_coeffmoments_sector 1 le_rfl s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hint := sd4_alpha2_integrable w F S t j z CS γ hz hzS hγ hCo hCi hm hn hw0 hw1
  have hb : bjC w F S t j z = ∫ ω, delAlphaC2 w F S t j z ω ∂P := by
    unfold bjC phiJC
    exact integral_condExp hG
  refine ⟨?_, ?_⟩
  · rw [hb]
    refine le_of_le_of_eq (integral_nonneg fun ω => ?_) (integral_re hint)
    exact (hC1 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1
      (sd4_del_measurable w F S t j) z hs hzS).1 ω
  · have hphi : Integrable (phiJC w F S t j z) P := integrable_condExp
    calc ‖bjC w F S t j z‖ = ‖∫ ω, phiJC w F S t j z ω ∂P‖ := rfl
      _ ≤ ∫ ω, ‖phiJC w F S t j z ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ _ω, C * w j ^ 2 / z.re ∂P :=
          integral_mono_ae hphi.norm (integrable_const _)
            (hC Ω m n B P F S t j w hCo hCi hm hn hw0 hw1 z hs hzS)
      _ = _ := by rw [integral_const, probReal_univ, one_smul]

/-! ### Helpers for `tl_perj_sector`, `sector_response` (task P-E.15.P3) -/

section SD7

private lemma sd7_fro_neg {k l : ℕ} (A : Matrix (Fin k) (Fin l) ℂ) : fro (-A) = fro A := by
  have h := sd6_fro_smul (-1 : ℂ) A
  rw [neg_one_smul] at h
  rw [h]; simp

private lemma sd7_fro_zero {k l : ℕ} : fro (0 : Matrix (Fin k) (Fin l) ℂ) = 0 := by
  unfold fro; simp

private lemma sd7_fro_finsum {k l : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → Matrix (Fin k) (Fin l) ℂ) : fro (∑ i ∈ s, f i) ≤ ∑ i ∈ s, fro (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sd7_fro_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (sd2_fro_add _ _).trans (add_le_add_right ih _)

private lemma sd7_fro_cont {k l : ℕ} : Continuous (fun a : Matrix (Fin k) (Fin l) ℂ => fro a) := by
  unfold fro
  fun_prop

private lemma sd7_fro_hasSum {k l : ℕ} (f : ℕ → Matrix (Fin k) (Fin l) ℂ)
    (a : Matrix (Fin k) (Fin l) ℂ) (c : ℕ → ℝ)
    (hf : HasSum f a) (hc : Summable c) (hfc : ∀ j, fro (f j) ≤ c j)
    (hc0 : ∀ j, 0 ≤ c j) : fro a ≤ ∑' j, c j := by
  have ht := (sd7_fro_cont (k := k) (l := l)).continuousAt.tendsto.comp hf
  refine le_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp]
  refine (sd7_fro_finsum s f).trans ?_
  exact (Finset.sum_le_sum fun j _ => hfc j).trans (hc.sum_le_tsum s (fun j _ => hc0 j))

end SD7

/-- Per-age response bound at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 875–881, the two displays combined per age with `eqn:app-drift-deletion-mean` and
`lem:app-drift-covariance`): `‖B 𝔼[α_{1,j}R_0^{(j)}(𝗎_j⊗𝗏_j) − α_{2,j}𝖷_0^{(j)}(𝗏_j⊗𝗏_j)] +
b_j 𝓗(z)Σ_in‖_F ≤ K w_j/x` with `Re b_j ≥ 0`, `|b_j| ≤ K w_j/x`, for `Re z ≥ s₀`. Real counterpart
`Muon.Drift.tl_perj` (`Tail.lean`:1816, there `s ≥ 1`). -/
theorem tl_perj_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (w : ℕ → ℝ) (j : ℕ), WeightClass w →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        0 ≤ (bjC w F S t j z).re ∧ ‖bjC w F S t j z‖ ≤ K * w j / z.re ∧
        fro ((B : ℂ) • meanC P (fun ω =>
            delAlphaC1 w F S t j z ω • (Rres (delBufAge w F S t j ω) (-z) *
              vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))
          - delAlphaC2 w F S t j z ω • (XzC (delBufAge w F S t j ω) z *
              vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) +
          bjC w F S t j z • (HmixC w F S t z * SinC F)) ≤ K * w j / z.re := by
  obtain ⟨KS, hKS⟩ := tl_S_sector s0 hs0 CS γ hγ
  obtain ⟨KQ, hKQ⟩ := tl_Q_sector s0 hs0 CS γ hγ
  obtain ⟨Kb, hKb⟩ := tl_b_sector s0 hs0 CS γ hγ
  obtain ⟨Kc, hKc⟩ := lem_app_drift_covariance_sector s0 hs0 CS γ hγ
  obtain ⟨Km, hKm⟩ := lem_app_drift_multiplier_ii_sector s0 hs0 CS γ hγ
  have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  refine ⟨|KS| + |Kb| + |Kb| * |Km| * |CS| / s0 + |Kc| * |CS| / Real.sqrt s0 + |KQ|,
    by positivity, ?_⟩
  intro Ω inst m n B P _ F S t w j hw hCo hCi hm hn z hs hzS
  have hspos : 0 < z.re := lt_of_lt_of_le hs0 hs
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hCS : 0 ≤ CS := (sd2_opNorm_nonneg_real _).trans hCo
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  have hsB : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hBr
  have hss : Real.sqrt s0 ≤ Real.sqrt z.re := Real.sqrt_le_sqrt hs
  obtain ⟨hSint, hSb⟩ := hKS Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  obtain ⟨hQint, Err, hErr, hQeq⟩ := hKQ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  obtain ⟨hb0, hb1⟩ := hKb Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn z hs hzS
  obtain ⟨-, hCjb, -, -⟩ := hKc Ω m n B P F S t w ⟨hw.1.1, hw.1.2.1, hw.2.1, hw.2.2⟩ hCo hCi
    hm hn z hs hzS
  have hHm := hKm Ω m n B P F S t j w hw hCo hCi hm hn z hs hzS
  have hCj := hCjb j
  have hsplit : (B : ℂ) • meanC P (fun ω =>
        delAlphaC1 w F S t j z ω • (Rres (delBufAge w F S t j ω) (-z) *
          vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))
      - delAlphaC2 w F S t j z ω • (XzC (delBufAge w F S t j ω) z *
          vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) =
      (B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
          (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) -
      (B : ℂ) • meanC P (fun ω => delAlphaC2 w F S t j z ω •
          (XzC (delBufAge w F S t j ω) z *
            vecMulVec (fun i => (ageV F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) := by
    rw [sd6_meanC_sub P _ _ hSint hQint, smul_sub]
  have hw2 : w j ^ 2 ≤ w j := by rw [sq]; exact mul_le_of_le_one_right hw0 hw1
  have hu0 : 0 ≤ w j / z.re := by positivity
  have hx1 : w j ^ 2 / z.re ≤ w j / z.re := div_le_div_of_nonneg_right hw2 hspos.le
  have hKb' : Kb * w j ^ 2 / z.re ≤ |Kb| * (w j / z.re) := by
    calc Kb * w j ^ 2 / z.re = Kb * (w j ^ 2 / z.re) := by rw [mul_div_assoc]
      _ ≤ |Kb| * (w j ^ 2 / z.re) := mul_le_mul_of_nonneg_right (le_abs_self Kb) (by positivity)
      _ ≤ |Kb| * (w j / z.re) := mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
  have hbn : ‖bjC w F S t j z‖ ≤ |Kb| * (w j / z.re) := hb1.trans hKb'
  refine ⟨hb0, ?_, ?_⟩
  · refine hbn.trans ?_
    rw [← mul_div_assoc]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hw0) hspos.le
    have : 0 ≤ |KS| := abs_nonneg _
    have : 0 ≤ |Kb| * |Km| * |CS| / s0 := by positivity
    have : 0 ≤ |Kc| * |CS| / Real.sqrt s0 := by positivity
    have : 0 ≤ |KQ| := abs_nonneg _
    linarith
  rw [hsplit, hQeq]
  set b := bjC w F S t j z with hbdef
  have hid : (B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
          (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) -
        ((b • HjC w F S t j z + CjC w F S t j z) * SinC F + Err) +
        b • (HmixC w F S t z * SinC F) =
      (B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
          (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) +
      (-(b • ((HjC w F S t j z - HmixC w F S t z) * SinC F))) +
        (-(CjC w F S t j z * SinC F)) + (-Err) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, smul_sub]
    abel
  rw [hid]
  have hSinC : opNorm (SinC F) ≤ |CS| :=
    (sd6_opNorm_cast F.C.Sin).trans (hCi.trans (le_abs_self CS))
  have p1 : fro ((B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
          (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ))))) ≤
        |KS| * (w j / z.re) := by
    refine hSb.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self KS) hu0
  have hHn : fro (HjC w F S t j z - HmixC w F S t z) ≤ |Km| * (w j / z.re) := by
    have e : HjC w F S t j z - HmixC w F S t z =
        (-1 : ℂ) • (HmixC w F S t z - HjC w F S t j z) := by
      rw [neg_one_smul, neg_sub]
    rw [e, sd6_fro_smul]
    simp only [norm_neg, norm_one, one_mul]
    refine hHm.trans ?_
    calc Km * w j / (z.re * Real.sqrt (B : ℝ)) ≤ |Km| * w j / (z.re * Real.sqrt (B : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Km) hw0)
            (by positivity)
      _ ≤ |Km| * w j / z.re := by
          apply div_le_div_of_nonneg_left (by positivity) hspos
          exact le_mul_of_one_le_right hspos.le hsB
      _ = _ := by ring
  have hux : w j / z.re ≤ 1 / s0 := by
    calc w j / z.re ≤ 1 / z.re := div_le_div_of_nonneg_right hw1 hspos.le
      _ ≤ 1 / s0 := one_div_le_one_div_of_le hs0 hs
  have p2 : fro (-(b • ((HjC w F S t j z - HmixC w F S t z) * SinC F))) ≤
      |Kb| * |Km| * |CS| / s0 * (w j / z.re) := by
    rw [sd7_fro_neg, sd6_fro_smul]
    have h1 : fro ((HjC w F S t j z - HmixC w F S t z) * SinC F) ≤
        |Km| * (w j / z.re) * |CS| :=
      (sd2_fro_mul_le_right _ _).trans (mul_le_mul hHn hSinC (sd2_opNorm_nonneg _)
        (by positivity))
    calc ‖b‖ * fro ((HjC w F S t j z - HmixC w F S t z) * SinC F)
        ≤ (|Kb| * (w j / z.re)) * (|Km| * (w j / z.re) * |CS|) :=
          mul_le_mul hbn h1 (sd2_fro_nonneg _) (by positivity)
      _ = (|Kb| * |Km| * |CS|) * ((w j / z.re) * (w j / z.re)) := by ring
      _ ≤ (|Kb| * |Km| * |CS|) * ((1 / s0) * (w j / z.re)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hux hu0
      _ = _ := by ring
  have p3 : fro (-(CjC w F S t j z * SinC F)) ≤ |Kc| * |CS| / Real.sqrt s0 * (w j / z.re) := by
    rw [sd7_fro_neg]
    refine (sd2_fro_mul_le_right _ _).trans ?_
    have hc : fro (CjC w F S t j z) ≤ |Kc| / Real.sqrt s0 * (w j / z.re) := by
      refine hCj.trans ?_
      have hdenom : z.re * Real.sqrt s0 ≤ z.re * Real.sqrt z.re * Real.sqrt (B : ℝ) := by
        calc z.re * Real.sqrt s0 ≤ z.re * Real.sqrt z.re :=
              mul_le_mul_of_nonneg_left hss hspos.le
          _ = z.re * Real.sqrt z.re * 1 := (mul_one _).symm
          _ ≤ z.re * Real.sqrt z.re * Real.sqrt (B : ℝ) :=
              mul_le_mul_of_nonneg_left hsB (by positivity)
      calc Kc * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ))
          ≤ |Kc| * w j ^ 2 / (z.re * Real.sqrt z.re * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Kc)
              (sq_nonneg _)) (by positivity)
        _ ≤ |Kc| * w j ^ 2 / (z.re * Real.sqrt s0) :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) hdenom
        _ ≤ |Kc| * w j / (z.re * Real.sqrt s0) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)
        _ = _ := by field_simp
    calc fro (CjC w F S t j z) * opNorm (SinC F)
        ≤ (|Kc| / Real.sqrt s0 * (w j / z.re)) * |CS| :=
          mul_le_mul hc hSinC (sd2_opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  have p4 : fro (-Err) ≤ |KQ| * (w j / z.re) := by
    rw [sd7_fro_neg]
    refine hErr.trans ?_
    calc KQ * w j ^ 2 / z.re ≤ |KQ| * w j ^ 2 / z.re :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self KQ) (sq_nonneg _))
            hspos.le
      _ ≤ |KQ| * w j / z.re := by
          apply div_le_div_of_nonneg_right _ hspos.le
          exact mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)
      _ = _ := by ring
  set Sj := (B : ℂ) • meanC P (fun ω => delAlphaC1 w F S t j z ω •
          (Rres (delBufAge w F S t j ω) (-z) *
            vecMulVec (fun i => (ageU F S t j ω i : ℂ)) (fun i => (ageV F S t j ω i : ℂ)))) with hSj
  set A := -(b • ((HjC w F S t j z - HmixC w F S t z) * SinC F)) with hA
  set C' := -(CjC w F S t j z * SinC F) with hC'
  have a1 := sd2_fro_add (Sj + A + C') (-Err)
  have a2 := sd2_fro_add (Sj + A) C'
  have a3 := sd2_fro_add Sj A
  have hfin : (|KS| + |Kb| + |Kb| * |Km| * |CS| / s0 + |Kc| * |CS| / Real.sqrt s0 + |KQ|) *
      w j / z.re = (|KS| + |Kb| + |Kb| * |Km| * |CS| / s0 + |Kc| * |CS| / Real.sqrt s0 + |KQ|) *
      (w j / z.re) := by ring
  rw [hfin]
  have hKb0 : 0 ≤ |Kb| * (w j / z.re) := by positivity
  linarith [p1, p2, p3, p4]

/-- The response identity at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 885–889):
```latex
\mathcal H(z)\,\mathsf Y_B(z)=E_0(z),\qquad\mathsf Y_B(z)\defeq\Id_{\Nin}+b_B(z)\Sigmain,\qquad
\norm{E_0(z)}_\F\le\frac Cx\quad(x\ge1).
```
with "on a compact `I` the same steps give" the bound `C_I`, and `Re b_B ≥ 0` (l. 889). Encoding:
`𝓗(z)𝖸_B(z) = 𝓗 + b_B (𝓗Σ_in)`; one `C` per `s₀` serves all `z ∈ 𝕊` with `Re z ≥ s₀` (this gives
both regimes); the series `b_B = ∑_j b_j` is summable. No sign condition on `C_Σ`, `γ⋆` is needed
(degenerate values make the hypotheses vacuous or the matrices zero). -/
theorem sector_response (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
      (S : FrozenSamples P m n B) (t : ℤ),
      WeightClass w → DriftBound F CS γ →
      ∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 →
        Summable (fun j => bjC w F S t j z) ∧ 0 ≤ (bBC w F S t z).re ∧
        fro (HmixC w F S t z + bBC w F S t z • (HmixC w F S t z * SinC F)) ≤ C / z.re := by
  obtain ⟨K, hK0, hK⟩ := tl_perj_sector s0 hs0 CS (max γ 0) (le_max_right _ _)
  refine ⟨K, ?_⟩
  intro Ω inst m n B P _ w F S t hw hDB z hs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hs
  obtain ⟨hCo, hCi, hmax⟩ := hDB
  have hm : (m : ℝ) ≤ max γ 0 * B :=
    ((Nat.cast_le.2 (le_max_left m n)).trans hmax).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg B))
  have hn : (n : ℝ) ≤ max γ 0 * B :=
    ((Nat.cast_le.2 (le_max_right m n)).trans hmax).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg B))
  have hexact := lem_app_drift_exact_sector hw F S t z hz hzS
  have hsumw : Summable (fun j => K * w j / z.re) := (hw.1.2.1.mul_left K).div_const z.re
  have hper := fun j => hK Ω m n B P F S t w j hw hCo hCi hm hn z hs hzS
  have hbS : Summable (fun j => bjC w F S t j z) :=
    Summable.of_norm_bounded hsumw (fun j => (hper j).2.1)
  have hb : HasSum (fun j => bjC w F S t j z) (bBC w F S t z) := hbS.hasSum
  have hZ := hexact.add (hb.smul_const (HmixC w F S t z * SinC F))
  have hbB0 : 0 ≤ (bBC w F S t z).re := by
    have h := hb.mapL Complex.reCLM
    exact h.nonneg fun j => (hper j).1
  refine ⟨hbS, hbB0, ?_⟩
  have hfro := sd7_fro_hasSum _ _ (fun j => K * w j / z.re) hZ hsumw (fun j => (hper j).2.2)
    (fun j => by have := hw.1.1 j; positivity)
  refine hfro.trans ?_
  rw [tsum_div_const, tsum_mul_left]
  have : K * ∑' j, w j ≤ K * 1 := mul_le_mul_of_nonneg_left hw.2.2 hK0
  rw [mul_one] at this
  exact div_le_div_of_nonneg_right this hz.le

/-- `thm:app-drift-mixed`(ii) on the sector, snapshot `cr-2026-10-23`: the bound of
`lem:app-dyn-mean`(i) in its unified form. Source (`sections/05-dynamics/section.tex` ll. 889–893
with ll. 800–803):
```latex
and $\abs{1+b_B\lambda_j}\ge\Ree(1+b_B\lambda_j)\ge1$, so
$\norm{\mathsf Y_B^{-1}}\le1$ and $\norm{\mathcal H(z)}_\F\le\norm{E_0(z)}_\F\le C/x$.
On a compact $I$ the same steps give $\norm{\mathcal H(z)}_\F\le C_I$.
```
For every `s₀ > 0` there is `C`, depending only on `(s₀, C_Σ, γ⋆)` and chosen before the dimension,
the weights, the state and the samples, with `‖𝓗(z)‖_F ≤ C/Re z` for every `z ∈ 𝕊` with
`Re z ≥ s₀`; and `𝖷_z(M_t)` is entrywise integrable for every `Re z > 0`. Real counterpart: the
`𝓗`-clause of `Muon.Drift.thm_app_drift_mixed_ii` (`Tail.lean`:2035), which is the case `s₀ = 1`,
`z = s` (via `hmixC_ofReal`). -/
theorem thm_app_drift_mixed_ii_sector (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
      (S : FrozenSamples P m n B) (t : ℤ),
      WeightClass w → DriftBound F CS γ →
        (∀ z : ℂ, 0 < z.re → ∀ (i : Fin m) (k : Fin n),
          Integrable (fun ω => XzC (WeightedBuf w F S t ω) z i k) P) ∧
        (∀ z : ℂ, s0 ≤ z.re → |z.im| ≤ z.re / 2 → fro (HmixC w F S t z) ≤ C / z.re) := by
  obtain ⟨C, hC⟩ := sector_response s0 hs0 CS γ
  refine ⟨C, ?_⟩
  intro Ω inst m n B P _ w F S t hw hDB
  refine ⟨fun z hz i k => sd2m_entry_int z hz _ (sd0_meas_WB w F S t) i k, ?_⟩
  intro z hs hzS
  obtain ⟨-, hb0, hfro⟩ := hC Ω m n B P w F S t hw hDB z hs hzS
  exact (fro_opNorm_le_add_smul_mul_psd (HmixC w F S t z) F.C.Sin F.C.psdIn _ hb0).1.trans hfro

/-! ## Holomorphy (`lem:app-dyn-mean`(ii)) -/

/-- Holomorphy of `𝓗` at fixed dimension, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 895–896): "At fixed dimension `z ↦ 𝓗(z)` is holomorphic on `Re z > 0`, since `z ↦ 𝖷_z(M_t)`
is." Entrywise, on the open half-plane. No real counterpart. -/
theorem hmixC_differentiableOn [IsProbabilityMeasure P] {w : ℕ → ℝ} (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (i : Fin m) (k : Fin n) :
    DifferentiableOn ℂ (fun z => HmixC w F S t z i k) {z : ℂ | 0 < z.re} := by
  intro z0 hz0
  have hz0' : 0 < z0.re := hz0
  refine DifferentiableAt.differentiableWithinAt ?_
  set r : ℝ := z0.re / 2 with hr
  have hr0 : 0 < r := by positivity
  set c : ℝ := 1 / r * (1 / (2 * Real.sqrt r)) with hc
  have hc0 : 0 ≤ c := by positivity
  let Fx : ℂ → Ω → ℂ := fun z ω => XzC (WeightedBuf w F S t ω) z i k
  let F' : Ω → ℂ := fun ω =>
    -(Rres (WeightedBuf w F S t ω) (-z0) * XzC (WeightedBuf w F S t ω) z0) i k
  have hmeasX : ∀ z : ℂ, 0 < z.re → Measurable (Fx z) := fun z hz =>
    ((sd0_cont_X z hz).matrix_elem i k).measurable.comp (sd0_meas_WB w F S t)
  have hball : ∀ z ∈ Metric.ball z0 r, r ≤ z.re := by
    intro z hz
    have h1 : |z.re - z0.re| ≤ ‖z - z0‖ := by
      have := Complex.abs_re_le_norm (z - z0)
      simpa using this
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have := (abs_le.mp (h1.trans hz.le)).1
    have h2 := abs_lt.mp (h1.trans_lt hz)
    linarith [h2.1]
  have key := hasDerivAt_integral_of_dominated_loc_of_lip (μ := P) (F := Fx) (F' := F')
    (x₀ := z0) (s := Metric.ball z0 r) (bound := fun _ => c) (Metric.ball_mem_nhds z0 hr0)
    (Filter.mem_of_superset (Metric.ball_mem_nhds z0 hr0) fun z hz =>
      (hmeasX z (lt_of_lt_of_le hr0 (hball z hz))).aestronglyMeasurable) ?_ ?_ ?_ (integrable_const c) ?_
  · exact key.2.differentiableAt
  · exact Integrable.of_bound (hmeasX z0 hz0').aestronglyMeasurable (1 / (2 * Real.sqrt z0.re))
      (ae_of_all _ fun ω => (sd0_entry_le _ i k).trans (sd0_X_bound _ z0 hz0'))
  · have hcont : Continuous (fun K : Mat m n => -(Rres K (-z0) * XzC K z0) i k) :=
      (((sd0_cont_R z0 hz0').matrix_mul (sd0_cont_X z0 hz0')).matrix_elem i k).neg
    exact (hcont.measurable.comp (sd0_meas_WB w F S t)).aestronglyMeasurable
  · refine ae_of_all _ fun ω => ?_
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_nnabs, abs_of_nonneg hc0, Complex.dist_eq, Complex.dist_eq]
    exact sd0_lip _ r hr0 x y (hball x hx) (hball y hy) i k
  · exact ae_of_all _ fun ω => sd0_hasDeriv _ z0 hz0' i k

end Muon.Dynamics

end
