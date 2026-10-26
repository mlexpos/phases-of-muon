import Muon.Setup.Resolvent
import Muon.DetEquiv.Resolvent
import Muon.Drift.Column

/-!
# Appendix E, `lem:app-dyn-mean`(i): the finite resolvent algebra at complex `z ∈ 𝕊`
(interface draft)

Snapshot `cr-2026-10-23`. Coordinator interface package for `lem:app-dyn-mean`(i)–(ii)
(`sections/05-dynamics/section.tex` ll. 768–798, proof ll. 806–893). The proof of (i) asserts that
the finite resolvent algebra of Appendix B holds "verbatim with `z ∈ 𝕊` in place of `s`"
(ll. 815–818). This module states those complex analogues; all statements are deterministic.
It imports no `Muon.Dynamics` module, so `Muon.Dynamics.FiniteMean` can import it.

Conventions.
* The sector is the source's `𝕊 = {z : x = Re z > 0, |Im z| ≤ x/2}` (ll. 758–760), written as the
  two hypotheses `0 < z.re`, `|z.im| ≤ z.re / 2`; they are the two conjuncts of
  `Muon.Dynamics.sectorS` (`FiniteMean.lean`, downstream). Where a constant may depend on a lower
  bound of `Re z`, the hypothesis is `s0 ≤ z.re` with `0 < s0`, and the constant is quantified
  after `s0` and before all data. This single form covers the source's two regimes "`x` in a
  compact `I ⊂ (0,∞)`" (take `s0 = min I`) and "`x ≥ 1`" (take `s0 = 1`); at real `z = s` it is
  the `s ≥ s₀` form of Appendix C.
* `R_z(K) = (KKᵀ + z)⁻¹` is `Muon.Setup.Rres K (-z)` (`Rres K w = (KKᵀ − w)⁻¹`), `R̃_z(K)` is
  `Muon.Setup.Rtil K (-z)`, and `𝖷_z(K)` is `Rres K (-z) * K.map (fun x : ℝ => (x : ℂ))`, which is
  `Muon.Dynamics.Xz K z` of `FiniteMean.lean` by definition. In the source parameter `z` the
  singular set of these objects is `(-∞, 0]` (in the `Rres` parameter `-z` it is `[0, ∞)`).
* The deletion scalars and coefficients over `ℂ` are the field-generic objects of
  `Muon.Drift.Column` (`colR`, `colRt`, `colX`, `colU`, `colV`, `colC`, `colLambda`,
  `colAlpha1..3`) applied to the real data cast to `ℂ`; nothing is redefined. The bridges
  `Rres K (-z) = colR (K.map ofReal) z`, `Rtil K (-z) = colRt (K.map ofReal) z` are proved below.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open scoped Matrix MatrixOrder ComplexOrder
open Matrix Muon.Setup Muon.DetEquiv Muon.Drift

noncomputable section

namespace Muon.Dynamics

/-! ## Bridges between `Rres` and the field-generic resolvents of `Muon.Drift.Column` -/

/-- `R_z(K) = (KKᵀ + z)⁻¹`: the `Rres` form `Rres K (-z)` equals the field-generic `colR` of the
complexified matrix at `z` (`eqn:app-de-RXdef` over `ℂ`). -/
theorem rres_neg_eq_colR {m n : ℕ} (K : Mat m n) (z : ℂ) :
    Rres K (-z) = colR (K.map (fun x : ℝ => (x : ℂ))) z := by
  unfold Rres colR
  congr 1
  rw [neg_smul, sub_neg_eq_add, ← Matrix.transpose_map]
  congr 1
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-- `R̃_z(K) = (KᵀK + z)⁻¹`: the `Rtil` form equals the field-generic `colRt` at `z`. -/
theorem rtil_neg_eq_colRt {m n : ℕ} (K : Mat m n) (z : ℂ) :
    Rtil K (-z) = colRt (K.map (fun x : ℝ => (x : ℂ))) z := by
  unfold Rtil colRt
  congr 1
  rw [neg_smul, sub_neg_eq_add, ← Matrix.transpose_map]
  congr 1
  exact Matrix.map_mul (f := Complex.ofRealHom)

/-! ## Sector bounds (`eqn:app-dyn-sector`) -/

private lemma pe15_self_dot {k : ℕ} (y : Fin k → ℂ) :
    star y ⬝ᵥ y = (‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2 : ℝ) := by
  have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) ((EuclideanSpace.equiv (Fin k) ℂ).symm y)
  rw [EuclideanSpace.inner_eq_star_dotProduct] at h
  simpa [dotProduct_comm] using h

private lemma pe15_cs {k : ℕ} (x y : Fin k → ℂ) :
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
private lemma pe15_energy {k : ℕ} (G : Matrix (Fin k) (Fin k) ℂ) (hG : G.PosSemidef)
    (z : ℂ) (x y : Fin k → ℂ)
    (hy : (G + z • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ y = x) :
    z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ≤
      ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖ := by
  have hpos := hG.re_dotProduct_nonneg y
  have hreal : (star y ⬝ᵥ x).re =
      (star y ⬝ᵥ (G *ᵥ y)).re + z.re * ‖(EuclideanSpace.equiv (Fin k) ℂ).symm y‖ ^ 2 := by
    rw [← hy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re]
    rw [pe15_self_dot y, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hc := pe15_cs x y
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
private lemma pe15_opNorm_le {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Fin b → ℂ, ‖(EuclideanSpace.equiv (Fin a) ℂ).symm (A *ᵥ x)‖ ≤
      c * ‖(EuclideanSpace.equiv (Fin b) ℂ).symm x‖) : opNorm A ≤ c := by
  rw [opNorm_eq_norm, Matrix.l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖(EuclideanSpace.equiv (Fin a) ℂ).symm
      (A *ᵥ (EuclideanSpace.equiv (Fin b) ℂ x))‖ ≤ c * ‖x‖
  simpa using h (EuclideanSpace.equiv (Fin b) ℂ x)

open scoped ComplexOrder in
private lemma pe15_colR_bound {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (z : ℂ) (hz : 0 < z.re)
    (hdet : IsUnit (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)).det) :
    opNorm (colR K z) ≤ 1 / z.re := by
  unfold colR
  refine pe15_opNorm_le _ (one_div_nonneg.mpr hz.le) fun x => ?_
  let y := (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *ᵥ x
  have hy : (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hG : (K * Kᵀ).PosSemidef := by
    rw [← hreal]
    exact Matrix.posSemidef_self_mul_conjTranspose K
  have he := pe15_energy (K * Kᵀ) hG z x y hy
  dsimp [y] at he ⊢
  calc
    _ ≤ ‖(EuclideanSpace.equiv (Fin a) ℂ).symm x‖ / z.re :=
      (le_div_iff₀ hz).2 (by simpa [mul_comm] using he)
    _ = 1 / z.re * ‖(EuclideanSpace.equiv (Fin a) ℂ).symm x‖ := by ring

private lemma pe15_quad {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (y : Fin a → ℂ) :
    star y ⬝ᵥ ((K * Kᵀ) *ᵥ y) = star (Kᵀ *ᵥ y) ⬝ᵥ (Kᵀ *ᵥ y) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]
  have hw : star y ᵥ* K = star (Kᵀ *ᵥ y) := by
    rw [Matrix.star_mulVec, ← hreal, Matrix.conjTranspose_conjTranspose]
  rw [hw]

private lemma pe15_cross {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (y : Fin a → ℂ) (q : Fin b → ℂ) :
    star y ⬝ᵥ (K *ᵥ q) = star (Kᵀ *ᵥ y) ⬝ᵥ q := by
  rw [Matrix.dotProduct_mulVec]
  have hw : star y ᵥ* K = star (Kᵀ *ᵥ y) := by
    rw [Matrix.star_mulVec, ← hreal, Matrix.conjTranspose_conjTranspose]
  rw [hw]

private lemma pe15_mixed_bound {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (hreal : Kᴴ = Kᵀ) (z : ℂ) (hz : 0 < z.re)
    (hdet : IsUnit (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)).det) :
    opNorm (colR K z * K) ≤ 1 / (2 * Real.sqrt z.re) := by
  refine pe15_opNorm_le _ (div_nonneg zero_le_one (by positivity)) fun q => ?_
  let y := (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ))⁻¹ *ᵥ (K *ᵥ q)
  have hy : (K * Kᵀ + z • (1 : Matrix (Fin a) (Fin a) ℂ)) *ᵥ y = K *ᵥ q := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have heq : star (Kᵀ *ᵥ y) ⬝ᵥ q =
      star (Kᵀ *ᵥ y) ⬝ᵥ (Kᵀ *ᵥ y) + z * (star y ⬝ᵥ y) := by
    rw [← pe15_cross K hreal y q, ← hy, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, pe15_quad K hreal]
  have hcs := pe15_cs q (Kᵀ *ᵥ y)
  have hrealEq := congrArg Complex.re heq
  rw [pe15_self_dot (Kᵀ *ᵥ y), pe15_self_dot y] at hrealEq
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

/-- `eqn:app-dyn-sector`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 807–813),
with the invertibility of `KKᵀ + z` and `KᵀK + z` used by the deletion identities (ll. 819–822).
For real `K` and `z ∈ 𝕊`, `x = Re z`:
```latex
\emph{(i), the sector bounds.} For real $K$ and $z\in\mathbb S$, the singular
value decomposition of $K$ gives
\begin{equation}\label{eqn:app-dyn-sector}
\norm{R_z(K)}\le\frac1x,\qquad\norm{\widetilde R_z(K)}\le\frac1x,\qquad
\norm{\mathsf X_z(K)}\le\frac1{2\sqrt x},\qquad\frac{\abs z}{x}\le\frac{\sqrt5}{2},
\end{equation}
because $\abs{s_k^2+z}\ge s_k^2+x$ for each singular value $s_k$.
```
Real counterpart: the norm bounds of `Muon.DetEquiv.lem_app_de_resolvent` (`Resolvent.lean`:322).
At `z = s > 0` the first three bounds specialize to those (the cast to `ℂ` preserves the operator
norm). -/
theorem eqn_app_dyn_sector {m n : ℕ} (K : Mat m n) (z : ℂ) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) :
    opNorm (Rres K (-z)) ≤ 1 / z.re ∧
    opNorm (Rtil K (-z)) ≤ 1 / z.re ∧
    opNorm (Rres K (-z) * K.map (fun x : ℝ => (x : ℂ))) ≤ 1 / (2 * Real.sqrt z.re) ∧
    ‖z‖ / z.re ≤ Real.sqrt 5 / 2 ∧
    IsUnit (K.map (fun x : ℝ => (x : ℂ)) * (K.map (fun x : ℝ => (x : ℂ)))ᵀ +
      z • (1 : Matrix (Fin m) (Fin m) ℂ)).det ∧
    IsUnit ((K.map (fun x : ℝ => (x : ℂ)))ᵀ * K.map (fun x : ℝ => (x : ℂ)) +
      z • (1 : Matrix (Fin n) (Fin n) ℂ)).det := by
  let Kc := K.map (fun x : ℝ => (x : ℂ))
  have hreal : Kcᴴ = Kcᵀ := by
    ext i j
    simp [Kc, Matrix.conjTranspose_apply]
  have hznot : ∀ r : ℝ, 0 ≤ r → -z ≠ (r : ℂ) := by
    intro r hr he
    have hre := congrArg Complex.re he
    simp only [map_neg, Complex.neg_re, Complex.ofReal_re] at hre
    linarith
  obtain ⟨hu, hut⟩ := gram_isUnit K (-z) hznot
  have hG : (K * Kᵀ).map Complex.ofReal = Kc * Kcᵀ := by
    rw [← Matrix.transpose_map]
    exact Matrix.map_mul (f := Complex.ofRealHom)
  have hGt : (Kᵀ * K).map Complex.ofReal = Kcᵀ * Kc := by
    rw [← Matrix.transpose_map]
    exact Matrix.map_mul (f := Complex.ofRealHom)
  rw [hG, neg_smul, sub_neg_eq_add] at hu
  rw [hGt, neg_smul, sub_neg_eq_add] at hut
  have hdet : IsUnit (Kc * Kcᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hu
  have hdett : IsUnit (Kcᵀ * Kc + z • (1 : Matrix (Fin n) (Fin n) ℂ)).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hut
  have hR : opNorm (Rres K (-z)) ≤ 1 / z.re := by
    rw [rres_neg_eq_colR]
    exact pe15_colR_bound Kc hreal z hz hdet
  have hRt : opNorm (Rtil K (-z)) ≤ 1 / z.re := by
    rw [rtil_neg_eq_colRt]
    unfold colRt
    have hrealT : (Kcᵀ)ᴴ = (Kcᵀ)ᵀ := by
      ext i j
      simp [Kc, Matrix.conjTranspose_apply]
    exact pe15_colR_bound Kcᵀ hrealT z hz hdett
  have hX : opNorm (Rres K (-z) * Kc) ≤ 1 / (2 * Real.sqrt z.re) := by
    rw [rres_neg_eq_colR]
    exact pe15_mixed_bound Kc hreal z hz hdet
  have himsq : z.im ^ 2 ≤ (z.re / 2) ^ 2 := by
    have hi := pow_le_pow_left₀ (abs_nonneg z.im) hzS 2
    simpa [sq_abs] using hi
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hzn : ‖z‖ ≤ Real.sqrt 5 / 2 * z.re := by
    refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [himsq, hs5]
  have hzratio : ‖z‖ / z.re ≤ Real.sqrt 5 / 2 := by
    exact (div_le_iff₀ hz).2 (by nlinarith [hzn])
  exact ⟨hR, hRt, hX, hzratio, hdet, hdett⟩

/-! ## Rank-two deletion at complex `z` -/

private abbrev pe15P {m : ℕ} (a b : Fin m → ℂ) : Matrix (Fin m) (Fin 2) ℂ :=
  Matrix.of fun i (j : Fin 2) => ![a i, b i] j

private lemma pe15_P_mulVec {m : ℕ} (a b : Fin m → ℂ) (x : Fin 2 → ℂ) :
    pe15P a b *ᵥ x = x 0 • a + x 1 • b := by
  ext i
  simp [pe15P, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

private lemma pe15_P_quad {m : ℕ} (a b : Fin m → ℂ) (θ00 θ01 θ10 θ11 : ℂ) :
    pe15P a b * !![θ00, θ01; θ10, θ11] * (pe15P a b)ᵀ =
      θ00 • vecMulVec a a + θ01 • vecMulVec a b + θ10 • vecMulVec b a + θ11 • vecMulVec b b := by
  ext i j
  simp [pe15P, Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply,
    Matrix.vecMulVec_apply] <;> ring

private lemma pe15_det_add {m : ℕ} (G0 R0 : Matrix (Fin m) (Fin m) ℂ) (hR : G0 * R0 = 1)
    (P : Matrix (Fin m) (Fin 2) ℂ) (Q : Matrix (Fin 2) (Fin 2) ℂ) :
    (G0 + P * Q * Pᵀ).det = G0.det * (1 + Q * (Pᵀ * R0 * P)).det := by
  have hG : G0 + P * Q * Pᵀ = G0 * (1 + R0 * P * Q * Pᵀ) := by
    simp only [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul]
  rw [hG, Matrix.det_mul]
  congr 1
  have h1 : R0 * P * Q * Pᵀ = (R0 * P) * (Q * Pᵀ) := by simp only [Matrix.mul_assoc]
  have h2 : Q * Pᵀ * (R0 * P) = Q * (Pᵀ * R0 * P) := by simp only [Matrix.mul_assoc]
  rw [h1, Matrix.det_one_add_mul_comm, h2]

private lemma pe15_inv {m : ℕ} (G0 R0 : Matrix (Fin m) (Fin m) ℂ) (hR : G0 * R0 = 1)
    (P : Matrix (Fin m) (Fin 2) ℂ) (Q T : Matrix (Fin 2) (Fin 2) ℂ)
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
    rw [Matrix.mul_sub, show G0 * (R0 * P * T * Pᵀ * R0) =
      (G0 * R0) * (P * T * Pᵀ * R0) by simp only [Matrix.mul_assoc], hR, Matrix.one_mul]
  have hPX : P * Q * Pᵀ * (R0 - R0 * P * T * Pᵀ * R0)
      = P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0 := by
    simp only [Matrix.mul_sub, Matrix.mul_assoc]
  rw [Matrix.add_mul, hGX, hPX]
  have hfin : (1 - P * T * Pᵀ * R0) +
      (P * Q * Pᵀ * R0 - P * Q * Pᵀ * R0 * P * T * Pᵀ * R0) =
      1 + P * (Q - T - Q * (Pᵀ * R0 * P) * T) * Pᵀ * R0 := by
    rw [hexp]; abel
  rw [hfin, hz, add_zero]

private lemma pe15_sand {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ)
    (P : Matrix (Fin m) (Fin 2) ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ)
    (hsym : R0ᵀ = R0) :
    R0 * P * T * Pᵀ * R0 = (R0 * P) * T * (R0 * P)ᵀ := by
  rw [Matrix.transpose_mul, hsym]
  simp only [Matrix.mul_assoc]

private lemma pe15_RP {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ) (a b : Fin m → ℂ) :
    R0 * pe15P a b = pe15P (R0 *ᵥ a) (R0 *ᵥ b) := by
  ext i j
  fin_cases j <;> simp [pe15P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private lemma pe15_apply {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ)
    (P : Matrix (Fin m) (Fin 2) ℂ) (T : Matrix (Fin 2) (Fin 2) ℂ) (c : Fin 2 → ℂ) :
    (R0 - R0 * P * T * Pᵀ * R0) *ᵥ (P *ᵥ c) =
      R0 *ᵥ (P *ᵥ (c - T *ᵥ (Pᵀ *ᵥ (R0 *ᵥ (P *ᵥ c))))) := by
  rw [Matrix.sub_mulVec]
  simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private lemma pe15_G {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ) (h z : ℂ)
    (u : Fin m → ℂ) (v : Fin n → ℂ) :
    (M0 + h • vecMulVec u v) * (M0 + h • vecMulVec u v)ᵀ +
        z • (1 : Matrix (Fin m) (Fin m) ℂ) =
      (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) +
        pe15P u (M0 *ᵥ v) * !![h ^ 2 * (∑ x, v x ^ 2), h; h, 0] * (pe15P u (M0 *ᵥ v))ᵀ := by
  have hA : ∀ i j : Fin m,
      ∑ x, (M0 i x + h * (u i * v x)) * (M0 j x + h * (u j * v x)) =
      ∑ x, M0 i x * M0 j x +
        (h * u j * ∑ x, M0 i x * v x) + (h * u i * ∑ x, M0 j x * v x) +
          h ^ 2 * u i * u j * ∑ x, v x ^ 2 := by
    intro i j
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by ring
  ext i j
  simp only [pe15P, Matrix.add_apply, Matrix.smul_apply, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply,
    Matrix.one_apply, Fin.sum_univ_two, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]
  rw [hA i j]
  ring

private lemma pe15_R_symm {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℂ) (z : ℂ) :
    (colR M z)ᵀ = colR M z := by
  unfold colR
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul, add_comm]

private lemma pe15_cross_symm {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ)
    (hsym : R0ᵀ = R0) (a b : Fin m → ℂ) :
    b ⬝ᵥ (R0 *ᵥ a) = a ⬝ᵥ (R0 *ᵥ b) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsym, dotProduct_comm]

private lemma pe15_gen {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ)
    (A : Matrix (Fin m) (Fin 2) ℂ) (i j : Fin 2) :
    (Aᵀ * R0 * A) i j = (fun k => A k i) ⬝ᵥ (R0 *ᵥ fun k => A k j) := by
  simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

private lemma pe15_W {m : ℕ} (R0 : Matrix (Fin m) (Fin m) ℂ) (hsym : R0ᵀ = R0)
    (a b : Fin m → ℂ) :
    (pe15P a b)ᵀ * R0 * pe15P a b =
      !![a ⬝ᵥ (R0 *ᵥ a), a ⬝ᵥ (R0 *ᵥ b);
         a ⬝ᵥ (R0 *ᵥ b), b ⬝ᵥ (R0 *ᵥ b)] := by
  have hc := pe15_cross_symm R0 hsym a b
  have ca : (fun k => pe15P a b k 0) = a := by funext k; simp [pe15P]
  have cb : (fun k => pe15P a b k 1) = b := by funext k; simp [pe15P]
  ext i j
  rw [pe15_gen]
  fin_cases i <;> fin_cases j <;> simp [ca, cb, hc]

private lemma pe15_sandwich {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ) (z : ℂ)
    (hR0 : IsUnit (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det)
    (hRt0 : IsUnit (M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ)).det) :
    M0ᵀ * colR M0 z * M0 = 1 - z • colRt M0 z := by
  unfold colR colRt
  have key : M0ᵀ * (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) =
      (M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ)) * M0ᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  set A := M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)
  set B := M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ)
  have hcomm : M0ᵀ * A⁻¹ = B⁻¹ * M0ᵀ := by
    calc M0ᵀ * A⁻¹ = (B⁻¹ * B) * (M0ᵀ * A⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hRt0, Matrix.one_mul]
      _ = B⁻¹ * ((B * M0ᵀ) * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * ((M0ᵀ * A) * A⁻¹) := by rw [key]
      _ = B⁻¹ * (M0ᵀ * (A * A⁻¹)) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * M0ᵀ := by rw [Matrix.mul_nonsing_inv _ hR0, Matrix.mul_one]
  have hMB : M0ᵀ * M0 = B - z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [show B = M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ) by rfl,
      add_sub_cancel_right]
  calc M0ᵀ * A⁻¹ * M0 = B⁻¹ * (M0ᵀ * M0) := by rw [hcomm, Matrix.mul_assoc]
    _ = B⁻¹ * (B - z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by rw [hMB]
    _ = 1 - z • B⁻¹ := by
      rw [Matrix.mul_sub, Matrix.nonsing_inv_mul _ hRt0, Matrix.mul_smul, Matrix.mul_one]

private lemma pe15_dot_mulVec {a b : ℕ} (K : Matrix (Fin a) (Fin b) ℂ)
    (y : Fin a → ℂ) (x : Fin b → ℂ) :
    y ⬝ᵥ (K *ᵥ x) = (Kᵀ *ᵥ y) ⬝ᵥ x := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]

private lemma pe15_W11 {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ) (z : ℂ)
    (hR0 : IsUnit (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det)
    (hRt0 : IsUnit (M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ)).det)
    (v : Fin n → ℂ) :
    (M0 *ᵥ v) ⬝ᵥ (colR M0 z *ᵥ (M0 *ᵥ v)) =
      v ⬝ᵥ v - z * colV M0 v z := by
  have hid := pe15_sandwich M0 z hR0 hRt0
  rw [dotProduct_comm, pe15_dot_mulVec,
    show M0ᵀ *ᵥ (colR M0 z *ᵥ (M0 *ᵥ v)) =
      (M0ᵀ * colR M0 z * M0) *ᵥ v by simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc],
    hid, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, sub_dotProduct,
    smul_dotProduct, dotProduct_comm (colRt M0 z *ᵥ v) v]
  rfl

private lemma pe15_scal (h z U C V N L a1 a2 a3 : ℂ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + z * h ^ 2 * U * V)
    (ha1 : a1 = h * (1 + h * C) / L) (ha2 : a2 = h ^ 2 * U / L)
    (ha3 : a3 = -(z * h ^ 2 * V) / L) :
    (1 + !![h ^ 2 * N, h; h, 0] * !![U, C; C, N - z * V]) *
      !![-a3, a1; a1, -a2] = !![h ^ 2 * N, h; h, 0] := by
  subst ha1 ha2 ha3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> (subst hLdef; ring)

private lemma pe15_vec (h z U C V N L a1 a2 a3 : ℂ) (hL : L ≠ 0)
    (hLdef : L = (1 + h * C) ^ 2 + z * h ^ 2 * U * V)
    (ha1 : a1 = h * (1 + h * C) / L) (ha2 : a2 = h ^ 2 * U / L)
    (ha3 : a3 = -(z * h ^ 2 * V) / L) :
    h • (![h * N, 1] - !![-a3, a1; a1, -a2] *ᵥ
      (!![U, C; C, N - z * V] *ᵥ ![h * N, 1])) = ![-a3, a1] := by
  subst ha1 ha2 ha3
  ext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;>
    field_simp <;> (subst hLdef; ring)

private lemma pe15_det_rel {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ) (h : ℂ)
    (u : Fin m → ℂ) (v : Fin n → ℂ) (M : Matrix (Fin m) (Fin n) ℂ) (z : ℂ)
    (hM : M = M0 + h • vecMulVec u v)
    (hR0 : IsUnit (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det)
    (hRt0 : IsUnit (M0ᵀ * M0 + z • (1 : Matrix (Fin n) (Fin n) ℂ)).det) :
    (M * Mᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det =
      (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det *
        colLambda M0 h u v z := by
  subst hM
  have hG0 : (M0 * M0ᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) * colR M0 z = 1 :=
    Matrix.mul_nonsing_inv _ hR0
  have hsym := pe15_R_symm M0 z
  have hU : u ⬝ᵥ (colR M0 z *ᵥ u) = colU M0 u z := rfl
  have hC : u ⬝ᵥ (colR M0 z *ᵥ (M0 *ᵥ v)) = colC M0 u v z := by
    unfold colC colX
    rw [Matrix.mulVec_mulVec]
  rw [pe15_G M0 h z u v, pe15_det_add _ _ hG0, pe15_W _ hsym, hU, hC,
    pe15_W11 M0 z hR0 hRt0 v]
  congr 1
  rw [Matrix.det_fin_two]
  simp [colLambda, Matrix.mul_apply, Fin.sum_univ_two, dotProduct]
  ring

private lemma pe15_scal_col {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ)
    (h z N : ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ)
    (hL : colLambda M0 h u v z ≠ 0) :
    (1 + !![h ^ 2 * N, h; h, 0] *
      !![colU M0 u z, colC M0 u v z; colC M0 u v z, N - z * colV M0 v z]) *
      !![-colAlpha3 M0 h u v z, colAlpha1 M0 h u v z;
         colAlpha1 M0 h u v z, -colAlpha2 M0 h u v z] =
      !![h ^ 2 * N, h; h, 0] := by
  exact pe15_scal h z (colU M0 u z) (colC M0 u v z) (colV M0 v z) N
    (colLambda M0 h u v z) (colAlpha1 M0 h u v z) (colAlpha2 M0 h u v z)
    (colAlpha3 M0 h u v z) hL rfl rfl rfl rfl

private lemma pe15_vec_col {m n : ℕ} (M0 : Matrix (Fin m) (Fin n) ℂ)
    (h z N : ℂ) (u : Fin m → ℂ) (v : Fin n → ℂ)
    (hL : colLambda M0 h u v z ≠ 0) :
    h • (![h * N, 1] -
      !![-colAlpha3 M0 h u v z, colAlpha1 M0 h u v z;
         colAlpha1 M0 h u v z, -colAlpha2 M0 h u v z] *ᵥ
        (!![colU M0 u z, colC M0 u v z; colC M0 u v z, N - z * colV M0 v z] *ᵥ
          ![h * N, 1])) =
      ![-colAlpha3 M0 h u v z, colAlpha1 M0 h u v z] := by
  exact pe15_vec h z (colU M0 u z) (colC M0 u v z) (colV M0 v z) N
    (colLambda M0 h u v z) (colAlpha1 M0 h u v z) (colAlpha2 M0 h u v z)
    (colAlpha3 M0 h u v z) hL rfl rfl rfl rfl

/-- `lem:app-de-deletion` at `z ∈ 𝕊` (identities and `ΛΛ' = 1`), snapshot `cr-2026-10-23`.
Source (`sections/05-dynamics/section.tex` ll. 815–825):
```latex
\emph{(i), the deletion identities.} The identities of
\cref{lem:app-de-deletion} and \cref{lem:app-drift-column} hold verbatim
with $z\in\mathbb S$ in place of $s$, the scalars
$\mathsf U,\mathsf V,\mathsf C,\Lambda$ and the coefficients now complex. Their
proofs are algebraic: they use the block inverse
\cref{eqn:app-de-blockinverse} with $s$ replaced by $z$, which exists since
$z\Id+KK^\T$ is invertible, and the invertibility of the two-by-two matrix
$S^{-1}+W$, which holds because Sylvester's identity in the same proof gives
$\det\mathcal L(M)=\Lambda\det\mathcal L(M_0)$ with both determinants nonzero.
The relation $\Lambda\Lambda'=1$ holds as there.
```
Real counterpart: `Muon.DetEquiv.lem_app_de_deletion` (`Resolvent.lean`:664; its docstring quotes
`lem:app-de-deletion`), clauses 1–4 (`Λ > 0` becomes `Λ ≠ 0`). The column identities over `ℂ` are
`Muon.Drift.lem_app_drift_column_field_i/ii` (`Column.lean`:136,192); their hypotheses `hΛ`,
`hdel` are clauses 1–2 here and `hR₀`, `hRt₀` come from `eqn_app_dyn_sector`.
Data: real `M₀, 𝗁, 𝗎, 𝗏` with `M = M₀ + 𝗁 𝗎⊗𝗏`, cast to `ℂ`; `Λ'` is `colLambda` computed from `M`
and `-𝗁`. -/
theorem lem_app_de_deletion_sector {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (z : ℂ) (hM : M = M₀ + h • outer u v) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) :
    let M₀c := M₀.map (fun x : ℝ => (x : ℂ))
    let Mc := M.map (fun x : ℝ => (x : ℂ))
    let uc : Fin m → ℂ := fun i => (u i : ℂ)
    let vc : Fin n → ℂ := fun i => (v i : ℂ)
    let hc : ℂ := (h : ℂ)
    colLambda M₀c hc uc vc z ≠ 0 ∧
    colR Mc z - colR M₀c z =
      (colAlpha3 M₀c hc uc vc z) • vecMulVec (colR M₀c z *ᵥ uc) (colR M₀c z *ᵥ uc)
        - (colAlpha1 M₀c hc uc vc z) • vecMulVec (colR M₀c z *ᵥ uc) (colX M₀c z *ᵥ vc)
        - (colAlpha1 M₀c hc uc vc z) • vecMulVec (colX M₀c z *ᵥ vc) (colR M₀c z *ᵥ uc)
        + (colAlpha2 M₀c hc uc vc z) • vecMulVec (colX M₀c z *ᵥ vc) (colX M₀c z *ᵥ vc) ∧
    hc • (colR Mc z *ᵥ (Mc *ᵥ vc)) =
      (-colAlpha3 M₀c hc uc vc z) • (colR M₀c z *ᵥ uc)
        + (colAlpha1 M₀c hc uc vc z) • (colX M₀c z *ᵥ vc) ∧
    colLambda M₀c hc uc vc z * colLambda Mc (-hc) uc vc z = 1 := by
  dsimp only
  let M0c := M₀.map (fun x : ℝ => (x : ℂ))
  let Mc := M.map (fun x : ℝ => (x : ℂ))
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  let hc : ℂ := (h : ℂ)
  have hMc : Mc = M0c + hc • vecMulVec uc vc := by
    ext i j
    simp [Mc, M0c, hc, uc, vc, hM, outer, Matrix.vecMulVec_apply]
  obtain ⟨-, -, -, -, hdet0, hdett0⟩ := eqn_app_dyn_sector M₀ z hz hzS
  obtain ⟨-, -, -, -, hdetM, hdettM⟩ := eqn_app_dyn_sector M z hz hzS
  have hsym := pe15_R_symm M0c z
  have hG0 : (M0c * M0cᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) * colR M0c z = 1 :=
    Matrix.mul_nonsing_inv _ hdet0
  have hrel1 := pe15_det_rel M0c hc uc vc Mc z hMc hdet0 hdett0
  have hM0c : M0c = Mc + (-hc) • vecMulVec uc vc := by
    rw [hMc]
    module
  have hrel2 := pe15_det_rel Mc (-hc) uc vc M0c z hM0c hdetM hdettM
  have hLne : colLambda M0c hc uc vc z ≠ 0 := by
    intro hL
    apply hdetM.ne_zero
    rw [hrel1, hL, mul_zero]
  have hNv : (∑ x, vc x ^ 2) = (sqNorm v : ℂ) := by
    simp [vc, sqNorm, Complex.ofReal_sum]
  have hvv : vc ⬝ᵥ vc = (sqNorm v : ℂ) := by
    rw [← hNv]
    simp [dotProduct, pow_two]
  have hGM : Mc * Mcᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ) =
      (M0c * M0cᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) +
        pe15P uc (M0c *ᵥ vc) * !![hc ^ 2 * (sqNorm v : ℂ), hc; hc, 0] *
          (pe15P uc (M0c *ᵥ vc))ᵀ := by
    rw [hMc, pe15_G, hNv]
  have hU : uc ⬝ᵥ (colR M0c z *ᵥ uc) = colU M0c uc z := rfl
  have hC : uc ⬝ᵥ (colR M0c z *ᵥ (M0c *ᵥ vc)) = colC M0c uc vc z := by
    unfold colC colX
    rw [Matrix.mulVec_mulVec]
  have hXv : colX M0c z *ᵥ vc = colR M0c z *ᵥ (M0c *ᵥ vc) := by
    unfold colX
    rw [Matrix.mulVec_mulVec]
  have hT : (1 + !![hc ^ 2 * (sqNorm v : ℂ), hc; hc, 0] *
      ((pe15P uc (M0c *ᵥ vc))ᵀ * colR M0c z * pe15P uc (M0c *ᵥ vc))) *
      !![-colAlpha3 M0c hc uc vc z, colAlpha1 M0c hc uc vc z;
         colAlpha1 M0c hc uc vc z, -colAlpha2 M0c hc uc vc z] =
      !![hc ^ 2 * (sqNorm v : ℂ), hc; hc, 0] := by
    rw [pe15_W _ hsym, hU, hC, pe15_W11 M0c z hdet0 hdett0 vc]
    rw [hvv]
    exact pe15_scal_col M0c hc z (sqNorm v : ℂ) uc vc hLne
  have hdecomp : colR Mc z = colR M0c z - colR M0c z * pe15P uc (M0c *ᵥ vc) *
      !![-colAlpha3 M0c hc uc vc z, colAlpha1 M0c hc uc vc z;
         colAlpha1 M0c hc uc vc z, -colAlpha2 M0c hc uc vc z] *
      (pe15P uc (M0c *ᵥ vc))ᵀ * colR M0c z := by
    show (Mc * Mcᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹ = _
    rw [hGM]
    exact pe15_inv _ _ hG0 _ _ _ hT
  have hdec2 : colR Mc z = colR M0c z - (colR M0c z * pe15P uc (M0c *ᵥ vc)) *
      !![-colAlpha3 M0c hc uc vc z, colAlpha1 M0c hc uc vc z;
         colAlpha1 M0c hc uc vc z, -colAlpha2 M0c hc uc vc z] *
      (colR M0c z * pe15P uc (M0c *ᵥ vc))ᵀ := by
    rw [hdecomp, pe15_sand _ _ _ hsym]
  have conj2 : colR Mc z - colR M0c z =
      colAlpha3 M0c hc uc vc z • vecMulVec (colR M0c z *ᵥ uc) (colR M0c z *ᵥ uc)
        - colAlpha1 M0c hc uc vc z • vecMulVec (colR M0c z *ᵥ uc) (colX M0c z *ᵥ vc)
        - colAlpha1 M0c hc uc vc z • vecMulVec (colX M0c z *ᵥ vc) (colR M0c z *ᵥ uc)
        + colAlpha2 M0c hc uc vc z • vecMulVec (colX M0c z *ᵥ vc) (colX M0c z *ᵥ vc) := by
    rw [hdec2, pe15_RP, pe15_P_quad, hXv]
    module
  have hMv : Mc *ᵥ vc = pe15P uc (M0c *ᵥ vc) *ᵥ ![hc * (sqNorm v : ℂ), 1] := by
    rw [hMc, pe15_P_mulVec]
    ext i
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.vecMulVec_mulVec,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [hvv]
    simp [smul_eq_mul]
    ring
  have hv := pe15_vec_col M0c hc z (sqNorm v : ℂ) uc vc hLne
  have conj3 : hc • (colR Mc z *ᵥ (Mc *ᵥ vc)) =
      (-colAlpha3 M0c hc uc vc z) • (colR M0c z *ᵥ uc) +
        colAlpha1 M0c hc uc vc z • (colX M0c z *ᵥ vc) := by
    have hWc : (pe15P uc (M0c *ᵥ vc))ᵀ *ᵥ
        (colR M0c z *ᵥ (pe15P uc (M0c *ᵥ vc) *ᵥ ![hc * (sqNorm v : ℂ), 1])) =
        ((pe15P uc (M0c *ᵥ vc))ᵀ * colR M0c z * pe15P uc (M0c *ᵥ vc)) *ᵥ
          ![hc * (sqNorm v : ℂ), 1] := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [hdecomp, hMv, pe15_apply, hWc, pe15_W _ hsym, hU, hC,
      pe15_W11 M0c z hdet0 hdett0 vc]
    rw [hvv]
    rw [← Matrix.mulVec_smul (colR M0c z) hc,
      ← Matrix.mulVec_smul (pe15P uc (M0c *ᵥ vc)) hc, hv, pe15_P_mulVec]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.mulVec_add, Matrix.mulVec_smul, hXv]
  have hprod : colLambda M0c hc uc vc z * colLambda Mc (-hc) uc vc z = 1 := by
    apply mul_left_cancel₀ hdet0.ne_zero
    rw [mul_one]
    calc
      (M0c * M0cᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det *
          (colLambda M0c hc uc vc z * colLambda Mc (-hc) uc vc z) =
        ((M0c * M0cᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det *
          colLambda M0c hc uc vc z) * colLambda Mc (-hc) uc vc z := by ring
      _ = (Mc * Mcᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det *
          colLambda Mc (-hc) uc vc z := by rw [← hrel1]
      _ = (M0c * M0cᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)).det := hrel2.symm
  exact ⟨hLne, conj2, conj3, hprod⟩

private def pe15Euc {k : ℕ} (x : Fin k → ℂ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin k) ℂ).symm x‖

private lemma pe15_cast_euc_sq {k : ℕ} (u : Vec k) :
    pe15Euc (fun i => (u i : ℂ)) ^ 2 = sqNorm u := by
  unfold pe15Euc sqNorm
  rw [EuclideanSpace.norm_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

private lemma pe15_norm_dot {k : ℕ} (x y : Fin k → ℂ) :
    ‖star x ⬝ᵥ y‖ ≤ pe15Euc x * pe15Euc y := by
  unfold pe15Euc
  calc
    ‖star x ⬝ᵥ y‖ = ‖inner ℂ ((EuclideanSpace.equiv (Fin k) ℂ).symm x)
        ((EuclideanSpace.equiv (Fin k) ℂ).symm y)‖ := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [dotProduct_comm]
    _ ≤ _ := norm_inner_le_norm _ _

open scoped Matrix.Norms.L2Operator in
private lemma pe15_apply_bound {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (x : Fin b → ℂ) :
    pe15Euc (A *ᵥ x) ≤ opNorm A * pe15Euc x := by
  unfold pe15Euc
  rw [opNorm_eq_norm]
  exact Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin b) ℂ).symm x)

private lemma pe15_quad_scalar_bound {k : ℕ} (A : Matrix (Fin k) (Fin k) ℂ)
    (u : Vec k) (x : ℝ) (hx : 0 < x) (hA : opNorm A ≤ 1 / x) :
    ‖(fun i => (u i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (u i : ℂ))‖ ≤ sqNorm u / x := by
  let uc : Fin k → ℂ := fun i => (u i : ℂ)
  have hstar : star uc = uc := by funext i; simp [uc]
  have h1 := pe15_norm_dot uc (A *ᵥ uc)
  rw [hstar] at h1
  have h2 := pe15_apply_bound A uc
  have hnon : 0 ≤ pe15Euc uc := norm_nonneg _
  have hsq := pe15_cast_euc_sq u
  change ‖uc ⬝ᵥ (A *ᵥ uc)‖ ≤ sqNorm u / x
  calc
    _ ≤ pe15Euc uc * pe15Euc (A *ᵥ uc) := h1
    _ ≤ pe15Euc uc * (opNorm A * pe15Euc uc) :=
      mul_le_mul_of_nonneg_left h2 hnon
    _ ≤ pe15Euc uc * ((1 / x) * pe15Euc uc) := by gcongr
    _ = sqNorm u / x := by rw [← hsq]; ring

private lemma pe15_cross_scalar_bound {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℂ)
    (u : Vec m) (v : Vec n) (x : ℝ) (hx : 0 < x)
    (hA : opNorm A ≤ 1 / (2 * Real.sqrt x)) :
    ‖(fun i => (u i : ℂ)) ⬝ᵥ (A *ᵥ fun i => (v i : ℂ))‖ ≤
      (sqNorm u + sqNorm v) / (4 * Real.sqrt x) := by
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  have hstar : star uc = uc := by funext i; simp [uc]
  have h1 := pe15_norm_dot uc (A *ᵥ vc)
  rw [hstar] at h1
  have h2 := pe15_apply_bound A vc
  have heu : 0 ≤ pe15Euc uc := norm_nonneg _
  have hev : 0 ≤ pe15Euc vc := norm_nonneg _
  have hsu := pe15_cast_euc_sq u
  have hsv := pe15_cast_euc_sq v
  have huv : pe15Euc uc * pe15Euc vc ≤ (sqNorm u + sqNorm v) / 2 := by
    nlinarith [sq_nonneg (pe15Euc uc - pe15Euc vc)]
  change ‖uc ⬝ᵥ (A *ᵥ vc)‖ ≤ _
  calc
    _ ≤ pe15Euc uc * pe15Euc (A *ᵥ vc) := h1
    _ ≤ pe15Euc uc * (opNorm A * pe15Euc vc) := mul_le_mul_of_nonneg_left h2 heu
    _ ≤ pe15Euc uc * ((1 / (2 * Real.sqrt x)) * pe15Euc vc) := by gcongr
    _ = (pe15Euc uc * pe15Euc vc) / (2 * Real.sqrt x) := by ring
    _ ≤ ((sqNorm u + sqNorm v) / 2) / (2 * Real.sqrt x) := by
      gcongr
    _ = (sqNorm u + sqNorm v) / (4 * Real.sqrt x) := by ring

/-- `eqn:app-dyn-sector-inverse`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 825–831): in the setting of `lem_app_de_deletion_sector`, with `𝖭 = ‖𝗎‖² + ‖𝗏‖²`
(`sqNorm u + sqNorm v`) and `x = Re z`,
```latex
With
\cref{eqn:app-dyn-sector} for the primed scalars,
$\abs{\mathsf C'}\le\mathsf N/(4\sqrt x)$ and
$\abs{z\mathsf U'\mathsf V'}\le(\sqrt5/2)\,\mathsf N^2/(4x)$, so the inequality
$(1+a)^2+b^2\le(1+a+b)^2$ gives
\begin{equation}\label{eqn:app-dyn-sector-inverse}
\abs\Lambda^{-1}=\abs{\Lambda'}\le\Big(1+\frac{\abs{\mathsf h}\,\mathsf N}{\sqrt x}\Big)^2 .
\end{equation}
```
Real counterpart: the last clause of `Muon.DetEquiv.lem_app_de_deletion` (`eqn:app-de-Lambda-inverse`,
constant `3/4` in place of `1`); the complex bound at `z = s` is the weaker real bound with `1`. -/
theorem eqn_app_dyn_sector_inverse {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (z : ℂ) (hM : M = M₀ + h • outer u v) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) :
    ‖colLambda (M₀.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖⁻¹ =
      ‖colLambda (M.map (fun x : ℝ => (x : ℂ))) (-(h : ℂ)) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖ ∧
    ‖colLambda (M₀.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun i => (u i : ℂ))
        (fun i => (v i : ℂ)) z‖⁻¹ ≤
      (1 + |h| * (sqNorm u + sqNorm v) / Real.sqrt z.re) ^ 2 := by
  let M0c := M₀.map (fun x : ℝ => (x : ℂ))
  let Mc := M.map (fun x : ℝ => (x : ℂ))
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  let hc : ℂ := (h : ℂ)
  obtain ⟨hL, -, -, hprod⟩ := lem_app_de_deletion_sector M₀ h u v M z hM hz hzS
  have hfirst : ‖colLambda M0c hc uc vc z‖⁻¹ =
      ‖colLambda Mc (-hc) uc vc z‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hprod]
  obtain ⟨hR, hRt, hX, hzNorm, -, -⟩ := eqn_app_dyn_sector M z hz hzS
  rw [rres_neg_eq_colR] at hR
  rw [rtil_neg_eq_colRt] at hRt
  rw [rres_neg_eq_colR] at hX
  have hU : ‖colU Mc uc z‖ ≤ sqNorm u / z.re := by
    exact pe15_quad_scalar_bound (colR Mc z) u z.re hz hR
  have hV : ‖colV Mc vc z‖ ≤ sqNorm v / z.re := by
    exact pe15_quad_scalar_bound (colRt Mc z) v z.re hz hRt
  have hC : ‖colC Mc uc vc z‖ ≤
      (sqNorm u + sqNorm v) / (4 * Real.sqrt z.re) := by
    exact pe15_cross_scalar_bound (colX Mc z) u v z.re hz hX
  have hNu : 0 ≤ sqNorm u := by
    unfold sqNorm
    positivity
  have hNv : 0 ≤ sqNorm v := by
    unfold sqNorm
    positivity
  have hN : 0 ≤ sqNorm u + sqNorm v := add_nonneg hNu hNv
  have hs : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hz
  have hs2 : Real.sqrt z.re ^ 2 = z.re := Real.sq_sqrt hz.le
  have hs5le : Real.sqrt 5 ≤ 3 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  have hzNorm' : ‖z‖ ≤ (3 / 2 : ℝ) * z.re := by
    calc
      ‖z‖ ≤ Real.sqrt 5 / 2 * z.re := (div_le_iff₀ hz).mp hzNorm
      _ ≤ (3 / 2 : ℝ) * z.re := by gcongr
  have hUV : ‖colU Mc uc z‖ * ‖colV Mc vc z‖ ≤
      (sqNorm u + sqNorm v) ^ 2 / (4 * z.re ^ 2) := by
    calc
      _ ≤ (sqNorm u / z.re) * (sqNorm v / z.re) := by gcongr
      _ ≤ ((sqNorm u + sqNorm v) ^ 2 / 4) / z.re ^ 2 := by
        have huv : sqNorm u * sqNorm v ≤ (sqNorm u + sqNorm v) ^ 2 / 4 := by
          nlinarith [sq_nonneg (sqNorm u - sqNorm v)]
        calc
          (sqNorm u / z.re) * (sqNorm v / z.re) =
              (sqNorm u * sqNorm v) / z.re ^ 2 := by ring
          _ ≤ ((sqNorm u + sqNorm v) ^ 2 / 4) / z.re ^ 2 := by gcongr
      _ = _ := by ring
  let t := |h| * (sqNorm u + sqNorm v) / Real.sqrt z.re
  have ht : 0 ≤ t := by positivity
  have hterm1 : ‖(1 - hc * colC Mc uc vc z) ^ 2‖ ≤ (1 + t / 4) ^ 2 := by
    rw [norm_pow]
    have hone : ‖(1 : ℂ) - hc * colC Mc uc vc z‖ ≤
        1 + |h| * ((sqNorm u + sqNorm v) / (4 * Real.sqrt z.re)) := by
      calc
        _ ≤ ‖(1 : ℂ)‖ + ‖hc * colC Mc uc vc z‖ := norm_sub_le _ _
        _ ≤ 1 + |h| * ((sqNorm u + sqNorm v) / (4 * Real.sqrt z.re)) := by
          rw [norm_one, norm_mul, show ‖hc‖ = |h| by simp [hc]]
          gcongr
    have he : |h| * ((sqNorm u + sqNorm v) / (4 * Real.sqrt z.re)) = t / 4 := by
      dsimp [t]
      ring
    rw [he] at hone
    exact pow_le_pow_left₀ (norm_nonneg _) hone 2
  have hterm2 : ‖z * (-hc) ^ 2 * colU Mc uc z * colV Mc vc z‖ ≤ 3 / 8 * t ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
      show ‖hc‖ = |h| by simp [hc]]
    calc
      ‖z‖ * |h| ^ 2 * ‖colU Mc uc z‖ * ‖colV Mc vc z‖ =
          ‖z‖ * |h| ^ 2 * (‖colU Mc uc z‖ * ‖colV Mc vc z‖) := by ring
      _ ≤ ((3 / 2 : ℝ) * z.re) * |h| ^ 2 *
              (‖colU Mc uc z‖ * ‖colV Mc vc z‖) := by
        gcongr
      _ ≤ ((3 / 2 : ℝ) * z.re) * |h| ^ 2 *
              ((sqNorm u + sqNorm v) ^ 2 / (4 * z.re ^ 2)) := by
        gcongr
      _ = 3 / 8 * t ^ 2 := by
        dsimp [t]
        rw [div_pow, hs2]
        field_simp
        ring
  have hLam : ‖colLambda Mc (-hc) uc vc z‖ ≤ (1 + t) ^ 2 := by
    unfold colLambda
    calc
      ‖(1 + -hc * colC Mc uc vc z) ^ 2 +
          z * (-hc) ^ 2 * colU Mc uc z * colV Mc vc z‖
        ≤ ‖(1 - hc * colC Mc uc vc z) ^ 2‖ +
            ‖z * (-hc) ^ 2 * colU Mc uc z * colV Mc vc z‖ := by
              convert norm_add_le _ _ using 2 <;> ring
      _ ≤ (1 + t / 4) ^ 2 + 3 / 8 * t ^ 2 := add_le_add hterm1 hterm2
      _ ≤ (1 + t) ^ 2 := by nlinarith
  refine ⟨hfirst, ?_⟩
  rw [hfirst]
  simpa [M0c, Mc, uc, vc, hc, t] using hLam

/-- `eqn:app-dyn-Rebeta`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 832–839):
in the setting of `lem_app_de_deletion_sector`, `α₂ = 𝗁² 𝗎ᵀ R_z(M) 𝗎` and `Re α₂ ≥ 0`.
```latex
Moreover, multiplying \cref{eqn:app-drift-column} by $\mathsf u^\T$ gives
$\mathsf h\,\mathsf u^\T R_z(M)\mathsf u=\mathsf h\mathsf U/\Lambda$, so
$\alpha_2=\mathsf h^2\,\mathsf u^\T R_z(M)\mathsf u$, and
\begin{equation}\label{eqn:app-dyn-Rebeta}
\Ree\alpha_2\ge0 ,
\end{equation}
since the eigenvalues of $R_z(M)$ are $(s_k^2+z)^{-1}$ and
$(1/z)$, all with nonnegative real part.
```
Real counterpart: `α₂ ≥ 0` in `Muon.Drift.lem_app_drift_coeffmoments` (`Coefficients.lean`:1379). -/
theorem eqn_app_dyn_Rebeta {m n : ℕ} (M₀ : Mat m n) (h : ℝ) (u : Vec m) (v : Vec n)
    (M : Mat m n) (z : ℂ) (hM : M = M₀ + h • outer u v) (hz : 0 < z.re)
    (hzS : |z.im| ≤ z.re / 2) :
    colAlpha2 (M₀.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun i => (u i : ℂ)) (fun i => (v i : ℂ)) z =
      (h : ℂ) ^ 2 * ((fun i => (u i : ℂ)) ⬝ᵥ
        (colR (M.map (fun x : ℝ => (x : ℂ))) z *ᵥ (fun i => (u i : ℂ)))) ∧
    0 ≤ (colAlpha2 (M₀.map (fun x : ℝ => (x : ℂ))) (h : ℂ) (fun i => (u i : ℂ))
      (fun i => (v i : ℂ)) z).re := by
  let M0c := M₀.map (fun x : ℝ => (x : ℂ))
  let Mc := M.map (fun x : ℝ => (x : ℂ))
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  let hc : ℂ := (h : ℂ)
  obtain ⟨hL, hdel, -, -⟩ := lem_app_de_deletion_sector M₀ h u v M z hM hz hzS
  have hcol := lem_app_drift_column_field_i Mc M0c hc z uc vc hL hdel
  have hd := congrArg (fun w : Fin m → ℂ => uc ⬝ᵥ w) hcol
  simp only [dotProduct_smul, smul_eq_mul, dotProduct_sub] at hd
  have hU : uc ⬝ᵥ (colR M0c z *ᵥ uc) = colU M0c uc z := rfl
  have hC : uc ⬝ᵥ (colX M0c z *ᵥ vc) = colC M0c uc vc z := rfl
  rw [hU, hC] at hd
  have hid : colAlpha2 M0c hc uc vc z =
      hc ^ 2 * (uc ⬝ᵥ (colR Mc z *ᵥ uc)) := by
    unfold colAlpha1 colAlpha2 at hd
    unfold colAlpha2
    have hds : hc * (uc ⬝ᵥ (colR Mc z *ᵥ uc)) =
        hc * colU M0c uc z / colLambda M0c hc uc vc z := by
      calc
        _ = hc * (1 + hc * colC M0c uc vc z) / colLambda M0c hc uc vc z *
              colU M0c uc z -
            hc ^ 2 * colU M0c uc z / colLambda M0c hc uc vc z *
              colC M0c uc vc z := hd
        _ = _ := by ring
    calc
      hc ^ 2 * colU M0c uc z / colLambda M0c hc uc vc z =
          hc * (hc * colU M0c uc z / colLambda M0c hc uc vc z) := by ring
      _ = hc * (hc * (uc ⬝ᵥ (colR Mc z *ᵥ uc))) := by rw [hds]
      _ = _ := by ring
  have hMcReal : Mcᴴ = Mcᵀ := by
    ext i j
    simp [Mc, Matrix.conjTranspose_apply]
  obtain ⟨-, -, -, -, hdetM, -⟩ := eqn_app_dyn_sector M z hz hzS
  let y := colR Mc z *ᵥ uc
  have hy : (Mc * Mcᵀ + z • (1 : Matrix (Fin m) (Fin m) ℂ)) *ᵥ y = uc := by
    dsimp [y, colR]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdetM, Matrix.one_mulVec]
  have hG : (Mc * Mcᵀ).PosSemidef := by
    rw [← hMcReal]
    exact Matrix.posSemidef_self_mul_conjTranspose Mc
  have hpos := hG.re_dotProduct_nonneg y
  have hreal : 0 ≤ (star y ⬝ᵥ uc).re := by
    rw [← hy, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, smul_eq_mul, Complex.add_re, Complex.mul_re,
      pe15_self_dot y, Complex.ofReal_re, Complex.ofReal_im]
    simp only [mul_zero, sub_zero]
    exact add_nonneg hpos (mul_nonneg hz.le (sq_nonneg _))
  have hquad : 0 ≤ (uc ⬝ᵥ (colR Mc z *ᵥ uc)).re := by
    change 0 ≤ (uc ⬝ᵥ y).re
    have hcj : star y ⬝ᵥ uc = star (uc ⬝ᵥ y) := by
      simp [dotProduct, uc, mul_comm]
    rw [hcj] at hreal
    simpa using hreal
  refine ⟨hid, ?_⟩
  rw [hid, Complex.mul_re]
  have hhRe : (hc ^ 2).re = h ^ 2 := by
    dsimp [hc]
    simp [pow_two, Complex.mul_re]
  have hhIm : (hc ^ 2).im = 0 := by
    dsimp [hc]
    simp [pow_two, Complex.mul_im]
  rw [hhRe, hhIm, zero_mul, sub_zero]
  exact mul_nonneg (sq_nonneg h) hquad

/-! ## Pointwise coefficient bounds at complex `z` -/

private lemma pe15_elem (c x y : ℝ) (hc : 0 ≤ c) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    1 + c * (x * y) ≤ (1 + c) * (1 + x) * (1 + y) := by
  nlinarith [mul_nonneg hc hx, mul_nonneg hc hy, mul_nonneg hx hy,
    mul_nonneg (mul_nonneg hc hx) hy]

private lemma pe15_coeff_growth2 (k p q N t : ℝ) (hk : 0 ≤ k) (hq : 0 ≤ q)
    (hN : 0 ≤ N) (ht : 0 < t) :
    p ^ 2 * q ^ 2 * N / t * ((1 + k) * (1 + q) * (1 + N)) ^ 2 ≤
      4 * (1 + k) ^ 3 * p ^ 2 / t * (1 + q) ^ 4 * (1 + N) ^ 3 := by
  have ha : (1 + k) ^ 2 ≤ 4 * (1 + k) ^ 3 := by
    have hk1 : 1 ≤ 1 + k := by linarith
    have hc : 0 ≤ (1 + k) ^ 3 := pow_nonneg (by linarith) 3
    calc
      (1 + k) ^ 2 = (1 + k) ^ 2 * 1 := by ring
      _ ≤ (1 + k) ^ 2 * (1 + k) :=
        mul_le_mul_of_nonneg_left hk1 (sq_nonneg (1 + k))
      _ = (1 + k) ^ 3 := by ring
      _ = 1 * (1 + k) ^ 3 := by ring
      _ ≤ 4 * (1 + k) ^ 3 := mul_le_mul_of_nonneg_right (by norm_num) hc
  have hqle : q ≤ 1 + q := le_add_of_nonneg_left (by norm_num)
  have hq2 : q ^ 2 ≤ (1 + q) ^ 2 := pow_le_pow_left₀ hq hqle 2
  have hN1 : N ≤ 1 + N := le_add_of_nonneg_left (by norm_num)
  have hi : q ^ 2 * N * (1 + k) ^ 2 ≤
      (1 + q) ^ 2 * (1 + N) * (4 * (1 + k) ^ 3) := by
    calc
      q ^ 2 * N * (1 + k) ^ 2 ≤ (1 + q) ^ 2 * N * (1 + k) ^ 2 := by gcongr
      _ ≤ (1 + q) ^ 2 * (1 + N) * (1 + k) ^ 2 := by gcongr
      _ ≤ (1 + q) ^ 2 * (1 + N) * (4 * (1 + k) ^ 3) := by gcongr
  let B := p ^ 2 / t * (1 + q) ^ 2 * (1 + N) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    p ^ 2 * q ^ 2 * N / t * ((1 + k) * (1 + q) * (1 + N)) ^ 2 =
        B * (q ^ 2 * N * (1 + k) ^ 2) := by dsimp [B]; ring
    _ ≤ B * ((1 + q) ^ 2 * (1 + N) * (4 * (1 + k) ^ 3)) :=
      mul_le_mul_of_nonneg_left hi hB
    _ = 4 * (1 + k) ^ 3 * p ^ 2 / t * (1 + q) ^ 4 * (1 + N) ^ 3 := by
      dsimp [B]
      ring

private lemma pe15_coeff_growth3 (k p q N : ℝ) (hk : 0 ≤ k) (hq : 0 ≤ q)
    (hN : 0 ≤ N) :
    (3 / 2 : ℝ) * p ^ 2 * q ^ 2 * N * ((1 + k) * (1 + q) * (1 + N)) ^ 2 ≤
      4 * (1 + k) ^ 3 * p ^ 2 * (1 + q) ^ 4 * (1 + N) ^ 3 := by
  have ha : (3 / 2 : ℝ) * (1 + k) ^ 2 ≤ 4 * (1 + k) ^ 3 := by
    have hk1 : 1 ≤ 1 + k := by linarith
    have hs : 0 ≤ (1 + k) ^ 2 := sq_nonneg _
    have hm := mul_le_mul_of_nonneg_left hk1 hs
    nlinarith
  have hqle : q ≤ 1 + q := le_add_of_nonneg_left (by norm_num)
  have hq2 : q ^ 2 ≤ (1 + q) ^ 2 := pow_le_pow_left₀ hq hqle 2
  have hN1 : N ≤ 1 + N := le_add_of_nonneg_left (by norm_num)
  have hi : (3 / 2 : ℝ) * (1 + k) ^ 2 * q ^ 2 * N ≤
      (4 * (1 + k) ^ 3) * (1 + q) ^ 2 * (1 + N) := by
    calc
      (3 / 2 : ℝ) * (1 + k) ^ 2 * q ^ 2 * N ≤
          (4 * (1 + k) ^ 3) * q ^ 2 * N := by gcongr
      _ ≤ (4 * (1 + k) ^ 3) * (1 + q) ^ 2 * N := by gcongr
      _ ≤ (4 * (1 + k) ^ 3) * (1 + q) ^ 2 * (1 + N) := by gcongr
  let B := p ^ 2 * (1 + q) ^ 2 * (1 + N) ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  calc
    (3 / 2 : ℝ) * p ^ 2 * q ^ 2 * N * ((1 + k) * (1 + q) * (1 + N)) ^ 2 =
        B * ((3 / 2 : ℝ) * (1 + k) ^ 2 * q ^ 2 * N) := by dsimp [B]; ring
    _ ≤ B * ((4 * (1 + k) ^ 3) * (1 + q) ^ 2 * (1 + N)) :=
      mul_le_mul_of_nonneg_left hi hB
    _ = 4 * (1 + k) ^ 3 * p ^ 2 * (1 + q) ^ 4 * (1 + N) ^ 3 := by
      dsimp [B]
      ring

/-- Pointwise coefficient bounds at `z ∈ 𝕊`, snapshot `cr-2026-10-23` (`sections/05-dynamics/section.tex`
ll. 841–852, first display of "the coefficient moments"; `𝗁 = ϖ d`, `0 ≤ ϖ ≤ 1`):
```latex
\emph{(i), the coefficient moments.} With $\mathsf h=\varpi d$, the bounds
\cref{eqn:app-dyn-sector,eqn:app-dyn-sector-inverse} and
\cref{eqn:app-de-elementary} give, as in the proof of
\cref{lem:app-drift-coeffmoments},
\[
\abs{\alpha_1}\le c_x\varpi\,\mathsf Z,\qquad
\abs{\alpha_2}\le\frac{c_x\varpi^2}{x}\,\mathsf Z,\qquad
\abs{\alpha_3}\le c_x\varpi^2\,\mathsf Z,\qquad
\mathsf Z\defeq(1+\abs d)^4(1+\mathsf N)^3,
\]
with $c_x$ bounded on compacts of $x$ and uniformly for $x\ge1$, where
$x^{-1/2}\le1$.
```
Encoding: for each `s0 > 0` one constant `c` serves every `z ∈ 𝕊` with `Re z ≥ s0`; this is
equivalent to the source's "bounded on compacts of `x` and uniformly for `x ≥ 1`". `c` is chosen
before all data. Real counterparts: `Muon.DetEquiv.lem_app_de_coeff` (`Resolvent.lean`:882; compact
`I`, `α₂` without the `1/x`) and the pointwise `α₂` bound in the proof of
`Muon.Drift.lem_app_drift_coeffmoments`. -/
theorem lem_app_de_coeff_sector (s0 : ℝ) (hs0 : 0 < s0) :
    ∃ c : ℝ, ∀ {m n : ℕ} (M₀ : Mat m n) (u : Vec m) (v : Vec n) (d ϖ : ℝ) (z : ℂ),
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ z.re → |z.im| ≤ z.re / 2 →
      ‖colAlpha1 (M₀.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
          (fun i => (v i : ℂ)) z‖ ≤
        c * ϖ * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 ∧
      ‖colAlpha2 (M₀.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
          (fun i => (v i : ℂ)) z‖ ≤
        c * ϖ ^ 2 / z.re * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 ∧
      ‖colAlpha3 (M₀.map (fun x : ℝ => (x : ℂ))) ((ϖ * d : ℝ) : ℂ) (fun i => (u i : ℂ))
          (fun i => (v i : ℂ)) z‖ ≤
        c * ϖ ^ 2 * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by
  let k := 1 / Real.sqrt s0
  refine ⟨4 * (1 + k) ^ 3, ?_⟩
  intro m n M₀ u v d ϖ z hϖ0 hϖ1 hzs hzS
  have hz : 0 < z.re := lt_of_lt_of_le hs0 hzs
  let M := M₀ + (ϖ * d) • outer u v
  let M0c := M₀.map (fun x : ℝ => (x : ℂ))
  let uc : Fin m → ℂ := fun i => (u i : ℂ)
  let vc : Fin n → ℂ := fun i => (v i : ℂ)
  let hc : ℂ := ((ϖ * d : ℝ) : ℂ)
  have hM : M = M₀ + (ϖ * d) • outer u v := rfl
  obtain ⟨-, hInv⟩ := eqn_app_dyn_sector_inverse M₀ (ϖ * d) u v M z hM hz hzS
  obtain ⟨hR, hRt, hX, -, -, -⟩ := eqn_app_dyn_sector M₀ z hz hzS
  rw [rres_neg_eq_colR] at hR
  rw [rtil_neg_eq_colRt] at hRt
  rw [rres_neg_eq_colR] at hX
  have hU : ‖colU M0c uc z‖ ≤ sqNorm u / z.re :=
    pe15_quad_scalar_bound (colR M0c z) u z.re hz hR
  have hV : ‖colV M0c vc z‖ ≤ sqNorm v / z.re :=
    pe15_quad_scalar_bound (colRt M0c z) v z.re hz hRt
  have hC : ‖colC M0c uc vc z‖ ≤
      (sqNorm u + sqNorm v) / (4 * Real.sqrt z.re) :=
    pe15_cross_scalar_bound (colX M0c z) u v z.re hz hX
  have hNu : 0 ≤ sqNorm u := by unfold sqNorm; positivity
  have hNv : 0 ≤ sqNorm v := by unfold sqNorm; positivity
  have hN : 0 ≤ sqNorm u + sqNorm v := add_nonneg hNu hNv
  have hk0 : 0 ≤ k := by dsimp [k]; positivity
  have hsroot : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hsqrtle : Real.sqrt s0 ≤ Real.sqrt z.re := Real.sqrt_le_sqrt hzs
  have hk : 1 / Real.sqrt z.re ≤ k := by
    dsimp [k]
    exact one_div_le_one_div_of_le hsroot hsqrtle
  have hhc : ‖hc‖ = ϖ * |d| := by
    simp [hc, abs_mul, abs_of_nonneg hϖ0]
  have hhd : ϖ * |d| ≤ |d| := mul_le_of_le_one_left (abs_nonneg d) hϖ1
  let N := sqNorm u + sqNorm v
  let R := (1 + k) * (1 + |d|) * (1 + N)
  have hR0 : 0 ≤ R := by dsimp [R, N]; positivity
  have hfac : 1 + ‖hc‖ * N / Real.sqrt z.re ≤ R := by
    rw [hhc]
    have hkn : 1 / Real.sqrt z.re * (ϖ * |d| * N) ≤ k * (|d| * N) := by
      gcongr
    have he : ϖ * |d| * N / Real.sqrt z.re =
        1 / Real.sqrt z.re * (ϖ * |d| * N) := by ring
    rw [he]
    calc
      1 + 1 / Real.sqrt z.re * (ϖ * |d| * N) ≤ 1 + k * (|d| * N) := by linarith
      _ ≤ R := by
        dsimp [R]
        exact pe15_elem k |d| N hk0 (abs_nonneg d) hN
  have hfacC : 1 + ‖hc‖ * ‖colC M0c uc vc z‖ ≤ R := by
    calc
      _ ≤ 1 + ‖hc‖ * (N / (4 * Real.sqrt z.re)) := by gcongr
      _ ≤ 1 + ‖hc‖ * N / Real.sqrt z.re := by
        have hs : 0 < Real.sqrt z.re := Real.sqrt_pos.mpr hz
        have : N / (4 * Real.sqrt z.re) ≤ N / Real.sqrt z.re := by
          gcongr <;> nlinarith
        simpa [add_comm, mul_div_assoc] using
          add_le_add_left (mul_le_mul_of_nonneg_left this (norm_nonneg hc)) 1
      _ ≤ R := hfac
  have hInvR : ‖colLambda M0c hc uc vc z‖⁻¹ ≤ R ^ 2 := by
    calc
      _ ≤ (1 + ‖hc‖ * N / Real.sqrt z.re) ^ 2 := by
        simpa [M0c, uc, vc, hc, N, Real.norm_eq_abs] using hInv
      _ ≤ R ^ 2 := pow_le_pow_left₀ (by positivity) hfac 2
  have hA1 : ‖colAlpha1 M0c hc uc vc z‖ ≤ ‖hc‖ * R ^ 3 := by
    unfold colAlpha1
    rw [norm_div, norm_mul]
    calc
      ‖hc‖ * ‖1 + hc * colC M0c uc vc z‖ * ‖colLambda M0c hc uc vc z‖⁻¹
          ≤ ‖hc‖ * (1 + ‖hc‖ * ‖colC M0c uc vc z‖) *
              ‖colLambda M0c hc uc vc z‖⁻¹ := by
            gcongr
            exact (norm_add_le _ _).trans_eq (by simp [norm_mul])
      _ ≤ ‖hc‖ * R * R ^ 2 := by gcongr
      _ = ‖hc‖ * R ^ 3 := by ring
  have hA2 : ‖colAlpha2 M0c hc uc vc z‖ ≤ ϖ ^ 2 * |d| ^ 2 * N / z.re * R ^ 2 := by
    unfold colAlpha2
    rw [norm_div, norm_mul, norm_pow, hhc]
    calc
      (ϖ * |d|) ^ 2 * ‖colU M0c uc z‖ * ‖colLambda M0c hc uc vc z‖⁻¹
          ≤ (ϖ * |d|) ^ 2 * (sqNorm u / z.re) * R ^ 2 := by gcongr
      _ = ϖ ^ 2 * |d| ^ 2 * (sqNorm u / z.re) * R ^ 2 := by ring
      _ ≤ ϖ ^ 2 * |d| ^ 2 * (N / z.re) * R ^ 2 := by
        have huN : sqNorm u ≤ N := by dsimp [N]; linarith
        gcongr
      _ = _ := by ring
  have hzN := (eqn_app_dyn_sector M₀ z hz hzS).2.2.2.1
  have hzlin : ‖z‖ ≤ (3 / 2 : ℝ) * z.re := by
    have hs5 : Real.sqrt 5 ≤ 3 := by
      rw [Real.sqrt_le_iff]
      norm_num
    calc
      ‖z‖ ≤ Real.sqrt 5 / 2 * z.re := (div_le_iff₀ hz).mp hzN
      _ ≤ (3 / 2 : ℝ) * z.re := by gcongr
  have hA3 : ‖colAlpha3 M0c hc uc vc z‖ ≤
      (3 / 2 : ℝ) * ϖ ^ 2 * |d| ^ 2 * N * R ^ 2 := by
    unfold colAlpha3
    rw [norm_div, norm_neg, norm_mul, norm_mul, norm_pow, hhc]
    calc
      ‖z‖ * (ϖ * |d|) ^ 2 * ‖colV M0c vc z‖ *
          ‖colLambda M0c hc uc vc z‖⁻¹
        ≤ ((3 / 2 : ℝ) * z.re) * (ϖ * |d|) ^ 2 *
            (sqNorm v / z.re) * R ^ 2 := by gcongr
      _ = (3 / 2 : ℝ) * ϖ ^ 2 * |d| ^ 2 * sqNorm v * R ^ 2 := by
        field_simp
      _ ≤ (3 / 2 : ℝ) * ϖ ^ 2 * |d| ^ 2 * N * R ^ 2 := by
        have hvN : sqNorm v ≤ N := by dsimp [N]; linarith
        gcongr
  have hfin1 : ‖hc‖ * R ^ 3 ≤
      4 * (1 + k) ^ 3 * ϖ * (1 + |d|) ^ 4 * (1 + N) ^ 3 := by
    rw [hhc]
    dsimp [R]
    let T := (1 + k) ^ 3 * ϖ * (1 + |d|) ^ 3 * (1 + N) ^ 3
    have hT : 0 ≤ T := by dsimp [T]; positivity
    have hd4 : |d| ≤ 4 * (1 + |d|) := by
      calc
        |d| ≤ 1 + |d| := le_add_of_nonneg_left (by norm_num)
        _ = 1 * (1 + |d|) := by ring
        _ ≤ 4 * (1 + |d|) :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc
      ϖ * |d| * ((1 + k) * (1 + |d|) * (1 + N)) ^ 3 = T * |d| := by
        dsimp [T]
        ring
      _ ≤ T * (4 * (1 + |d|)) := mul_le_mul_of_nonneg_left hd4 hT
      _ = 4 * (1 + k) ^ 3 * ϖ * (1 + |d|) ^ 4 * (1 + N) ^ 3 := by
        dsimp [T]
        ring
  have hfin2 : ϖ ^ 2 * |d| ^ 2 * N / z.re * R ^ 2 ≤
      4 * (1 + k) ^ 3 * ϖ ^ 2 / z.re * (1 + |d|) ^ 4 * (1 + N) ^ 3 := by
    dsimp [R]
    exact pe15_coeff_growth2 k ϖ |d| N z.re hk0 (abs_nonneg d) hN hz
  have hfin3 : (3 / 2 : ℝ) * ϖ ^ 2 * |d| ^ 2 * N * R ^ 2 ≤
      4 * (1 + k) ^ 3 * ϖ ^ 2 * (1 + |d|) ^ 4 * (1 + N) ^ 3 := by
    dsimp [R]
    exact pe15_coeff_growth3 k ϖ |d| N hk0 (abs_nonneg d) hN
  exact ⟨hA1.trans (by simpa [M0c, uc, vc, hc, N, k] using hfin1),
    hA2.trans (by simpa [M0c, uc, vc, hc, N, k] using hfin2),
    hA3.trans (by simpa [M0c, uc, vc, hc, N, k] using hfin3)⟩

/-! ## The inverse of `𝖸_B` -/

private lemma pe15_psd_re {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (x : Fin n → ℂ) :
    0 ≤ (star x ⬝ᵥ (S.map Complex.ofReal *ᵥ x)).re := by
  have ha := hS.dotProduct_mulVec_nonneg (fun i => (x i).re)
  have hb := hS.dotProduct_mulVec_nonneg (fun i => (x i).im)
  simp only [star_trivial] at ha hb
  simp only [dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum]
  change 0 ≤ Complex.reCLM (∑ i, ∑ j, star (x i) * (↑(S i j) * x j))
  simp only [map_sum, Complex.reCLM_apply, Complex.mul_re, Complex.star_def,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.mul_im, neg_mul, zero_mul]
  simpa [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_add_distrib] using
    add_nonneg ha hb

private lemma pe15_euc_ofLp {n : ℕ} (x : Fin n → ℂ) :
    ((EuclideanSpace.equiv (Fin n) ℂ).symm x).ofLp = x :=
  ContinuousLinearEquiv.apply_symm_apply (EuclideanSpace.equiv (Fin n) ℂ) x

private lemma pe15_norm_add_smul_sq {n : ℕ} (x g : Fin n → ℂ) (b : ℂ) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (x + b • g)‖ ^ 2 =
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm x‖ ^ 2 +
        2 * (b * (star x ⬝ᵥ g)).re +
          ‖b‖ ^ 2 * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm g‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [pe15_euc_ofLp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dotProduct, Finset.mul_sum]
  change (∑ i, ‖x i + b * g i‖ ^ 2) =
    (∑ i, ‖x i‖ ^ 2) + 2 * (∑ i, b * (star (x i) * g i)).re +
      ∑ i, ‖b‖ ^ 2 * ‖g i‖ ^ 2
  change (∑ i, ‖x i + b * g i‖ ^ 2) =
    (∑ i, ‖x i‖ ^ 2) + 2 * Complex.reCLM (∑ i, b * (star (x i) * g i)) +
      ∑ i, ‖b‖ ^ 2 * ‖g i‖ ^ 2
  simp only [map_sum, Complex.reCLM_apply, Complex.sq_norm, Complex.normSq_apply,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.star_def,
    Complex.conj_re, Complex.conj_im]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private lemma pe15_psd_expansive {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.PosSemidef) (b : ℂ) (hb : 0 ≤ b.re) (x : Fin n → ℂ) :
    ‖(EuclideanSpace.equiv (Fin n) ℂ).symm x‖ ≤
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm
        (x + b • (S.map Complex.ofReal *ᵥ x))‖ := by
  let g := S.map Complex.ofReal *ᵥ x
  have hp := pe15_psd_re S hS x
  have hp' : 0 ≤ (star x ⬝ᵥ g).re := by simpa [g] using hp
  have him : (star x ⬝ᵥ g).im = 0 := by
    have hSc : (S.map Complex.ofReal).IsHermitian :=
      hS.isHermitian.map Complex.ofReal (fun r => by simp)
    simpa [g] using hSc.im_star_dotProduct_mulVec_self x
  have he := pe15_norm_add_smul_sq x g b
  have hs : ‖(EuclideanSpace.equiv (Fin n) ℂ).symm x‖ ^ 2 ≤
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (x + b • g)‖ ^ 2 := by
    rw [he]
    rw [Complex.mul_re, him, mul_zero, sub_zero]
    have hcross : 0 ≤ 2 * b.re * (star x ⬝ᵥ g).re := by positivity
    have hlast : 0 ≤ ‖b‖ ^ 2 * ‖(EuclideanSpace.equiv (Fin n) ℂ).symm g‖ ^ 2 := by
      positivity
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hs

private lemma pe15_fro_nonneg {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) : 0 ≤ fro A :=
  Real.sqrt_nonneg _

private lemma pe15_fro_sq {a b : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) :
    fro A ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]

/-- `‖𝖸_B⁻¹‖ ≤ 1` in the form used by the assembly of `lem:app-dyn-mean`(i), snapshot
`cr-2026-10-23` (`sections/05-dynamics/section.tex` ll. 889–893): for `𝖸 = Id + b Σ` with `Σ`
real PSD and `Re b ≥ 0`,
```latex
By \cref{eqn:app-dyn-Rebeta}, $\Ree b_B\ge0$. The matrix $\mathsf Y_B$ is
diagonal in the eigenbasis of $\Sigmain$ with eigenvalues $1+b_B\lambda_j$,
and $\abs{1+b_B\lambda_j}\ge\Ree(1+b_B\lambda_j)\ge1$, so
$\norm{\mathsf Y_B^{-1}}\le1$ and $\norm{\mathcal H(z)}_\F\le\norm{E_0(z)}_\F\le C/x$.
```
Stated as the two consequences used, `‖H‖_F ≤ ‖H𝖸‖_F` and `‖H‖ ≤ ‖H𝖸‖`, with
`H𝖸 = H + b (HΣ)`. Real counterpart (Frobenius only, `b ≥ 0` real): `Muon.Drift.tl_fro_Y`
(`Tail.lean`:1745). The operator-norm clause at real `b ≥ 0` is the step `‖𝖸_B(s)⁻¹‖ ≤ 1` of (iv)
(ll. 959–961). -/
theorem fro_opNorm_le_add_smul_mul_psd {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℂ)
    (S : Mat n n) (hS : S.PosSemidef) (b : ℂ) (hb : 0 ≤ b.re) :
    fro H ≤ fro (H + b • (H * S.map (fun x : ℝ => (x : ℂ)))) ∧
    opNorm H ≤ opNorm (H + b • (H * S.map (fun x : ℝ => (x : ℂ)))) := by
  let Sc : Matrix (Fin n) (Fin n) ℂ := S.map Complex.ofReal
  let Y : Matrix (Fin n) (Fin n) ℂ := 1 + b • Sc
  have hsym : Sᵀ = S := by
    have ht := hS.isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at ht
    exact ht
  have hScsym : Scᵀ = Sc := by
    ext i j
    simp only [Sc, Matrix.transpose_apply, Matrix.map_apply]
    rw [show S j i = S i j by
      have ht := congrFun (congrFun hsym i) j
      simpa only [Matrix.transpose_apply] using ht]
  have hexp (x : Fin n → ℂ) :
      ‖(EuclideanSpace.equiv (Fin n) ℂ).symm x‖ ≤
        ‖(EuclideanSpace.equiv (Fin n) ℂ).symm (Y *ᵥ x)‖ := by
    simpa [Y, Sc, Matrix.add_mulVec, Matrix.smul_mulVec] using
      pe15_psd_expansive S hS b hb x
  have hYinj : Function.Injective Y.mulVec := by
    intro x y hxy
    have hz : Y *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hn := hexp (x - y)
    rw [hz] at hn
    simp only [map_zero, norm_zero] at hn
    have he : (EuclideanSpace.equiv (Fin n) ℂ).symm (x - y) = 0 :=
      norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
    have hv : x - y = 0 := by
      apply (EuclideanSpace.equiv (Fin n) ℂ).symm.injective
      simpa using he
    exact sub_eq_zero.mp hv
  have hYunit : IsUnit Y := Matrix.mulVec_injective_iff_isUnit.mp hYinj
  have hYdet : IsUnit Y.det := (Matrix.isUnit_iff_isUnit_det Y).mp hYunit
  have hinv : opNorm Y⁻¹ ≤ 1 := by
    refine pe15_opNorm_le (A := Y⁻¹) (c := 1) (by norm_num) ?_
    intro x
    have he := hexp (Y⁻¹ *ᵥ x)
    have hmul : Y *ᵥ (Y⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv Y hYdet, Matrix.one_mulVec]
    simpa [hmul] using he
  have hHY : H * Y = H + b • (H * Sc) := by
    simp [Y, Matrix.mul_add, Matrix.mul_smul]
  constructor
  · have hrow : ∀ i : Fin m, ∑ k, ‖H i k‖ ^ 2 ≤
        ∑ k, ‖(H + b • (H * Sc)) i k‖ ^ 2 := by
      intro i
      let h : Fin n → ℂ := fun k => H i k
      let g : Fin n → ℂ := Sc *ᵥ h
      have hent : ∀ k, (H + b • (H * Sc)) i k = h k + b * g k := by
        intro k
        have hm : (H * Sc) i k = g k := by
          simp only [Matrix.mul_apply, g, Matrix.mulVec, dotProduct, h]
          refine Finset.sum_congr rfl fun l _ => ?_
          have ht := congrFun (congrFun hScsym k) l
          simp only [Matrix.transpose_apply] at ht
          rw [← ht]
          ring
        simp [hm, h]
      have hn := pe15_psd_expansive S hS b hb h
      have hs := (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mpr hn
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
      simp only [pe15_euc_ofLp] at hs
      change @LE.le ℝ Real.linearOrder.toLE (∑ k, ‖H i k‖ ^ 2)
        (∑ k, ‖(H + b • (H * Sc)) i k‖ ^ 2)
      simpa only [hent, h, g, Sc, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hs
    have hsq : fro H ^ 2 ≤ fro (H + b • (H * Sc)) ^ 2 := by
      rw [pe15_fro_sq, pe15_fro_sq]
      exact Finset.sum_le_sum fun i _ => hrow i
    simpa [Sc] using
      (pow_le_pow_iff_left₀ (pe15_fro_nonneg H)
        (pe15_fro_nonneg (H + b • (H * Sc))) two_ne_zero).mp hsq
  · have hmul : opNorm ((H * Y) * Y⁻¹) ≤ opNorm (H * Y) * opNorm Y⁻¹ := by
      rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
      exact Matrix.l2_opNorm_mul (H * Y) Y⁻¹
    have hcancel : (H * Y) * Y⁻¹ = H := by
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv Y hYdet, Matrix.mul_one]
    rw [hcancel] at hmul
    calc
      opNorm H ≤ opNorm (H * Y) * opNorm Y⁻¹ := hmul
      _ ≤ opNorm (H * Y) * 1 :=
        mul_le_mul_of_nonneg_left hinv (by unfold opNorm; positivity)
      _ = opNorm (H + b • (H * S.map (fun x : ℝ => (x : ℂ)))) := by
        rw [mul_one, hHY]

end Muon.Dynamics

end
