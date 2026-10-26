import Muon.DetEquiv.Resolvent

/-!
# Muon.Drift: deletion identities for the mixed resolvent (work package L-C.2)

Interface of `lem:app-drift-column` (`sections/03-drift/section.tex` l.228–236), snapshot
`cr-2026-10-23`. Pure finite-dimensional algebra.

Declaration of record: `Muon.Drift.lem_app_drift_column`, over `ℝ` with `0 < s`, both parts as a
conjunction, using B's real objects (`Muon.DetEquiv.Rs`, `Xs`, `Rts`, `alpha1..3`,
`Resolvent.lean`).

Field-generic forms: `lem_app_drift_column_field_i` and `_field_ii` state the source over a general
field `K` with a spectral parameter `s : K`, per `CARD.md` §5(d), so that E (`05-dynamics`)
instantiates it at complex `s := z` without duplication. The real specialization is
`Muon.DetEquiv.lem_app_de_deletion` (B, `Resolvent.lean`), which supplies the hypothesis `hdel`
below (`eqn:app-de-deletion-R`) and gives `Λ > 0` for `s > 0`. Over `K` the resolvents are the
inverses `(MMᵀ + s·1)⁻¹` and `(MᵀM + s·1)⁻¹` of `Matrix`, so every identity needing an inverse
carries an explicit `IsUnit (det _)` hypothesis; without it `Matrix.inv` returns junk. The scalar
`Λ` of `eqn:app-de-UVC` is the denominator of the α's, so it carries `Λ ≠ 0`.

The `col*` objects are field-generic counterparts of B's `Rs`, `Xs`, `delU`, `delV`, `delC`,
`delLambda`, `alpha1..3` (which are fixed to `ℝ`); no project object of the same type is duplicated.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open scoped Matrix MatrixOrder
open Matrix

noncomputable section

namespace Muon.Drift

variable {K : Type*} [Field K] {m n : ℕ}

/-- Private helper: a rank-one matrix acting on a vector. -/
private lemma vecMulVec_mulVec_eq' (a : Fin m → K) (b c : Fin n → K) :
    vecMulVec a b *ᵥ c = (b ⬝ᵥ c) • a := by
  ext i
  simp only [mulVec, dotProduct, vecMulVec, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Output resolvent `R_s(M) = (MMᵀ + s Id)⁻¹` over a field (`eqn:app-de-RXdef`). -/
def colR (M : Matrix (Fin m) (Fin n) K) (s : K) : Matrix (Fin m) (Fin m) K :=
  (M * Mᵀ + s • (1 : Matrix (Fin m) (Fin m) K))⁻¹

/-- Input resolvent `R̃_s(M) = (MᵀM + s Id)⁻¹` over a field (`eqn:app-de-RXdef`). -/
def colRt (M : Matrix (Fin m) (Fin n) K) (s : K) : Matrix (Fin n) (Fin n) K :=
  (Mᵀ * M + s • (1 : Matrix (Fin n) (Fin n) K))⁻¹

/-- Mixed resolvent `𝖷_s(M) = R_s(M) M` over a field (`eqn:app-de-RXdef`). -/
def colX (M : Matrix (Fin m) (Fin n) K) (s : K) : Matrix (Fin m) (Fin n) K :=
  colR M s * M

/-- `𝖴 = uᵀ R_s(M₀) u` (`eqn:app-de-UVC`). -/
def colU (M₀ : Matrix (Fin m) (Fin n) K) (u : Fin m → K) (s : K) : K :=
  dotProduct u (colR M₀ s *ᵥ u)

/-- `𝖵 = vᵀ R̃_s(M₀) v` (`eqn:app-de-UVC`). -/
def colV (M₀ : Matrix (Fin m) (Fin n) K) (v : Fin n → K) (s : K) : K :=
  dotProduct v (colRt M₀ s *ᵥ v)

/-- `𝖢 = uᵀ 𝖷_s(M₀) v` (`eqn:app-de-UVC`). -/
def colC (M₀ : Matrix (Fin m) (Fin n) K) (u : Fin m → K) (v : Fin n → K) (s : K) : K :=
  dotProduct u (colX M₀ s *ᵥ v)

/-- `Λ = (1 + 𝗁𝖢)² + s 𝗁² 𝖴𝖵` (`eqn:app-de-UVC`). -/
def colLambda (M₀ : Matrix (Fin m) (Fin n) K) (h : K) (u : Fin m → K) (v : Fin n → K) (s : K) : K :=
  (1 + h * colC M₀ u v s) ^ 2 + s * h ^ 2 * colU M₀ u s * colV M₀ v s

/-- `α₁ = 𝗁(1 + 𝗁𝖢)/Λ` (`eqn:app-de-coefficients`). -/
def colAlpha1 (M₀ : Matrix (Fin m) (Fin n) K) (h : K) (u : Fin m → K) (v : Fin n → K) (s : K) : K :=
  h * (1 + h * colC M₀ u v s) / colLambda M₀ h u v s

/-- `α₂ = 𝗁² 𝖴/Λ` (`eqn:app-de-coefficients`). -/
def colAlpha2 (M₀ : Matrix (Fin m) (Fin n) K) (h : K) (u : Fin m → K) (v : Fin n → K) (s : K) : K :=
  h ^ 2 * colU M₀ u s / colLambda M₀ h u v s

/-- `α₃ = -s 𝗁² 𝖵/Λ` (`eqn:app-de-coefficients`). -/
def colAlpha3 (M₀ : Matrix (Fin m) (Fin n) K) (h : K) (u : Fin m → K) (v : Fin n → K) (s : K) : K :=
  -(s * h ^ 2 * colV M₀ v s) / colLambda M₀ h u v s

/-- Private helper: `colR` is symmetric. -/
private lemma colR_transpose' (M : Matrix (Fin m) (Fin n) K) (s : K) :
    (colR M s)ᵀ = colR M s := by
  unfold colR
  rw [Matrix.transpose_nonsing_inv]
  congr 1
  simp [Matrix.transpose_add, Matrix.transpose_mul]

/-- Private helper: `M₀ᵀ R₀ M₀ = Id − s R̃₀` (push-through identity). -/
private lemma colR_sandwich (M₀ : Matrix (Fin m) (Fin n) K) (s : K)
    (hR₀ : IsUnit (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) K)).det)
    (hRt₀ : IsUnit (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) K)).det) :
    M₀ᵀ * colR M₀ s * M₀ = 1 - s • colRt M₀ s := by
  unfold colR colRt
  have key : M₀ᵀ * (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) K))
      = (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) K)) * M₀ᵀ := by
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_smul,
      Matrix.smul_mul,
      Matrix.mul_one, Matrix.one_mul]
  set A := M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) K) with hAdef
  set B := M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) K) with hBdef
  have hcomm : M₀ᵀ * A⁻¹ = B⁻¹ * M₀ᵀ := by
    calc M₀ᵀ * A⁻¹ = (B⁻¹ * B) * (M₀ᵀ * A⁻¹) := by
          rw [Matrix.nonsing_inv_mul _ hRt₀, Matrix.one_mul]
      _ = B⁻¹ * ((B * M₀ᵀ) * A⁻¹) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * ((M₀ᵀ * A) * A⁻¹) := by rw [key]
      _ = B⁻¹ * (M₀ᵀ * (A * A⁻¹)) := by simp only [Matrix.mul_assoc]
      _ = B⁻¹ * M₀ᵀ := by rw [Matrix.mul_nonsing_inv _ hR₀, Matrix.mul_one]
  have hMB : M₀ᵀ * M₀ = B - s • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [hBdef, add_sub_cancel_right]
  calc M₀ᵀ * A⁻¹ * M₀ = B⁻¹ * (M₀ᵀ * M₀) := by rw [hcomm, Matrix.mul_assoc]
    _ = B⁻¹ * (B - s • (1 : Matrix (Fin n) (Fin n) K)) := by rw [hMB]
    _ = 1 - s • B⁻¹ := by
          rw [mul_sub, Matrix.nonsing_inv_mul _ hRt₀, Matrix.mul_smul, Matrix.mul_one]

/-- lem:app-drift-column. Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.228–236, verbatim).
Part (i) is `eqn:app-drift-column`.

\begin{lemma}[Deletion identities for the mixed resolvent]\label{lem:app-drift-column}
In the setting of \cref{lem:app-de-deletion}, with $\mathsf X\defeq\mathsf X_s(M)$,
\begin{align}
\mathsf h\,R\mathsf u&=\alpha_1\,R_0\mathsf u-\alpha_2\,\mathsf X_0\mathsf v ,\label{eqn:app-drift-column}\\
\mathsf X-\mathsf X_0&=\alpha_3\,R_0(\mathsf u\tensor\mathsf u)\mathsf X_0+s\,\alpha_1\,R_0(\mathsf u\tensor\mathsf v)\widetilde R_0
-\alpha_1\,\mathsf X_0(\mathsf v\tensor\mathsf u)\mathsf X_0-s\,\alpha_2\,\mathsf X_0(\mathsf v\tensor\mathsf v)\widetilde R_0 .
\label{eqn:app-drift-Xdiff}
\end{align}
\end{lemma}

Field-generic form of part (i). `hdel` is the rank-two deletion identity `eqn:app-de-deletion-R`
of the setting (`Muon.DetEquiv.lem_app_de_deletion`). -/
theorem lem_app_drift_column_field_i
    (M M₀ : Matrix (Fin m) (Fin n) K) (h s : K) (u : Fin m → K) (v : Fin n → K)
    (hΛ : colLambda M₀ h u v s ≠ 0)
    (hdel : colR M s - colR M₀ s =
      colAlpha3 M₀ h u v s • vecMulVec (colR M₀ s *ᵥ u) (colR M₀ s *ᵥ u)
        - colAlpha1 M₀ h u v s • vecMulVec (colR M₀ s *ᵥ u) (colX M₀ s *ᵥ v)
        - colAlpha1 M₀ h u v s • vecMulVec (colX M₀ s *ᵥ v) (colR M₀ s *ᵥ u)
        + colAlpha2 M₀ h u v s • vecMulVec (colX M₀ s *ᵥ v) (colX M₀ s *ᵥ v)) :
    h • (colR M s *ᵥ u) =
      colAlpha1 M₀ h u v s • (colR M₀ s *ᵥ u) - colAlpha2 M₀ h u v s • (colX M₀ s *ᵥ v) := by
  have hU : dotProduct (colR M₀ s *ᵥ u) u = colU M₀ u s := by
    unfold colU; exact dotProduct_comm _ _
  have hC : dotProduct (colX M₀ s *ᵥ v) u = colC M₀ u v s := by
    unfold colC; exact dotProduct_comm _ _
  have hd := congrArg (fun A : Matrix (Fin m) (Fin m) K => A *ᵥ u) hdel
  simp only [sub_mulVec, add_mulVec, smul_mulVec, vecMulVec_mulVec_eq', hU, hC] at hd
  have hR : colR M s *ᵥ u = colR M₀ s *ᵥ u
      + (colAlpha3 M₀ h u v s * colU M₀ u s - colAlpha1 M₀ h u v s * colC M₀ u v s)
          • (colR M₀ s *ᵥ u)
      + (colAlpha2 M₀ h u v s * colC M₀ u v s - colAlpha1 M₀ h u v s * colU M₀ u s)
          • (colX M₀ s *ᵥ v) := by
    linear_combination (norm := module) hd
  have S1 : h * (1 + colAlpha3 M₀ h u v s * colU M₀ u s - colAlpha1 M₀ h u v s * colC M₀ u v s)
      = colAlpha1 M₀ h u v s := by
    unfold colAlpha1 colAlpha3
    unfold colLambda at hΛ ⊢
    generalize hLg : (1 + h * colC M₀ u v s) ^ 2 + s * h ^ 2 * colU M₀ u s * colV M₀ v s = L
      at hΛ ⊢
    field_simp
    rw [← hLg]
    ring
  have S2 : h * (colAlpha2 M₀ h u v s * colC M₀ u v s - colAlpha1 M₀ h u v s * colU M₀ u s)
      = -colAlpha2 M₀ h u v s := by
    unfold colAlpha1 colAlpha2
    unfold colLambda at hΛ ⊢
    field_simp
    ring
  rw [hR]
  linear_combination (norm := module) S1 • (colR M₀ s *ᵥ u) + S2 • (colX M₀ s *ᵥ v)

/-- lem:app-drift-column. Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.228–236, verbatim).
Part (ii) is `eqn:app-drift-Xdiff`.

\begin{lemma}[Deletion identities for the mixed resolvent]\label{lem:app-drift-column}
In the setting of \cref{lem:app-de-deletion}, with $\mathsf X\defeq\mathsf X_s(M)$,
\begin{align}
\mathsf h\,R\mathsf u&=\alpha_1\,R_0\mathsf u-\alpha_2\,\mathsf X_0\mathsf v ,\label{eqn:app-drift-column}\\
\mathsf X-\mathsf X_0&=\alpha_3\,R_0(\mathsf u\tensor\mathsf u)\mathsf X_0+s\,\alpha_1\,R_0(\mathsf u\tensor\mathsf v)\widetilde R_0
-\alpha_1\,\mathsf X_0(\mathsf v\tensor\mathsf u)\mathsf X_0-s\,\alpha_2\,\mathsf X_0(\mathsf v\tensor\mathsf v)\widetilde R_0 .
\label{eqn:app-drift-Xdiff}
\end{align}
\end{lemma}

Field-generic form of part (ii), `𝖷 = 𝖷_s(M)`, `M = M₀ + 𝗁 𝗎⊗𝗏`. Hypotheses: `hdel` as in
part (i); `hR₀`, `hRt₀` invertibility of `M₀ M₀ᵀ + s` and `M₀ᵀ M₀ + s` (needed for
`M₀ᵀ R₀ M₀ = Id − s R̃₀`). -/
theorem lem_app_drift_column_field_ii
    (M M₀ : Matrix (Fin m) (Fin n) K) (h s : K) (u : Fin m → K) (v : Fin n → K)
    (hM : M = M₀ + h • vecMulVec u v)
    (hR₀ : IsUnit (M₀ * M₀ᵀ + s • (1 : Matrix (Fin m) (Fin m) K)).det)
    (hRt₀ : IsUnit (M₀ᵀ * M₀ + s • (1 : Matrix (Fin n) (Fin n) K)).det)
    (hΛ : colLambda M₀ h u v s ≠ 0)
    (hdel : colR M s - colR M₀ s =
      colAlpha3 M₀ h u v s • vecMulVec (colR M₀ s *ᵥ u) (colR M₀ s *ᵥ u)
        - colAlpha1 M₀ h u v s • vecMulVec (colR M₀ s *ᵥ u) (colX M₀ s *ᵥ v)
        - colAlpha1 M₀ h u v s • vecMulVec (colX M₀ s *ᵥ v) (colR M₀ s *ᵥ u)
        + colAlpha2 M₀ h u v s • vecMulVec (colX M₀ s *ᵥ v) (colX M₀ s *ᵥ v)) :
    colX M s - colX M₀ s =
      colAlpha3 M₀ h u v s • (colR M₀ s * vecMulVec u u * colX M₀ s)
        + (s * colAlpha1 M₀ h u v s) • (colR M₀ s * vecMulVec u v * colRt M₀ s)
        - colAlpha1 M₀ h u v s • (colX M₀ s * vecMulVec v u * colX M₀ s)
        - (s * colAlpha2 M₀ h u v s) • (colX M₀ s * vecMulVec v v * colRt M₀ s) := by
  have hsymm : (colR M₀ s)ᵀ = colR M₀ s := colR_transpose' M₀ s
  have hid : M₀ᵀ * colR M₀ s * M₀ = 1 - s • colRt M₀ s := colR_sandwich M₀ s hR₀ hRt₀
  have hXT : (colX M₀ s)ᵀ * M₀ = 1 - s • colRt M₀ s := by
    unfold colX
    rw [Matrix.transpose_mul, hsymm]
    exact hid
  have hvR : ∀ w : Fin m → K, w ᵥ* colR M₀ s = colR M₀ s *ᵥ w := by
    intro w
    rw [← Matrix.mulVec_transpose, hsymm]
  have V1 : (colR M₀ s *ᵥ u) ᵥ* M₀ = u ᵥ* colX M₀ s := by
    unfold colX
    rw [← hvR, Matrix.vecMul_vecMul]
  have V2 : (colX M₀ s *ᵥ v) ᵥ* M₀ = v - s • (v ᵥ* colRt M₀ s) := by
    have hvX : colX M₀ s *ᵥ v = v ᵥ* (colX M₀ s)ᵀ := by
      rw [← Matrix.mulVec_transpose, Matrix.transpose_transpose]
    rw [hvX, Matrix.vecMul_vecMul, hXT, Matrix.vecMul_sub, Matrix.vecMul_smul,
      Matrix.vecMul_one]
  have hRu := lem_app_drift_column_field_i M M₀ h s u v hΛ hdel
  have hR' := sub_eq_iff_eq_add'.mp hdel
  have hMR : ∀ R : Matrix (Fin m) (Fin m) K,
      R * M = R * M₀ + vecMulVec (h • (R *ᵥ u)) v := by
    intro R
    rw [hM, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_vecMulVec]
    congr 1
    ext i j
    simp [vecMulVec, mul_assoc]
  have hX' : colX M s = colR M s * M₀ + vecMulVec (h • (colR M s *ᵥ u)) v := hMR _
  have hd0 : colR M₀ s * M₀ = colX M₀ s := rfl
  have hsplit : ∀ a b c : Matrix (Fin m) (Fin n) K, a + b + c - a = b + c :=
    fun a b c => by abel
  rw [hX', hRu, hR', Matrix.add_mul (colR M₀ s), hd0, hsplit]
  simp only [Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul, Matrix.vecMulVec_mul,
    Matrix.mul_vecMulVec,
    V1, V2]
  ext i j
  simp only [vecMulVec, Matrix.of_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- lem:app-drift-column. Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.228–236, verbatim).
Parts (i) and (ii) are the conjunction below.

\begin{lemma}[Deletion identities for the mixed resolvent]\label{lem:app-drift-column}
In the setting of \cref{lem:app-de-deletion}, with $\mathsf X\defeq\mathsf X_s(M)$,
\begin{align}
\mathsf h\,R\mathsf u&=\alpha_1\,R_0\mathsf u-\alpha_2\,\mathsf X_0\mathsf v ,\label{eqn:app-drift-column}\\
\mathsf X-\mathsf X_0&=\alpha_3\,R_0(\mathsf u\tensor\mathsf u)\mathsf X_0+s\,\alpha_1\,R_0(\mathsf u\tensor\mathsf v)\widetilde R_0
-\alpha_1\,\mathsf X_0(\mathsf v\tensor\mathsf u)\mathsf X_0-s\,\alpha_2\,\mathsf X_0(\mathsf v\tensor\mathsf v)\widetilde R_0 .
\label{eqn:app-drift-Xdiff}
\end{align}
\end{lemma}

Real declaration of record (both parts, over `ℝ`, `0 < s`), stated with B's real objects
`Muon.DetEquiv.Rs`, `Xs`, `Rts`, `alpha1..3` (`Resolvent.lean`). Part (i): `𝗁 R 𝗎 = α₁ R₀ 𝗎 − α₂ 𝖷₀ 𝗏`.
Part (ii): the four-term `𝖷 − 𝖷₀` formula. The only hypotheses are `M = M₀ + 𝗁 𝗎⊗𝗏` and `0 < s`. -/
theorem lem_app_drift_column
    (M M₀ : Mat m n) (h s : ℝ) (u : Vec m) (v : Vec n)
    (hM : M = M₀ + h • outer u v) (hs : 0 < s) :
    h • (Muon.DetEquiv.Rs M s *ᵥ u) =
        Muon.DetEquiv.alpha1 M₀ h u v s • (Muon.DetEquiv.Rs M₀ s *ᵥ u)
          - Muon.DetEquiv.alpha2 M₀ h u v s • (Muon.DetEquiv.Xs M₀ s *ᵥ v) ∧
    Muon.DetEquiv.Xs M s - Muon.DetEquiv.Xs M₀ s =
        Muon.DetEquiv.alpha3 M₀ h u v s •
            (Muon.DetEquiv.Rs M₀ s * outer u u * Muon.DetEquiv.Xs M₀ s)
          + (s * Muon.DetEquiv.alpha1 M₀ h u v s) •
            (Muon.DetEquiv.Rs M₀ s * outer u v * Muon.DetEquiv.Rts M₀ s)
          - Muon.DetEquiv.alpha1 M₀ h u v s •
            (Muon.DetEquiv.Xs M₀ s * outer v u * Muon.DetEquiv.Xs M₀ s)
          - (s * Muon.DetEquiv.alpha2 M₀ h u v s) •
            (Muon.DetEquiv.Xs M₀ s * outer v v * Muon.DetEquiv.Rts M₀ s) := by
  have hUnit : ∀ {a b : ℕ} (A : Mat a b),
      IsUnit (A * Aᵀ + s • (1 : Mat a a)).det := by
    intro a b A
    have h1 : (A * Aᵀ).PosSemidef := by
      have h := Matrix.posSemidef_self_mul_conjTranspose A
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
    have h3 := Matrix.PosDef.add_posSemidef h2 h1
    rw [add_comm]
    exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'
  have hUnitT : IsUnit (M₀ᵀ * M₀ + s • (1 : Mat n n)).det := by
    have h := hUnit M₀ᵀ
    rwa [Matrix.transpose_transpose] at h
  have hdel := (Muon.DetEquiv.lem_app_de_deletion M₀ h u v M s hM hs).2.1
  have hΛ := (Muon.DetEquiv.lem_app_de_deletion M₀ h u v M s hM hs).1.ne'
  exact ⟨lem_app_drift_column_field_i (K := ℝ) M M₀ h s u v hΛ hdel,
    lem_app_drift_column_field_ii (K := ℝ) M M₀ h s u v hM (hUnit M₀) hUnitT hΛ hdel⟩

end Muon.Drift

end
