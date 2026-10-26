import Muon.Foundations.Conventions
import Muon.Setup.RegularizedMap

/-!
# Appendix A: Gram resolvents and rectangular resolvent intertwining

Work package L-A.3 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/01-setup/section.tex`: `lem:app-setup-intertwining` l.1015–1032 (with the
consequences `eqn:app-setup-AB-intertwining-consequences`), `eqn:app-setup-resolvents` l.1000–1003,
`eqn:app-setup-intertwining-M` l.1054–1056. Card `sections/01-setup/CARD.md` §2, §3, §5 row L-A.3.

Objects: the rectangular resolvents `rectRes A B z = (AB − z Id)⁻¹` (over ℂ, real inputs cast by
`Matrix.map Complex.ofReal`), and the Gram resolvents `Rres M z = (MMᵀ − z Id)⁻¹` and
`Rtil M z = (MᵀM − z Id)⁻¹` of the buffer `M`, with the paper's sign convention `R(z) = (MMᵀ − z)⁻¹`.

Not here: the spectral measures `eqn:app-setup-spectral-measures` are `Muon.nuOut` / `Muon.nuIn`
(`Muon.Foundations.Conventions`), reused and not restated. `eqn:app-setup-update-resolvent`
(revision of L-A.3, snapshot `cr-2026-10-23`) is stated at the end of this file, using `Muon.Q`
and `lem_app_setup_contour` from `Muon.Setup.RegularizedMap` (L-A.2).
-/

noncomputable section

open scoped Matrix MatrixOrder
open scoped ComplexOrder
open Matrix

namespace Muon.Setup

/-! ## Resolvent objects -/

/-- Rectangular resolvent `R_AB(z) = (AB − z Id_{n₁})⁻¹` over ℂ, for real `A : n₁ × n₂` and
`B : n₂ × n₁` (`lem:app-setup-intertwining`, `section.tex` l.1015–1032). The inverse is the
matrix-ring inverse; the paper's domain `z ∉ σ(AB)` is carried by `IsUnit` hypotheses in the
statements below, not by this definition. -/
def rectRes {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ) (B : Matrix (Fin n₂) (Fin n₁) ℝ)
    (z : ℂ) : Matrix (Fin n₁) (Fin n₁) ℂ :=
  ((A * B).map Complex.ofReal - z • (1 : Matrix (Fin n₁) (Fin n₁) ℂ))⁻¹

/-- eqn:app-setup-resolvents, output-side Gram resolvent `R(z) = (MMᵀ − z Id_{N_out})⁻¹` (first display). Snapshot `cr-2026-10-23`. LaTeX:

\begin{equation}\label{eqn:app-setup-resolvents}
R(z)\defeq\big(\Mt\Mt^\T-z\,\Id_{\Nout}\big)^{-1},\qquad
\widetilde R(z)\defeq\big(\Mt^\T\Mt-z\,\Id_{\Nin}\big)^{-1}.
\end{equation}
-/
def Rres {m n : ℕ} (M : Mat m n) (z : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  ((M * Mᵀ).map Complex.ofReal - z • (1 : Matrix (Fin m) (Fin m) ℂ))⁻¹

/-- eqn:app-setup-resolvents, input-side Gram resolvent `R̃(z) = (MᵀM − z Id_{N_in})⁻¹` (second display). Snapshot `cr-2026-10-23`. LaTeX:

\begin{equation}\label{eqn:app-setup-resolvents}
R(z)\defeq\big(\Mt\Mt^\T-z\,\Id_{\Nout}\big)^{-1},\qquad
\widetilde R(z)\defeq\big(\Mt^\T\Mt-z\,\Id_{\Nin}\big)^{-1}.
\end{equation}
-/
def Rtil {m n : ℕ} (M : Mat m n) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((Mᵀ * M).map Complex.ofReal - z • (1 : Matrix (Fin n) (Fin n) ℂ))⁻¹

/-! ## Rectangular resolvent intertwining -/

private lemma resAux_inv_facts {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) (h : IsUnit X) :
    X⁻¹ * X = 1 ∧ X * X⁻¹ = 1 := by
  obtain ⟨u, rfl⟩ := h
  rw [← Matrix.coe_units_inv]
  exact ⟨u.inv_mul, u.mul_inv⟩

private lemma resAux_intertwine {k l : ℕ} (a : Matrix (Fin k) (Fin l) ℂ)
    (b : Matrix (Fin l) (Fin k) ℂ) (z : ℂ)
    (hAB : IsUnit (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ)))
    (hBA : IsUnit (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))) :
    (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ))⁻¹ * a =
        a * (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))⁻¹ ∧
      b * (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ))⁻¹ =
        (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))⁻¹ * b := by
  obtain ⟨hX1, hX2⟩ := resAux_inv_facts _ hAB
  obtain ⟨hY1, hY2⟩ := resAux_inv_facts _ hBA
  have e1 : (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ)) * a =
      a * (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  have e2 : b * (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ)) =
      (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ)) * b := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.mul_assoc]
  set X := a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  set Y := b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ) with hYdef
  constructor
  · calc X⁻¹ * a = X⁻¹ * a * (Y * Y⁻¹) := by rw [hY2, Matrix.mul_one]
      _ = X⁻¹ * (a * Y) * Y⁻¹ := by simp only [Matrix.mul_assoc]
      _ = X⁻¹ * (X * a) * Y⁻¹ := by rw [e1]
      _ = a * Y⁻¹ := by rw [← Matrix.mul_assoc X⁻¹ X a, hX1, Matrix.one_mul]
  · calc b * X⁻¹ = Y⁻¹ * Y * (b * X⁻¹) := by rw [hY1, Matrix.one_mul]
      _ = Y⁻¹ * (Y * b) * X⁻¹ := by simp only [Matrix.mul_assoc]
      _ = Y⁻¹ * (b * X) * X⁻¹ := by rw [← e2]
      _ = Y⁻¹ * b * (X * X⁻¹) := by simp only [Matrix.mul_assoc]
      _ = Y⁻¹ * b := by rw [hX2, Matrix.mul_one]

private lemma resAux_consequences {k l : ℕ} (a : Matrix (Fin k) (Fin l) ℂ)
    (b : Matrix (Fin l) (Fin k) ℂ) (z : ℂ)
    (hAB : IsUnit (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ)))
    (hBA : IsUnit (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))) :
    a * (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))⁻¹ * b =
        (1 : Matrix (Fin k) (Fin k) ℂ) + z • (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ))⁻¹ ∧
      b * (a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ))⁻¹ * a =
        (1 : Matrix (Fin l) (Fin l) ℂ) + z • (b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ))⁻¹ := by
  obtain ⟨h1, h2⟩ := resAux_intertwine a b z hAB hBA
  obtain ⟨hX1, _⟩ := resAux_inv_facts _ hAB
  obtain ⟨hY1, _⟩ := resAux_inv_facts _ hBA
  set X := a * b - z • (1 : Matrix (Fin k) (Fin k) ℂ) with hXdef
  set Y := b * a - z • (1 : Matrix (Fin l) (Fin l) ℂ) with hYdef
  have hab : a * b = X + z • (1 : Matrix (Fin k) (Fin k) ℂ) := (sub_add_cancel _ _).symm
  have hba : b * a = Y + z • (1 : Matrix (Fin l) (Fin l) ℂ) := (sub_add_cancel _ _).symm
  constructor
  · rw [← h1, Matrix.mul_assoc, hab, Matrix.mul_add, hX1, Matrix.mul_smul, Matrix.mul_one]
  · rw [h2, Matrix.mul_assoc, hba, Matrix.mul_add, hY1, Matrix.mul_smul, Matrix.mul_one]

/-- lem:app-setup-intertwining, identities `R_AB A = A R_BA` and `B R_AB = R_BA B`. Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.lem_app_setup_intertwining_i`. LaTeX:

\begin{lemma}[Rectangular resolvent intertwining]\label{lem:app-setup-intertwining}
Let $\vec{A}\in\mathbb{R}^{n_1\times n_2}$ and $\vec{B}\in\mathbb{R}^{n_2\times n_1}$. For
$z\in\mathbb{C}\setminus(\sigma(\vec{A}\vec{B})\cup\sigma(\vec{B}\vec{A}))$, define
\[
R_{AB}(z)\defeq(\vec{A}\vec{B}-z\,\Id_{n_1})^{-1},\qquad
R_{BA}(z)\defeq(\vec{B}\vec{A}-z\,\Id_{n_2})^{-1}.
\]
Then
\begin{equation}\label{eqn:app-setup-AB-intertwining}
R_{AB}\vec{A}=\vec{A}R_{BA},\qquad
\vec{B}R_{AB}=R_{BA}\vec{B},
\end{equation}
and consequently
\begin{equation}\label{eqn:app-setup-AB-intertwining-consequences}
\vec{A}R_{BA}\vec{B}=\Id_{n_1}+z\,R_{AB},\qquad
\vec{B}R_{AB}\vec{A}=\Id_{n_2}+z\,R_{BA}.
\end{equation}
\end{lemma}
-/
theorem lem_app_setup_intertwining_i {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (B : Matrix (Fin n₂) (Fin n₁) ℝ) (z : ℂ)
    (hAB : IsUnit ((A * B).map Complex.ofReal - z • (1 : Matrix (Fin n₁) (Fin n₁) ℂ)))
    (hBA : IsUnit ((B * A).map Complex.ofReal - z • (1 : Matrix (Fin n₂) (Fin n₂) ℂ))) :
    rectRes A B z * A.map Complex.ofReal = A.map Complex.ofReal * rectRes B A z ∧
      B.map Complex.ofReal * rectRes A B z = rectRes B A z * B.map Complex.ofReal := by
  have hP : (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
    ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
  have hQ : (B * A).map Complex.ofReal = B.map Complex.ofReal * A.map Complex.ofReal := by
    ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
  unfold rectRes
  rw [hP] at hAB ⊢
  rw [hQ] at hBA ⊢
  exact resAux_intertwine _ _ z hAB hBA

/-- lem:app-setup-intertwining, consequences `A R_BA B = Id + z R_AB` and `B R_AB A = Id + z R_BA` (`eqn:app-setup-AB-intertwining-consequences`). Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.lem_app_setup_intertwining_ii`. LaTeX:

\begin{lemma}[Rectangular resolvent intertwining]\label{lem:app-setup-intertwining}
Let $\vec{A}\in\mathbb{R}^{n_1\times n_2}$ and $\vec{B}\in\mathbb{R}^{n_2\times n_1}$. For
$z\in\mathbb{C}\setminus(\sigma(\vec{A}\vec{B})\cup\sigma(\vec{B}\vec{A}))$, define
\[
R_{AB}(z)\defeq(\vec{A}\vec{B}-z\,\Id_{n_1})^{-1},\qquad
R_{BA}(z)\defeq(\vec{B}\vec{A}-z\,\Id_{n_2})^{-1}.
\]
Then
\begin{equation}\label{eqn:app-setup-AB-intertwining}
R_{AB}\vec{A}=\vec{A}R_{BA},\qquad
\vec{B}R_{AB}=R_{BA}\vec{B},
\end{equation}
and consequently
\begin{equation}\label{eqn:app-setup-AB-intertwining-consequences}
\vec{A}R_{BA}\vec{B}=\Id_{n_1}+z\,R_{AB},\qquad
\vec{B}R_{AB}\vec{A}=\Id_{n_2}+z\,R_{BA}.
\end{equation}
\end{lemma}
-/
theorem lem_app_setup_intertwining_ii {n₁ n₂ : ℕ} (A : Matrix (Fin n₁) (Fin n₂) ℝ)
    (B : Matrix (Fin n₂) (Fin n₁) ℝ) (z : ℂ)
    (hAB : IsUnit ((A * B).map Complex.ofReal - z • (1 : Matrix (Fin n₁) (Fin n₁) ℂ)))
    (hBA : IsUnit ((B * A).map Complex.ofReal - z • (1 : Matrix (Fin n₂) (Fin n₂) ℂ))) :
    A.map Complex.ofReal * rectRes B A z * B.map Complex.ofReal =
        (1 : Matrix (Fin n₁) (Fin n₁) ℂ) + z • rectRes A B z ∧
      B.map Complex.ofReal * rectRes A B z * A.map Complex.ofReal =
        (1 : Matrix (Fin n₂) (Fin n₂) ℂ) + z • rectRes B A z := by
  have hP : (A * B).map Complex.ofReal = A.map Complex.ofReal * B.map Complex.ofReal := by
    ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
  have hQ : (B * A).map Complex.ofReal = B.map Complex.ofReal * A.map Complex.ofReal := by
    ext i j; simp [Matrix.mul_apply, Complex.ofReal_sum]
  unfold rectRes
  rw [hP] at hAB ⊢
  rw [hQ] at hBA ⊢
  exact resAux_consequences _ _ z hAB hBA

/-! ## Gram resolvents for `z ∉ [0, ∞)` -/

/-- Private helper: a positive semidefinite complex matrix `X` has `X - z Id` invertible for
`z ∉ [0, ∞)`. Proof: if `(X - z)u = 0` with `u ≠ 0`, then `z ⟨u,u⟩ = ⟨u, Xu⟩ ≥ 0` with
`⟨u,u⟩ > 0`, forcing `z ∈ [0, ∞)`. -/
private lemma resAux_gram_aux {k : ℕ} (X : Matrix (Fin k) (Fin k) ℂ) (hX : X.PosSemidef)
    (z : ℂ) (hz : ∀ r : ℝ, 0 ≤ r → z ≠ (r : ℂ)) :
    IsUnit (X - z • (1 : Matrix (Fin k) (Fin k) ℂ)) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro u v huv
  by_contra hne
  have hu0 : u - v ≠ 0 := sub_ne_zero.mpr hne
  have hker : (X - z • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ (u - v) = 0 := by
    rw [Matrix.mulVec_sub, huv, sub_self]
  have hXu : X *ᵥ (u - v) = z • (u - v) := by
    have h1 : (X - z • (1 : Matrix (Fin k) (Fin k) ℂ)) *ᵥ (u - v) =
        X *ᵥ (u - v) - z • (u - v) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    rw [h1] at hker
    exact sub_eq_zero.mp hker
  have hs : 0 < star (u - v) ⬝ᵥ (u - v) := Matrix.dotProduct_star_self_pos_iff.mpr hu0
  have hnn : 0 ≤ star (u - v) ⬝ᵥ (X *ᵥ (u - v)) := hX.dotProduct_mulVec_nonneg (u - v)
  rw [hXu, dotProduct_smul, smul_eq_mul] at hnn
  rw [Complex.lt_def] at hs
  rw [Complex.le_def] at hnn
  simp only [Complex.mul_re, Complex.mul_im, Complex.zero_re, Complex.zero_im] at hnn
  obtain ⟨hsr, hsi⟩ := hs
  obtain ⟨hr, hi⟩ := hnn
  rw [Complex.zero_re] at hsr
  rw [Complex.zero_im] at hsi
  have hzim : z.im = 0 := by
    have h2 : z.im * (star (u - v) ⬝ᵥ (u - v)).re = 0 := by
      rw [← hsi] at hi
      linarith [hi]
    rcases mul_eq_zero.mp h2 with h | h
    · exact h
    · linarith
  have hzre : 0 ≤ z.re := by
    rw [hzim] at hr
    nlinarith [hr, hsr]
  apply hz z.re hzre
  apply Complex.ext
  · simp
  · simp [hzim]


/-- eqn:app-setup-resolvents (presupposition). For `z ∈ ℂ ∖ [0, ∞)` the matrices `MMᵀ − z Id` and `MᵀM − z Id` are invertible, since their spectra are nonnegative (PSD); the paper defines `R(z)` and `R̃(z)` on this domain. Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.gram_isUnit`. LaTeX:

\begin{equation}\label{eqn:app-setup-resolvents}
R(z)\defeq\big(\Mt\Mt^\T-z\,\Id_{\Nout}\big)^{-1},\qquad
\widetilde R(z)\defeq\big(\Mt^\T\Mt-z\,\Id_{\Nin}\big)^{-1}.
\end{equation}
-/
theorem gram_isUnit {m n : ℕ} (M : Mat m n) (z : ℂ) (hz : ∀ r : ℝ, 0 ≤ r → z ≠ (r : ℂ)) :
    IsUnit ((M * Mᵀ).map Complex.ofReal - z • (1 : Matrix (Fin m) (Fin m) ℂ)) ∧
      IsUnit ((Mᵀ * M).map Complex.ofReal - z • (1 : Matrix (Fin n) (Fin n) ℂ)) := by
  have hB : (M * Mᵀ).map Complex.ofReal =
      (M.map Complex.ofReal) * (M.map Complex.ofReal)ᴴ := by
    ext i j; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
  have hC : (Mᵀ * M).map Complex.ofReal =
      (M.map Complex.ofReal)ᴴ * (M.map Complex.ofReal) := by
    ext i j; simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.ofReal_sum]
  rw [hB, hC]
  exact ⟨resAux_gram_aux _ (Matrix.posSemidef_self_mul_conjTranspose _) z hz,
    resAux_gram_aux _ (Matrix.posSemidef_conjTranspose_mul_self _) z hz⟩

/-- eqn:app-setup-intertwining-M, first identity `R(z) M = M R̃(z)` for `z ∈ ℂ ∖ [0, ∞)`. Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.eqn_app_setup_intertwining_M_i`. LaTeX:

\begin{equation}\label{eqn:app-setup-intertwining-M}
R(z)\Mt=\Mt\widetilde R(z),\qquad \Mt^\T R(z)\Mt=\Id_{\Nin}+z\widetilde R(z),\qquad
\Mt\widetilde R(z)\Mt^\T=\Id_{\Nout}+zR(z).
\end{equation}
-/
theorem eqn_app_setup_intertwining_M_i {m n : ℕ} (M : Mat m n) (z : ℂ)
    (hz : ∀ r : ℝ, 0 ≤ r → z ≠ (r : ℂ)) :
    Rres M z * M.map Complex.ofReal = M.map Complex.ofReal * Rtil M z := by
  obtain ⟨hAB, hBA⟩ := gram_isUnit M z hz
  exact (lem_app_setup_intertwining_i M Mᵀ z hAB hBA).1

/-- eqn:app-setup-intertwining-M, second identity `Mᵀ R(z) M = Id_{N_in} + z R̃(z)`. Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.eqn_app_setup_intertwining_M_ii`. LaTeX:

\begin{equation}\label{eqn:app-setup-intertwining-M}
R(z)\Mt=\Mt\widetilde R(z),\qquad \Mt^\T R(z)\Mt=\Id_{\Nin}+z\widetilde R(z),\qquad
\Mt\widetilde R(z)\Mt^\T=\Id_{\Nout}+zR(z).
\end{equation}
-/
theorem eqn_app_setup_intertwining_M_ii {m n : ℕ} (M : Mat m n) (z : ℂ)
    (hz : ∀ r : ℝ, 0 ≤ r → z ≠ (r : ℂ)) :
    Mᵀ.map Complex.ofReal * Rres M z * M.map Complex.ofReal =
      (1 : Matrix (Fin n) (Fin n) ℂ) + z • Rtil M z := by
  obtain ⟨hAB, hBA⟩ := gram_isUnit M z hz
  exact (lem_app_setup_intertwining_ii M Mᵀ z hAB hBA).2

/-- eqn:app-setup-intertwining-M, third identity `M R̃(z) Mᵀ = Id_{N_out} + z R(z)`. Snapshot `cr-2026-10-23`. Declaration of record `Muon.Setup.eqn_app_setup_intertwining_M_iii`. LaTeX:

\begin{equation}\label{eqn:app-setup-intertwining-M}
R(z)\Mt=\Mt\widetilde R(z),\qquad \Mt^\T R(z)\Mt=\Id_{\Nin}+z\widetilde R(z),\qquad
\Mt\widetilde R(z)\Mt^\T=\Id_{\Nout}+zR(z).
\end{equation}
-/
theorem eqn_app_setup_intertwining_M_iii {m n : ℕ} (M : Mat m n) (z : ℂ)
    (hz : ∀ r : ℝ, 0 ≤ r → z ≠ (r : ℂ)) :
    M.map Complex.ofReal * Rtil M z * Mᵀ.map Complex.ofReal =
      (1 : Matrix (Fin m) (Fin m) ℂ) + z • Rres M z := by
  obtain ⟨hAB, hBA⟩ := gram_isUnit M z hz
  exact (lem_app_setup_intertwining_ii M Mᵀ z hAB hBA).1

/-! ## Real-to-complex transport for the regularized update -/

private lemma resAux_real_posDef {m n : ℕ} (M : Mat m n) {c : ℝ} (hc : 0 < c) :
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

private lemma resAux_map_inv {m : ℕ} (X : Mat m m) (hX : IsUnit X.det) :
    (X⁻¹).map Complex.ofReal = (X.map Complex.ofReal)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  have h1 : X.map Complex.ofReal * (X⁻¹).map Complex.ofReal = (X * X⁻¹).map Complex.ofReal := by
    ext a b
    simp [Matrix.mul_apply, Complex.ofReal_sum]
  rw [h1, Matrix.mul_nonsing_inv X hX]
  ext a b
  by_cases h : a = b <;> simp [Matrix.one_apply, h]

/-! ## Regularized update as an integral of the Gram resolvent -/

/-- eqn:app-setup-update-resolvent, `Q_ϱ(Mₜ) = (2/π) ∫₀^∞ R(−ϱ − u²) Mₜ du`, entrywise, with the
integrand's real argument `z = −(ϱ + u²)` and `R = Rres M` (`eqn:app-setup-resolvents`). Snapshot
`cr-2026-10-23`. Declaration of record `Muon.Setup.eqn_app_setup_update_resolvent`. LaTeX:

\begin{equation}\label{eqn:app-setup-update-resolvent}
\Qridge{\ridge}(\Mt)=\frac2\pi\int_0^\infty R(-\ridge-u^2)\,\Mt\,du ,
\end{equation}
-/
theorem eqn_app_setup_update_resolvent {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) (M : Mat m n) :
    ∀ i j, ((Q ϱ M).map Complex.ofReal) i j =
      (2 / (Real.pi : ℂ)) * ∫ u in Set.Ioi (0 : ℝ),
        (Rres M ((-(ϱ + u ^ 2) : ℝ) : ℂ) * M.map Complex.ofReal) i j := by
  intro i j
  have hcontour := (lem_app_setup_contour ϱ hϱ M).1 i j
  have hfun : ∀ u : ℝ, (Rres M ((-(ϱ + u ^ 2) : ℝ) : ℂ) * M.map Complex.ofReal) i j =
      (((M * Mᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * M) i j : ℂ) := by
    intro u
    have hc : 0 < ϱ + u ^ 2 := by positivity
    have hdet' : IsUnit (M * Mᵀ + (ϱ + u ^ 2) • (1 : Mat m m)).det :=
      isUnit_iff_ne_zero.mpr (resAux_real_posDef M hc).det_pos.ne'
    have hR : Rres M ((-(ϱ + u ^ 2) : ℝ) : ℂ) =
        ((M * Mᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹).map Complex.ofReal := by
      rw [resAux_map_inv _ hdet']
      unfold Rres
      congr 1
      ext a b
      by_cases h : a = b <;> simp [h, Matrix.map_apply] <;> ring
    rw [hR]
    simp [Matrix.mul_apply, Complex.ofReal_sum]
  simp only [hfun]
  rw [Matrix.map_apply, hcontour, integral_complex_ofReal, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_ofNat]

end Muon.Setup

end
