import Muon.Drift.Defs

/-!
# Muon.Drift: kernel, half-anisotropic and truncation statements (work package L-C.4)

Snapshot `cr-2026-10-23`. Section `sections/03-drift/section.tex`; card `sections/03-drift/CARD.md`
§3 and §5 row L-C.4. Owned statements:

* `cor:app-drift-kernel`: part (ii) (`cor_app_drift_kernel_ii`, `cor_app_drift_kernel_ii_lip`),
  and the diagonal helper of part (i) (`kernel_diag_gbar`). The remaining clauses of part (i)
  belong to L-C.10.
* `cor:app-drift-halfaniso`: parts (i), (iii), (iv) (`cor_app_drift_halfaniso_i`, `_iii`, `_iv`).
  The label alias `rem:app-drift-halfaniso` maps to the same declarations. Part (ii) is L-C.11.
* `prop:app-drift-truncation`: part (ii) (`prop_app_drift_truncation_ii`).
* `thm:app-drift-mixed`: the `T`-bound of part (ii) (`thm_app_drift_mixed_ii_T`). The `𝓗`-bound
  and part (i) belong to L-C.7 and L-C.9.
* Helpers of card §5: `DriftBound` (the data bundle), `spectral_mem_classK`,
  `gbar_integrable_bound` (first claim of `thm:app-drift-mean`, assembled by L-C.10).

Definitions come from `Muon.Drift.Defs` (L-C.1). The spectral measures are always passed as
`(specOutFM F, specInFM F)`, in that order. Every constant `CS`, `γ` is a positive real standing
for the paper's `C_Σ`, `γ⋆`. No `sorry` is a definition; every proof body is `sorry`.

Deviations and open points are listed in the result JSON `open_questions`:
* `cor_app_drift_halfaniso_iv` takes the Stieltjes hypothesis in its negative-axis form
  (`hStieltjes`, for `z > 0`). The source as written is ill-typed (card §6.8; `CORRECTIONS.md`
  row 4 is pending).
* `prop_app_drift_truncation_ii` states the limit in ε–N form (card §6.11).
-/

open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

namespace Muon.Drift

variable {m n B : ℕ}

/-- Data bundle of the frozen-state model in `thm:app-drift-mixed`(ii): `max(N_out,N_in) ≤ γ⋆ B`
and `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ`. The normalization `‖Â‖_F = 1` is the field `F.hA`. Snapshot
`cr-2026-10-23`. Source, verbatim (`sections/03-drift/section.tex`):
```
\begin{theorem}[Mixed resolvent closure and tail bound]\label{thm:app-drift-mixed}
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every compact $I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-drift-mixed}
\sup_{s\in I}\norm{\mathcal H(s)-T(s)}_\F\longrightarrow0 .
\end{equation}
\item In the frozen-state model under \cref{assum:data-target}, with
$\max(\Nout,\Nin)\le\gamma_\star B$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$,
$\norm{\Ahat}_\F=1$ and weights satisfying \cref{eqn:app-drift-weights}, but
without any condition on $\norm{\Ahat}$ and for every finite dimension,
there is $C$ depending only on $(C_\Sigma,\gamma_\star)$ such that
\begin{equation}\label{eqn:app-drift-tail}
\norm{\mathcal H(s)}_\F\le\frac{C}{s}\quad(s\ge1),\qquad
\norm{T(s)}_\F\le\frac{C_\Sigma}{s}\quad(s>0).
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
def DriftBound (F : FrozenParams m n B) (CS γ : ℝ) : Prop :=
  opNorm F.C.Sout ≤ CS ∧ opNorm F.C.Sin ≤ CS ∧ ((max m n : ℕ) : ℝ) ≤ γ * (B : ℝ)

/-! ### Private helpers (proof support for the two targets; not statements) -/

open scoped MatrixOrder Matrix.Norms.L2Operator

private lemma kern_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  rw [opNorm_eq_norm]; exact norm_nonneg _

private lemma kern_fro_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ fro K := Real.sqrt_nonneg _

private lemma kern_sq_sum_eq {p q : ℕ} (K : Mat p q) : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma kern_fro_transpose {p q : ℕ} (K : Mat p q) : fro Kᵀ = fro K := by
  unfold fro
  congr 1
  exact Finset.sum_comm

open scoped Matrix.Norms.L2Operator in
private lemma kern_opNorm_transpose {p q : ℕ} (K : Mat p q) : opNorm Kᵀ = opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

open scoped Matrix.Norms.Frobenius in
private lemma kern_fro_smul {p q : ℕ} (c : ℝ) (K : Mat p q) : fro (c • K) = |c| * fro K := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

/-- Operator-norm bound from a squared-vector bound. -/
private lemma kern_opNorm_le_of_sq {a b : ℕ} (K : Mat a b) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x : Vec b, ∑ k, (K *ᵥ x) k ^ 2 ≤ c ^ 2 * ∑ i, x i ^ 2) : opNorm K ≤ c := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hc fun x => ?_
  show ‖Matrix.toEuclideanLin K x‖ ≤ c * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin K x‖ ^ 2 ≤ (c * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin K x), mul_nonneg hc (norm_nonneg x)]

/-- `‖K x‖₂² ≤ ‖K‖² ‖x‖₂²` in coordinates. -/
private lemma kern_sq_mulVec_le {p q : ℕ} (U : Mat p q) (x : Vec q) :
    ∑ k, (U *ᵥ x) k ^ 2 ≤ opNorm U ^ 2 * ∑ i, x i ^ 2 := by
  have h2 : ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ≤ opNorm U * ‖WithLp.toLp 2 x‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm (WithLp.toLp 2 x)
    simpa [opNorm] using this
  have hn : ∀ v : Vec q, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have hm : ∑ k, (U *ᵥ x) k ^ 2 = ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ^ 2 := by
    have e : Matrix.toEuclideanLin U (WithLp.toLp 2 x) = WithLp.toLp 2 (U *ᵥ x) := by
      ext k
      simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct]
    rw [e]
    have hp : ∀ v : Vec p, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
      intro v
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    exact (hp _).symm
  rw [hm, ← hn x]
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow] at h3
  exact h3

private lemma kern_fro_mul_left {p q r : ℕ} (X : Mat p q) (Y : Mat q r) :
    fro (X * Y) ≤ opNorm X * fro Y := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (mul_nonneg (kern_opNorm_nonneg X) (kern_fro_nonneg _)) ?_
  have hL : fro (X * Y) ^ 2 = ∑ j, ∑ i, (X * Y) i j ^ 2 := by
    rw [kern_sq_sum_eq, Finset.sum_comm]
  have hR : (opNorm X * fro Y) ^ 2 = opNorm X ^ 2 * ∑ k, ∑ j, Y k j ^ 2 := by
    rw [mul_pow, kern_sq_sum_eq]
  rw [hL, hR]
  calc ∑ j, ∑ i, (X * Y) i j ^ 2 ≤ ∑ j, opNorm X ^ 2 * ∑ k, Y k j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h := kern_sq_mulVec_le X (fun k => Y k j)
        have e : ∀ i, (X * Y) i j = (X *ᵥ fun k => Y k j) i := fun i => by
          simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
        simp only [e]
        exact h
    _ = opNorm X ^ 2 * ∑ k, ∑ j, Y k j ^ 2 := by
        simp only [Finset.mul_sum]
        exact Finset.sum_comm

private lemma kern_fro_mul_right {p q r : ℕ} (Y : Mat p q) (X : Mat q r) :
    fro (Y * X) ≤ fro Y * opNorm X := by
  have h := kern_fro_mul_left Xᵀ Yᵀ
  rw [← Matrix.transpose_mul, kern_fro_transpose, kern_fro_transpose, kern_opNorm_transpose] at h
  linarith [mul_comm (fro Y) (opNorm X)]

/-- Copy of the squared-quadratic bound for `CFC.sqrt` (`Muon.DetEquiv.Gaussian`, private there). -/
private lemma kern_sqrt_quad {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) (C : ℝ)
    (hC : opNorm S ≤ C) (z : Vec k) :
    ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2 ≤ C * ∑ i, z i ^ 2 := by
  have h0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS
  have hR : (CFC.sqrt S).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  have hRR : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h0
  have hsym : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    simpa using hR.eq
  have h1 : ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2 = dotProduct z (Matrix.mulVec S z) := by
    calc ∑ i, (Matrix.mulVec (CFC.sqrt S) z i) ^ 2
        = dotProduct (Matrix.mulVec (CFC.sqrt S) z) (Matrix.mulVec (CFC.sqrt S) z) := by
          simp [dotProduct, sq]
      _ = dotProduct z (Matrix.mulVec S z) := by
          rw [Matrix.dotProduct_mulVec, ← hsym, Matrix.vecMul_transpose, hsym,
            Matrix.mulVec_mulVec, hRR, dotProduct_comm]
  have h2 : ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ ≤ opNorm S * ‖WithLp.toLp 2 z‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)).le_opNorm (WithLp.toLp 2 z)
    simpa [opNorm] using this
  have hn : ∀ v : Vec k, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
    intro v
    rw [EuclideanSpace.norm_sq_eq]
    simp [Real.norm_eq_abs, sq_abs]
  have h3 : dotProduct z (Matrix.mulVec S z)
      = inner ℝ (WithLp.toLp 2 z) (Matrix.toEuclideanLin S (WithLp.toLp 2 z)) := by
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_toLp, dotProduct, PiLp.inner_apply, mul_comm]
  have h4 : ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ ≤ C * ‖WithLp.toLp 2 z‖ :=
    h2.trans (mul_le_mul_of_nonneg_right hC (norm_nonneg _))
  rw [h1, h3, ← hn]
  calc inner ℝ (WithLp.toLp 2 z) (Matrix.toEuclideanLin S (WithLp.toLp 2 z))
      ≤ ‖WithLp.toLp 2 z‖ * ‖Matrix.toEuclideanLin S (WithLp.toLp 2 z)‖ := real_inner_le_norm _ _
    _ ≤ ‖WithLp.toLp 2 z‖ * (C * ‖WithLp.toLp 2 z‖) := mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = C * ‖WithLp.toLp 2 z‖ ^ 2 := by ring

private lemma kern_sqrt_opNorm_le {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) (CS : ℝ)
    (hCS : opNorm S ≤ CS) (h0 : 0 ≤ CS) : opNorm (CFC.sqrt S) ≤ Real.sqrt CS := by
  refine kern_opNorm_le_of_sq _ (Real.sqrt_nonneg _) fun z => ?_
  rw [Real.sq_sqrt h0]
  exact kern_sqrt_quad S hS CS hCS z

private lemma kern_EG_fro_le (F : FrozenParams m n B) {CS : ℝ} (hCS : 0 < CS)
    (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS) :
    fro (rOut F.C * F.A * rIn F.C) ≤ CS := by
  have h1 := kern_fro_mul_right (rOut F.C * F.A) (rIn F.C)
  have h2 := kern_fro_mul_left (rOut F.C) F.A
  rw [F.hA, mul_one] at h2
  have ho := kern_sqrt_opNorm_le F.C.Sout F.C.psdOut CS hSo hCS.le
  have hi := kern_sqrt_opNorm_le F.C.Sin F.C.psdIn CS hSi hCS.le
  calc fro (rOut F.C * F.A * rIn F.C)
      ≤ fro (rOut F.C * F.A) * opNorm (rIn F.C) := h1
    _ ≤ opNorm (rOut F.C) * opNorm (rIn F.C) :=
        mul_le_mul_of_nonneg_right h2 (kern_opNorm_nonneg _)
    _ ≤ Real.sqrt CS * Real.sqrt CS :=
        mul_le_mul ho hi (kern_opNorm_nonneg _) (Real.sqrt_nonneg _)
    _ = CS := Real.mul_self_sqrt hCS.le

/-- Inverse of `s • 1 + a • S` (PSD `S`, `a, s`, `a ≥ 0`, `s > 0`) has operator norm `≤ 1/s`. -/
private lemma kern_inv_opNorm_le {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) :
    opNorm (s • (1 : Mat k k) + a • S)⁻¹ ≤ 1 / s := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hMy : ∀ (y : Vec k) (i : Fin k), (M *ᵥ y) i = s * y i + a * (S *ᵥ y) i := by
    intro y i
    simp [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  have key : ∀ y : Vec k, s ^ 2 * ∑ i, y i ^ 2 ≤ ∑ i, (M *ᵥ y) i ^ 2 := by
    intro y
    have hYnn : 0 ≤ ∑ i, y i * (S *ᵥ y) i := by
      have := hS.dotProduct_mulVec_nonneg y
      simpa [dotProduct, star_trivial] using this
    have hz : 0 ≤ ∑ i, (S *ᵥ y) i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have e : ∑ i, (M *ᵥ y) i ^ 2 = ∑ i, (s ^ 2 * y i ^ 2 + 2 * s * a * (y i * (S *ᵥ y) i)
        + a ^ 2 * (S *ᵥ y) i ^ 2) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hMy]; ring
    rw [e]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hs.le) ha) hYnn,
      mul_nonneg (sq_nonneg a) hz]
  have hinj : Function.Injective (M *ᵥ ·) := by
    intro y y' h
    have h' : M *ᵥ y = M *ᵥ y' := h
    have h0 : M *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h', sub_self]
    have h1 := key (y - y')
    have h2 : ∑ i, (M *ᵥ (y - y')) i ^ 2 = 0 := by rw [h0]; simp
    have hnn : 0 ≤ ∑ i, (y - y') i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, (y - y') i ^ 2 = 0 := by
      have hs2 : 0 < s ^ 2 := pow_pos hs 2
      refine le_antisymm ?_ hnn
      nlinarith
    have hz : ∀ i, (y - y') i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg ((y - y') i))).mp hsum i
        (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).mp this
    exact sub_eq_zero.mp (funext hz)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M ((Matrix.isUnit_iff_isUnit_det M).mp hu)
  refine kern_opNorm_le_of_sq _ (one_div_nonneg.mpr hs.le) fun v => ?_
  have hv : M *ᵥ (M⁻¹ *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hMinv, Matrix.one_mulVec]
  have h := key (M⁻¹ *ᵥ v)
  rw [hv] at h
  have hs2 : 0 < s ^ 2 := pow_pos hs 2
  rw [div_pow, one_pow, one_div]
  calc ∑ i, (M⁻¹ *ᵥ v) i ^ 2 = (s ^ 2)⁻¹ * (s ^ 2 * ∑ i, (M⁻¹ *ᵥ v) i ^ 2) := by
        rw [← mul_assoc, inv_mul_cancel₀ hs2.ne', one_mul]
    _ ≤ (s ^ 2)⁻¹ * ∑ i, v i ^ 2 := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hs2.le)

/-- `0 ≤ L_w(q) ≤ 1` for `q ≥ 0` under `WeightClass w` (`J ∈ [0,1]` on `[0,∞)`). -/
private lemma kern_Lw_bounds {w : ℕ → ℝ} (hw : WeightClass w) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Lw w q ∧ Lw w q ≤ 1 := by
  obtain ⟨⟨hw0, hwS, -⟩, -, hw1⟩ := hw
  have hJ0 : ∀ j, 0 ≤ Muon.DetEquiv.J (w j ^ 2 * q) := fun j => by
    unfold Muon.DetEquiv.J
    apply integral_nonneg
    intro g
    have hm := mul_nonneg (mul_nonneg (sq_nonneg (w j)) hq) (sq_nonneg g)
    exact div_nonneg (sq_nonneg g) (by linarith)
  have hJ1 : ∀ j, Muon.DetEquiv.J (w j ^ 2 * q) ≤ 1 := fun j => by
    unfold Muon.DetEquiv.J
    have hx : 0 ≤ w j ^ 2 * q := mul_nonneg (sq_nonneg _) hq
    have hpt : ∀ g : ℝ, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ≤ g ^ 2 := fun g => by
      have hm := mul_nonneg hx (sq_nonneg g)
      exact div_le_self (sq_nonneg g) (by linarith)
    calc (∫ g, g ^ 2 / (1 + w j ^ 2 * q * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
        ≤ ∫ g, g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun g => div_nonneg (sq_nonneg g) (by
              have hm := mul_nonneg hx (sq_nonneg g)
              linarith))
            (Muon.Foundations.gaussian_integrable_pow 2) (Filter.Eventually.of_forall hpt)
      _ = 1 := Muon.Foundations.gaussian_moment_two
  have hterm : ∀ j, 0 ≤ w j * Muon.DetEquiv.J (w j ^ 2 * q) := fun j => mul_nonneg (hw0 j) (hJ0 j)
  have hle : ∀ j, w j * Muon.DetEquiv.J (w j ^ 2 * q) ≤ w j := fun j =>
    mul_le_of_le_one_right (hw0 j) (hJ1 j)
  have hS : Summable (fun j => w j * Muon.DetEquiv.J (w j ^ 2 * q)) :=
    Summable.of_nonneg_of_le hterm hle hwS
  refine ⟨tsum_nonneg hterm, ?_⟩
  calc Lw w q = ∑' j, w j * Muon.DetEquiv.J (w j ^ 2 * q) := rfl
    _ ≤ ∑' j, w j := hS.tsum_le_tsum hle hwS
    _ ≤ 1 := hw1

private lemma kern_isBranch_nonneg {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {s : ℝ}
    {x : ℝ × ℝ × ℝ × ℝ} (h : IsBranchSol F ν ν' s x) :
    0 ≤ x.1 ∧ 0 ≤ x.2.1 ∧ 0 ≤ x.2.2.1 ∧ 0 ≤ x.2.2.2 := by
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨a1, a2, a3, a4, -⟩ := h
  exact ⟨a1, a2, a3, a4⟩

/-- Mass and support of `(1/B) ∑ δ_{λ_i}` for the eigenvalues of a PSD `S` with `‖S‖ ≤ CS`
and `k ≤ γ B`: zero outside `[0, CS]`, total mass on `[0, CS]` at most `γ`. -/
private lemma kern_meas_props {k B : ℕ} (S : Mat k k) (hS : S.PosSemidef) {CS γ : ℝ}
    (hCS : opNorm S ≤ CS) (hB : 0 < B) (hk : (k : ℝ) ≤ γ * B) :
    ((B : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS)ᶜ = 0 ∧
    ((B : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS)
      ≤ ENNReal.ofReal γ := by
  have habs : ∀ i, |hS.isHermitian.eigenvalues i| ≤ opNorm S := by
    intro i
    have hv := hS.isHermitian.mulVec_eigenvectorBasis i
    have hn : ‖hS.isHermitian.eigenvectorBasis i‖ = 1 :=
      hS.isHermitian.eigenvectorBasis.orthonormal.1 i
    have h1 := Matrix.l2_opNorm_mulVec S (hS.isHermitian.eigenvectorBasis i)
    have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (S *ᵥ ⇑(hS.isHermitian.eigenvectorBasis i)) =
        hS.isHermitian.eigenvalues i • hS.isHermitian.eigenvectorBasis i := by
      rw [hv]
      ext
      simp
    rw [h2, norm_smul, hn, Real.norm_eq_abs] at h1
    simp only [mul_one] at h1
    rw [opNorm_eq_norm]
    exact h1
  have hmem : ∀ i, hS.isHermitian.eigenvalues i ∈ Icc (0:ℝ) CS := fun i =>
    ⟨Matrix.PosSemidef.eigenvalues_nonneg hS i,
      (le_abs_self _).trans ((habs i).trans hCS)⟩
  constructor
  · have hz : ∀ i, Measure.dirac (hS.isHermitian.eigenvalues i) (Icc 0 CS)ᶜ = 0 := fun i => by
      rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
      exact Set.indicator_of_notMem (by rw [Set.mem_compl_iff, not_not]; exact hmem i) _
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hz,
      Finset.sum_const_zero, smul_zero]
  · have h1 : ∀ i, Measure.dirac (hS.isHermitian.eigenvalues i) (Icc 0 CS) = 1 := fun i =>
      Measure.dirac_apply_of_mem (hmem i)
    have hsum : (∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS) = (k : ℝ≥0∞) := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, h1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hconv : (B : ℝ≥0∞)⁻¹ * (k : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ) / B) := by
      rw [ENNReal.ofReal_div_of_pos hBr, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        div_eq_mul_inv, mul_comm]
    rw [Measure.smul_apply, hsum, smul_eq_mul, hconv]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hBr).mpr hk)
/-- Helper of `thm:app-drift-mixed`(ii): under `DriftBound`, the pair of spectral measures lies in
the class `𝒦` of `eqn:app-de-class` (`classK`), so that the branch theorem applies. Snapshot
`cr-2026-10-23`. Source context, verbatim:
```
\begin{theorem}[Mixed resolvent closure and tail bound]\label{thm:app-drift-mixed}
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every compact $I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-drift-mixed}
\sup_{s\in I}\norm{\mathcal H(s)-T(s)}_\F\longrightarrow0 .
\end{equation}
\item In the frozen-state model under \cref{assum:data-target}, with
$\max(\Nout,\Nin)\le\gamma_\star B$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$,
$\norm{\Ahat}_\F=1$ and weights satisfying \cref{eqn:app-drift-weights}, but
without any condition on $\norm{\Ahat}$ and for every finite dimension,
there is $C$ depending only on $(C_\Sigma,\gamma_\star)$ such that
\begin{equation}\label{eqn:app-drift-tail}
\norm{\mathcal H(s)}_\F\le\frac{C}{s}\quad(s\ge1),\qquad
\norm{T(s)}_\F\le\frac{C_\Sigma}{s}\quad(s>0).
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem spectral_mem_classK (F : FrozenParams m n B) {CS γ : ℝ} (h : DriftBound F CS γ) :
    (specOutFM F, specInFM F) ∈ classK CS γ := by
  obtain ⟨hSo, hSi, hmax⟩ := h
  have hB : 0 < B := F.hB
  have hm : (m : ℝ) ≤ γ * B := (Nat.cast_le.mpr (le_max_left m n)).trans hmax
  have hn : (n : ℝ) ≤ γ * B := (Nat.cast_le.mpr (le_max_right m n)).trans hmax
  obtain ⟨o1, o2⟩ := kern_meas_props F.C.Sout F.C.psdOut hSo hB hm
  obtain ⟨i1, i2⟩ := kern_meas_props F.C.Sin F.C.psdIn hSi hB hn
  exact ⟨o2, o1, i2, i1⟩

/-- `thm:app-drift-mixed`(ii), the `T`-bound only: `‖T(s)‖_F ≤ C_Σ/s` for every `s > 0`, under
`WeightClass w` and `DriftBound`. The bound on `𝓗(s)` belongs to L-C.7. Snapshot
`cr-2026-10-23`. Source, verbatim:
```
\begin{theorem}[Mixed resolvent closure and tail bound]\label{thm:app-drift-mixed}
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every compact $I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-drift-mixed}
\sup_{s\in I}\norm{\mathcal H(s)-T(s)}_\F\longrightarrow0 .
\end{equation}
\item In the frozen-state model under \cref{assum:data-target}, with
$\max(\Nout,\Nin)\le\gamma_\star B$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$,
$\norm{\Ahat}_\F=1$ and weights satisfying \cref{eqn:app-drift-weights}, but
without any condition on $\norm{\Ahat}$ and for every finite dimension,
there is $C$ depending only on $(C_\Sigma,\gamma_\star)$ such that
\begin{equation}\label{eqn:app-drift-tail}
\norm{\mathcal H(s)}_\F\le\frac{C}{s}\quad(s\ge1),\qquad
\norm{T(s)}_\F\le\frac{C_\Sigma}{s}\quad(s>0).
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_drift_mixed_ii_T {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {s : ℝ} (hs : 0 < s) :
    fro (Tcand w F (specOutFM F) (specInFM F) s) ≤ CS / s := by
  have hp := spectral_mem_classK F h
  obtain ⟨hSo, hSi, -⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := kern_isBranch_nonneg
    (branchSol_spec (Fw_admissible hw.1) hC hγ hp hs)
  have hq : 0 ≤ branchQ w (specOutFM F) (specInFM F) s := by
    unfold branchQ
    exact mul_nonneg (mul_nonneg hs.le h1) h2
  obtain ⟨L0, L1⟩ := kern_Lw_bounds hw hq
  have hR := kern_inv_opNorm_le F.C.Sout F.C.psdOut h3 hs
  have hRt := kern_inv_opNorm_le F.C.Sin F.C.psdIn h4 hs
  have hEG := kern_EG_fro_le F hC hSo hSi
  have hinv : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
  have hX : fro (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F
      * Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) ≤ (1 / s) * CS * (1 / s) := by
    calc _ ≤ fro (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F)
          * opNorm (Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) := kern_fro_mul_right _ _
      _ ≤ (opNorm (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s) * fro (EG F))
          * opNorm (Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) :=
          mul_le_mul_of_nonneg_right (kern_fro_mul_left _ _) (kern_opNorm_nonneg _)
      _ ≤ ((1 / s) * CS) * (1 / s) :=
          mul_le_mul (mul_le_mul hR hEG (kern_fro_nonneg _) hinv) hRt (kern_opNorm_nonneg _)
            (mul_nonneg hinv hC.le)
      _ = (1 / s) * CS * (1 / s) := rfl
  unfold Tcand
  rw [kern_fro_smul, abs_of_nonneg (mul_nonneg hs.le L0)]
  have hXnn := kern_fro_nonneg (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F
      * Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s)
  calc s * Lw w (branchQ w (specOutFM F) (specInFM F) s) * _
      ≤ s * 1 * _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left L1 hs.le) hXnn
    _ ≤ s * 1 * ((1 / s) * CS * (1 / s)) := mul_le_mul_of_nonneg_left hX (by linarith)
    _ = CS / s := by field_simp

/-- `s • 1 + a • S` is invertible (`S` PSD, `a ≥ 0`, `s > 0`). -/
private lemma kern_isUnit_det {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) : (s • (1 : Mat k k) + a • S).det ≠ 0 := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hinj : Function.Injective (M *ᵥ ·) := by
    intro y y' h
    have h' : M *ᵥ y = M *ᵥ y' := h
    have h0 : M *ᵥ (y - y') = 0 := by rw [Matrix.mulVec_sub, h', sub_self]
    set z := y - y' with hz
    have hSz : 0 ≤ ∑ i, z i * (S *ᵥ z) i := by
      have := hS.dotProduct_mulVec_nonneg z
      simpa [dotProduct, star_trivial] using this
    have hMz : M *ᵥ z = s • z + a • (S *ᵥ z) := by
      simp [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    have h1 : 0 = ∑ i, z i * (M *ᵥ z) i := by rw [h0]; simp
    have h2 : ∑ i, z i * (M *ᵥ z) i = s * ∑ i, z i ^ 2 + a * ∑ i, z i * (S *ᵥ z) i := by
      rw [hMz, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp; ring
    have hnn : 0 ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hsum : ∑ i, z i ^ 2 = 0 := by
      refine le_antisymm ?_ hnn
      nlinarith [mul_nonneg ha hSz]
    have hz0 : ∀ i, z i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp hsum i
        (Finset.mem_univ _)
      exact (pow_eq_zero_iff two_ne_zero).mp this
    exact sub_eq_zero.mp (funext hz0)
  have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact ((Matrix.isUnit_iff_isUnit_det M).mp hu).ne_zero

/-- Continuity of `u ↦ Tcand (ϱ + u²)` for `ϱ > 0`. -/
private lemma kern_Tcand_continuous {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Continuous (fun u : ℝ => Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
  have hp := spectral_mem_classK F h
  have hF := Fw_admissible hw.1
  have hs : Continuous (fun u : ℝ => ϱ + u ^ 2) := by fun_prop
  have hspos : ∀ u : ℝ, 0 < ϱ + u ^ 2 := fun u => by positivity
  have hcontP := (thm_app_de_branch_ii hF hC hγ).1
  have hS : Continuous (fun u : ℝ => branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
    have := hcontP.comp_continuous (g := fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
      branchSol (Fw w) p.2.1 p.2.2 p.1)
      (f := fun u : ℝ => (ϱ + u ^ 2, (specOutFM F, specInFM F)))
      (hs.prodMk continuous_const) (fun u => ⟨hspos u, hp⟩)
    exact this
  have c1 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).1) :=
    continuous_fst.comp hS
  have c2 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.1) :=
    continuous_fst.comp (continuous_snd.comp hS)
  have c3 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1) :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hS))
  have c4 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hS))
  have hq : Continuous (fun u : ℝ => branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
    unfold branchQ
    exact (hs.mul c1).mul c2
  have hqnn : ∀ u : ℝ, 0 ≤ branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2) := fun u => by
    obtain ⟨h1, h2, -, -⟩ := kern_isBranch_nonneg
      (branchSol_spec hF hC hγ hp (hspos u))
    unfold branchQ
    exact mul_nonneg (mul_nonneg (hspos u).le h1) h2
  have hL : Continuous (fun u : ℝ => Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2))) := by
    have hLc := (lem_app_de_scalar_ii hw.1).2.2.2.1
    exact hLc.comp_continuous hq (fun u => hqnn u)
  have hR : Continuous (fun u : ℝ => Rbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + u ^ 2)) := by
    unfold Rbar
    rw [continuous_iff_continuousAt]
    intro u
    have hM : Continuous (fun u : ℝ => (ϱ + u ^ 2) • (1 : Mat m m) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 • F.C.Sout) :=
      (hs.smul continuous_const).add (c3.smul continuous_const)
    obtain ⟨-, -, h3, -⟩ := kern_isBranch_nonneg (branchSol_spec hF hC hγ hp (hspos u))
    have hdet := kern_isUnit_det F.C.Sout F.C.psdOut h3 (hspos u)
    have hinv : ContinuousAt Inv.inv ((ϱ + u ^ 2) • (1 : Mat m m) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 • F.C.Sout) :=
      continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
    exact ContinuousAt.comp (g := Inv.inv) (f := fun u : ℝ => (ϱ + u ^ 2) • (1 : Mat m m) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 • F.C.Sout) hinv
        hM.continuousAt
  have hRt : Continuous (fun u : ℝ => Rtbar (Fw w) (specOutFM F) (specInFM F) F.C (ϱ + u ^ 2)) := by
    unfold Rtbar
    rw [continuous_iff_continuousAt]
    intro u
    have hM : Continuous (fun u : ℝ => (ϱ + u ^ 2) • (1 : Mat n n) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2 • F.C.Sin) :=
      (hs.smul continuous_const).add (c4.smul continuous_const)
    obtain ⟨-, -, -, h4⟩ := kern_isBranch_nonneg (branchSol_spec hF hC hγ hp (hspos u))
    have hdet := kern_isUnit_det F.C.Sin F.C.psdIn h4 (hspos u)
    have hinv : ContinuousAt Inv.inv ((ϱ + u ^ 2) • (1 : Mat n n) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2 • F.C.Sin) :=
      continuousAt_matrix_inv _ (by
        rw [Ring.inverse_eq_inv']; exact continuousAt_inv₀ hdet)
    exact ContinuousAt.comp (g := Inv.inv) (f := fun u : ℝ => (ϱ + u ^ 2) • (1 : Mat n n) +
        (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2 • F.C.Sin) hinv
        hM.continuousAt
  unfold Tcand
  exact ((hs.mul hL).smul ((hR.matrix_mul continuous_const).matrix_mul hRt))

/-- `∫₀^∞ du/(ϱ + u²) = π/(2√ϱ)`, with integrability. -/
private lemma kern_ioi_integral {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2)⁻¹) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2)⁻¹ = Real.pi / 2 * (Real.sqrt ϱ)⁻¹ := by
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hb : 0 < (Real.sqrt ϱ)⁻¹ := inv_pos.mpr hr
  have hfun : (fun u : ℝ => (ϱ + u ^ 2)⁻¹) =
      fun u => ϱ⁻¹ * (fun x : ℝ => (1 + x ^ 2)⁻¹) ((Real.sqrt ϱ)⁻¹ * u) := by
    funext u
    have : ϱ + u ^ 2 = ϱ * (1 + ((Real.sqrt ϱ)⁻¹ * u) ^ 2) := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hϱ.le]; field_simp
    rw [this, mul_inv]
  have hint : IntegrableOn (fun x : ℝ => (1 + x ^ 2)⁻¹) (Ioi 0) :=
    integrable_inv_one_add_sq.integrableOn
  refine ⟨?_, ?_⟩
  · rw [hfun]
    refine Integrable.const_mul ?_ _
    exact (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb).mpr
      (by simpa using hint)
  · rw [hfun, integral_const_mul, integral_comp_mul_left_Ioi (fun x : ℝ => (1 + x ^ 2)⁻¹) 0 hb]
    simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul,
      inv_inv]
    have : ϱ⁻¹ = (Real.sqrt ϱ)⁻¹ * (Real.sqrt ϱ)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hϱ.le]
    rw [this]
    field_simp

/-- Cauchy–Schwarz for the entrywise pairing of matrices. -/
private lemma kern_dot_le {p q : ℕ} (a b : Mat p q) :
    ∑ i, ∑ j, a i j * b i j ≤ fro a * fro b := by
  have h1 : ∑ i, ∑ j, a i j * b i j = ∑ x : Fin p × Fin q, a x.1 x.2 * b x.1 x.2 := by
    rw [Fintype.sum_prod_type]
  have hsq : (∑ x : Fin p × Fin q, a x.1 x.2 * b x.1 x.2) ^ 2 ≤
      (∑ x : Fin p × Fin q, a x.1 x.2 ^ 2) * (∑ x : Fin p × Fin q, b x.1 x.2 ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have ea : ∑ x : Fin p × Fin q, a x.1 x.2 ^ 2 = fro a ^ 2 := by
    rw [kern_sq_sum_eq, Fintype.sum_prod_type]
  have eb : ∑ x : Fin p × Fin q, b x.1 x.2 ^ 2 = fro b ^ 2 := by
    rw [kern_sq_sum_eq, Fintype.sum_prod_type]
  rw [ea, eb, ← mul_pow] at hsq
  rw [h1]
  exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (kern_fro_nonneg a) (kern_fro_nonneg b))).2

private lemma kern_abs_le_fro {p q : ℕ} (a : Mat p q) (i : Fin p) (j : Fin q) :
    |a i j| ≤ fro a := by
  have h : a i j ^ 2 ≤ fro a ^ 2 := by
    rw [kern_sq_sum_eq]
    calc a i j ^ 2 ≤ ∑ j', a i j' ^ 2 :=
          Finset.single_le_sum (f := fun j' => a i j' ^ 2) (fun _ _ => sq_nonneg _)
            (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', a i' j' ^ 2 :=
          Finset.single_le_sum (f := fun i' => ∑ j', a i' j' ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  exact abs_le_of_sq_le_sq h (kern_fro_nonneg a)

private lemma kern_sq_sum_eq' {p q : ℕ} (K : Mat p q) :
    fro K ^ 2 = ∑ i, ∑ j, K i j * K i j := by
  rw [kern_sq_sum_eq]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => sq _

/-- Pairing with a fixed array commutes with the integral. -/
private lemma kern_int_pair {p q : ℕ} (g : Fin p → Fin q → ℝ) (T : ℝ → Fin p → Fin q → ℝ)
    (hint : ∀ i j, IntegrableOn (fun u : ℝ => T u i j) (Ioi 0)) :
    IntegrableOn (fun u : ℝ => ∑ i, ∑ j, g i j * T u i j) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, g i j * T u i j = ∑ i, ∑ j, g i j * ∫ u in Ioi (0 : ℝ), T u i j := by
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _, ?_⟩
  rw [integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    (hint i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => (hint i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

private lemma kern_dot_symm {k : ℕ} (M : Mat k k) (hM : Mᵀ = M) (x y : Vec k) :
    dotProduct x (M *ᵥ y) = dotProduct (M *ᵥ x) y := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hM]

private lemma kern_symm_of_psd {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) : Sᵀ = S := by
  simpa using hS.isHermitian.eq

/-- `CFC.sqrt S` acts on an eigenvector of `S` by the square root of the eigenvalue. -/
private lemma kern_sqrt_eig {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {u : Vec k} {μ : ℝ}
    (hμ : 0 ≤ μ) (hu : S *ᵥ u = μ • u) : CFC.sqrt S *ᵥ u = Real.sqrt μ • u := by
  have h0 : 0 ≤ S := Matrix.nonneg_iff_posSemidef.mpr hS
  have hRp : (CFC.sqrt S).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
  have hRR : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h0
  have hsym : (CFC.sqrt S)ᵀ = CFC.sqrt S := kern_symm_of_psd _ hRp
  set R := CFC.sqrt S with hR
  have hRRu : R *ᵥ (R *ᵥ u) = μ • u := by rw [Matrix.mulVec_mulVec, hRR, hu]
  have hss := Real.mul_self_sqrt hμ
  rcases hμ.eq_or_lt with h | h
  · -- μ = 0
    have hd : dotProduct (R *ᵥ u) (R *ᵥ u) = 0 := by
      rw [← kern_dot_symm R hsym, hRRu, ← h]; simp
    have := dotProduct_self_eq_zero.mp hd
    rw [this, ← h]; simp
  · have hspos : 0 < Real.sqrt μ := Real.sqrt_pos.mpr h
    set y : Vec k := R *ᵥ u - Real.sqrt μ • u with hy
    have hRy : R *ᵥ y = (-Real.sqrt μ) • y := by
      rw [hy, Matrix.mulVec_sub, Matrix.mulVec_smul, hRRu]
      ext i
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (-(u i)) * hss
    have hnn := hRp.dotProduct_mulVec_nonneg y
    rw [hRy, star_trivial, dotProduct_smul, smul_eq_mul] at hnn
    have hyy : dotProduct y y = 0 := by
      have h1 : 0 ≤ dotProduct y y := Finset.sum_nonneg fun i _ => mul_self_nonneg _
      nlinarith
    have := dotProduct_self_eq_zero.mp hyy
    exact sub_eq_zero.mp this

/-- Eigenvector action of `(s • 1 + a • S)⁻¹`. -/
private lemma kern_inv_eig {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a s μ : ℝ}
    (ha : 0 ≤ a) (hs : 0 < s) (hμ : 0 ≤ μ) {u : Vec k} (hu : S *ᵥ u = μ • u) :
    (s • (1 : Mat k k) + a • S)⁻¹ *ᵥ u = (s + a * μ)⁻¹ • u := by
  set M : Mat k k := s • (1 : Mat k k) + a • S with hM
  have hdet := kern_isUnit_det S hS ha hs
  have hMu : M *ᵥ u = (s + a * μ) • u := by
    rw [hM, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hu,
      smul_smul, add_smul]
  have hpos : 0 < s + a * μ := by positivity
  have h1 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hdet)
  have h2 : u = (s + a * μ) • (M⁻¹ *ᵥ u) := by
    calc u = (M⁻¹ * M) *ᵥ u := by rw [h1, Matrix.one_mulVec]
      _ = M⁻¹ *ᵥ (M *ᵥ u) := by rw [Matrix.mulVec_mulVec]
      _ = _ := by rw [hMu, Matrix.mulVec_smul]
  calc M⁻¹ *ᵥ u = (s + a * μ)⁻¹ • ((s + a * μ) • (M⁻¹ *ᵥ u)) := by
        rw [smul_smul, inv_mul_cancel₀ hpos.ne', one_smul]
    _ = (s + a * μ)⁻¹ • u := by rw [← h2]

private lemma kern_dot_mulVec {p q : ℕ} (X : Mat p q) (U : Vec p) (V : Vec q) :
    dotProduct U (X *ᵥ V) = ∑ i, ∑ j, (U i * V j) * X i j := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- `thm:app-drift-mean`, first claim (helper of card §5, L-C.4): for `ϱ > 0`, every entry of the
integrand of `eqn:app-drift-Gbar` is integrable on `(0,∞)` in `u`, and
`‖Ḡ_ϱ‖_F ≤ C_Σ/√ϱ`. The remaining claims are L-C.10's. Snapshot `cr-2026-10-23`. Source,
verbatim:
```
\begin{theorem}[Regularized mean]\label{thm:app-drift-mean}
Under \cref{assum:app-setup-regime}, the integral \cref{eqn:app-drift-Gbar}
converges absolutely in Frobenius norm, with
$\norm{\Gtildebar_\ridge}_\F\le C_\Sigma/\sqrt\ridge$, and
\begin{equation}\label{eqn:app-drift-mean}
\varepsilon_B\defeq\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge}_\F\longrightarrow0 .
\end{equation}
Consequently, for every deterministic $V\in\R^{\Nout\times\Nin}$,
\begin{equation}\label{eqn:app-drift-pairing}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\big|\big\langle V,\EE\,\Qridge\ridge(\Mt)-\Gtildebar_\ridge\big\rangle\big|\le\norm V_\F\,\varepsilon_B,
\qquad \langle V,W\rangle\defeq\Tr(VW^\T).
\end{equation}
\end{theorem}
```
-/
theorem gbar_integrable_bound {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (∀ i j, IntegrableOn (fun u : ℝ => Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j) (Ioi 0)) ∧
      fro (Gbar w F (specOutFM F) (specInFM F) ϱ) ≤ CS / Real.sqrt ϱ := by
  have hcont := kern_Tcand_continuous hC hγ hw F h hϱ
  obtain ⟨hI, hIv⟩ := kern_ioi_integral hϱ
  have hpt : ∀ u : ℝ, fro (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ≤
      CS * (ϱ + u ^ 2)⁻¹ := fun u => by
    have := thm_app_drift_mixed_ii_T hC hγ hw F h (s := ϱ + u ^ 2) (by positivity)
    rwa [div_eq_mul_inv] at this
  have hint : ∀ i j, IntegrableOn
      (fun u : ℝ => Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j) (Ioi 0) := by
    intro i j
    refine Integrable.mono' (hI.const_mul CS) ?_ ?_
    · exact (((continuous_apply j).comp ((continuous_apply i).comp hcont))).aestronglyMeasurable
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall fun u _ => ?_)
      rw [Real.norm_eq_abs]
      exact (kern_abs_le_fro _ i j).trans (hpt u)
  refine ⟨hint, ?_⟩
  set G := Gbar w F (specOutFM F) (specInFM F) ϱ with hG
  set c : ℝ := CS / Real.sqrt ϱ with hc
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have hc0 : 0 ≤ c := by positivity
  have hGij : ∀ i j, G i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
      Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j := fun i j => rfl
  obtain ⟨hpi, hpe⟩ := kern_int_pair (fun i j => G i j)
    (fun u i j => Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j) hint
  have hsumint : ∑ i, ∑ j, G i j * G i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
      ∑ i, ∑ j, G i j * Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j := by
    rw [hpe, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    nth_rw 2 [hGij i j]
    ring
  have hle : ∫ u in Ioi (0 : ℝ),
      ∑ i, ∑ j, G i j * Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j ≤
      ∫ u in Ioi (0 : ℝ), fro G * CS * (ϱ + u ^ 2)⁻¹ := by
    refine setIntegral_mono_on hpi (hI.const_mul (fro G * CS)) measurableSet_Ioi fun u _ => ?_
    calc _ ≤ fro G * fro (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) :=
            kern_dot_le _ _
        _ ≤ fro G * (CS * (ϱ + u ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left (hpt u) (kern_fro_nonneg _)
        _ = _ := by ring
  rw [integral_const_mul, hIv] at hle
  have hpi0 : 0 < Real.pi := Real.pi_pos
  have hmain : fro G ^ 2 ≤ fro G * c := by
    rw [kern_sq_sum_eq' G]
    calc ∑ i, ∑ j, G i j * G i j = (2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
          ∑ i, ∑ j, G i j * Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i j := hsumint
      _ ≤ (2 / Real.pi) * (fro G * CS * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹)) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = fro G * c := by rw [hc]; field_simp
  by_contra hcon
  rw [not_le] at hcon
  nlinarith [kern_fro_nonneg G]

/-- `cor:app-drift-kernel`(i), diagonal helper (card §5): in the eigenbases of `Σ_out`, `Σ_in`,
`√(μ_i λ_j) · u_iᵀ Ḡ_ϱ v_j = √2 · 𝔡(μ_i,λ_j) · u_iᵀ Â v_j`. This is the identity behind
`eqn:app-drift-projected`; the remaining clauses of (i) are L-C.10's. Snapshot `cr-2026-10-23`.
Source, verbatim:
```
\begin{corollary}[The drift kernel]\label{cor:app-drift-kernel}
Under \cref{assum:app-setup-regime}, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update and put $(E_\ridge)_{ij}\defeq u_i^\T\big(\EE\Gtilde-\Gtildebar_\ridge\big)v_j$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ and every $\ridge\in[\ridge_-,\ridge_+]$,
\begin{equation}\label{eqn:app-drift-projected}
\EE\big[u_i^\T\Gtilde v_j\big]=\frac{\sqrt2\,\mathfrak d(\mu_i,\lambda_j)}{\sqrt{2\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij}
=\frac{\mathfrak d(\mu_i,\lambda_j)}{\sqrt{\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij},
\end{equation}
and $\sup_{\ridge\in[\ridge_-,\ridge_+]}\big(\sum_{i,j}(E_\ridge)_{ij}^2\big)^{1/2}=\varepsilon_B\to0$.
Consequently the frozen-state drift \cref{eqn:app-setup-DV} of the update
$\Gtilde$ is
\begin{equation}\label{eqn:app-drift-Dij}
\cD_{ij}(t)=\frac{\mathfrak d_{ij}}{\sqrt{\cR(t)}}\,\CMscr Q_{ij}(t)+(u_i^\T\Dt v_j)(E_\ridge)_{ij},
\qquad \mathfrak d_{ij}\defeq\mathfrak d(\mu_i,\lambda_j),
\end{equation}
and for every bounded function $\phi$ on $[0,\infty)^2$,
\begin{equation}\label{eqn:app-drift-tested}
\Big|\sum_{i,j}\phi(\mu_i,\lambda_j)\,(u_i^\T\Dt v_j)\,(E_\ridge)_{ij}\Big|\le\norm\phi_\infty\,\norm{\Dt}_\F\,\varepsilon_B .
\end{equation}
\item For every $\ridge\in[\ridge_-,\ridge_+]$ the function $\mathfrak d$ is
continuous on $[0,\infty)^2$, vanishes when $\mu=0$ or $\lambda=0$, and satisfies
\begin{equation}\label{eqn:app-drift-kernel-bounds}
0\le\mathfrak d(\mu,\lambda)\le\frac{\mu\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\mu\mathfrak d(\mu,\lambda)}\le\frac{\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\lambda\mathfrak d(\mu,\lambda)}\le\frac{\mu}{\sqrt{2\ridge}},
\end{equation}
with one-sided derivatives at $0$; in particular $\mathfrak d$ is Lipschitz on
$[0,C_\Sigma]^2$ with constant $C_\Sigma/\sqrt{2\ridge_-}$ in each variable.
\end{enumerate}
\end{corollary}
```
-/
theorem kernel_diag_gbar {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (SD : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) (j : Fin n) :
    Real.sqrt (SD.μ i * SD.lam j) *
        dotProduct (SD.u i) (Gbar w F (specOutFM F) (specInFM F) ϱ *ᵥ SD.v j) =
      Real.sqrt 2 * kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) (SD.lam j) *
        dotProduct (SD.u i) (F.A *ᵥ SD.v j) := by
  have hp := spectral_mem_classK F h
  have hF := Fw_admissible hw.1
  have hμ := μ_nonneg SD i
  have hl := lam_nonneg SD j
  have hcont := kern_Tcand_continuous hC hγ hw F h hϱ
  obtain ⟨hint, -⟩ := gbar_integrable_bound hC hγ hw F h hϱ
  set μ := SD.μ i with hμdef
  set U := SD.u i with hU
  set V := SD.v j with hV
  set d := dotProduct U (F.A *ᵥ V) with hd
  have e3 : ∀ {p q r t : ℕ} (P : Mat p q) (Q : Mat q r) (R : Mat r t) (x : Vec t),
      (P * Q * R) *ᵥ x = P *ᵥ (Q *ᵥ (R *ᵥ x)) := fun P Q R x => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hpt : ∀ t : ℝ, dotProduct U (Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2) *ᵥ V) =
      (Real.sqrt μ * Real.sqrt (SD.lam j) * d) * ((ϱ + t ^ 2) *
        Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + t ^ 2)) *
        ((ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.1 * μ)⁻¹ *
        (ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.2 *
          SD.lam j)⁻¹)) := by
    intro t
    have hz : 0 < ϱ + t ^ 2 := by positivity
    obtain ⟨-, -, h3, h4⟩ := kern_isBranch_nonneg (branchSol_spec hF hC hγ hp hz)
    set z := ϱ + t ^ 2 with hzdef
    set a := (branchSol (Fw w) (specOutFM F) (specInFM F) z).2.2.1 with ha
    set b := (branchSol (Fw w) (specOutFM F) (specInFM F) z).2.2.2 with hb
    have hRt : Rtbar (Fw w) (specOutFM F) (specInFM F) F.C z *ᵥ V = (z + b * SD.lam j)⁻¹ • V :=
      kern_inv_eig F.C.Sin F.C.psdIn h4 hz hl (eig_v SD j)
    have hrI : rIn F.C *ᵥ V = Real.sqrt (SD.lam j) • V :=
      kern_sqrt_eig F.C.Sin F.C.psdIn hl (eig_v SD j)
    have hrO : rOut F.C *ᵥ U = Real.sqrt μ • U :=
      kern_sqrt_eig F.C.Sout F.C.psdOut hμ (eig_u SD i)
    have hRU : Rbar (Fw w) (specOutFM F) (specInFM F) F.C z *ᵥ U = (z + a * μ)⁻¹ • U :=
      kern_inv_eig F.C.Sout F.C.psdOut h3 hz hμ (eig_u SD i)
    have hsymR : (Rbar (Fw w) (specOutFM F) (specInFM F) F.C z)ᵀ =
        Rbar (Fw w) (specOutFM F) (specInFM F) F.C z := by
      unfold Rbar
      rw [Matrix.transpose_nonsing_inv]
      congr 1
      rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
        Matrix.transpose_one, kern_symm_of_psd _ F.C.psdOut]
    have hsymO : (rOut F.C)ᵀ = rOut F.C := kern_symm_of_psd _
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _))
    unfold Tcand
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    unfold EG
    rw [e3, e3, hRt]
    simp only [Matrix.mulVec_smul, hrI, dotProduct_smul, smul_eq_mul]
    rw [kern_dot_symm _ hsymR, hRU]
    simp only [smul_dotProduct, smul_eq_mul]
    rw [kern_dot_symm _ hsymO, hrO]
    simp only [smul_dotProduct, smul_eq_mul]
    rw [hd]
    ring
  set z : ℝ → ℝ := fun t => ϱ + t ^ 2 with hzf
  set f : ℝ → ℝ := fun t => (z t) * Lw w (branchQ w (specOutFM F) (specInFM F) (z t)) *
    ((z t + (branchSol (Fw w) (specOutFM F) (specInFM F) (z t)).2.2.1 * μ)⁻¹ *
      (z t + (branchSol (Fw w) (specOutFM F) (specInFM F) (z t)).2.2.2 * SD.lam j)⁻¹) with hf
  obtain ⟨-, hpe⟩ := kern_int_pair (fun i' j' => U i' * V j')
    (fun t i' j' => Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2) i' j') hint
  have hG : dotProduct U (Gbar w F (specOutFM F) (specInFM F) ϱ *ᵥ V) =
      (2 / Real.pi) * ((Real.sqrt μ * Real.sqrt (SD.lam j) * d) * ∫ t in Ioi (0 : ℝ), f t) := by
    have h1 : ∫ t in Ioi (0 : ℝ), ∑ i', ∑ j', (U i' * V j') *
        Tcand w F (specOutFM F) (specInFM F) (ϱ + t ^ 2) i' j' =
        (Real.sqrt μ * Real.sqrt (SD.lam j) * d) * ∫ t in Ioi (0 : ℝ), f t := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      simp only
      rw [← kern_dot_mulVec]
      exact hpt t
    rw [← h1, hpe, kern_dot_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    show _ = _
    change (U i' * V j') * ((2 / Real.pi) * ∫ u in Ioi (0 : ℝ),
      Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) i' j') = _
    ring
  have hK : kernel w (specOutFM F) (specInFM F) ϱ μ (SD.lam j) =
      (Real.sqrt 2 / Real.pi) * (μ * SD.lam j * ∫ t in Ioi (0 : ℝ), f t) := by
    unfold kernel
    congr 1
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf, hzf]
    have hz : 0 < ϱ + t ^ 2 := by positivity
    obtain ⟨-, -, h3, h4⟩ := kern_isBranch_nonneg (branchSol_spec hF hC hγ hp hz)
    have h5 : 0 < ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.1 * μ := by
      have := mul_nonneg h3 hμ; linarith
    have h6 : 0 < ϱ + t ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + t ^ 2)).2.2.2 * SD.lam j := by
      have := mul_nonneg h4 hl; linarith
    field_simp
  rw [hG, hK]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hm : Real.sqrt (μ * SD.lam j) = Real.sqrt μ * Real.sqrt (SD.lam j) := Real.sqrt_mul hμ _
  have hμs : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ
  have hls : Real.sqrt (SD.lam j) * Real.sqrt (SD.lam j) = SD.lam j := Real.mul_self_sqrt hl
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  rw [hm]
  field_simp
  rw [Real.sq_sqrt hμ, Real.sq_sqrt hl, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  ring

/-- Branch data for the drift kernel (continuity in `u` and signs), extracted from the proof of
`kern_Tcand_continuous`. -/
private lemma kg_branch {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1) ∧
    Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2) ∧
    Continuous (fun u : ℝ => Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2))) ∧
    (∀ u : ℝ, 0 ≤ (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1) ∧
    (∀ u : ℝ, 0 ≤ (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2) ∧
    (∀ u : ℝ, 0 ≤ Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ∧
      Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ≤ 1) := by
  have hp := spectral_mem_classK F h
  have hF := Fw_admissible hw.1
  have hs : Continuous (fun u : ℝ => ϱ + u ^ 2) := by fun_prop
  have hspos : ∀ u : ℝ, 0 < ϱ + u ^ 2 := fun u => by positivity
  have hcontP := (thm_app_de_branch_ii hF hC hγ).1
  have hS : Continuous (fun u : ℝ => branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
    have := hcontP.comp_continuous (g := fun p : ℝ × (FiniteMeasure ℝ × FiniteMeasure ℝ) =>
      branchSol (Fw w) p.2.1 p.2.2 p.1)
      (f := fun u : ℝ => (ϱ + u ^ 2, (specOutFM F, specInFM F)))
      (hs.prodMk continuous_const) (fun u => ⟨hspos u, hp⟩)
    exact this
  have c1 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).1) :=
    continuous_fst.comp hS
  have c2 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.1) :=
    continuous_fst.comp (continuous_snd.comp hS)
  have c3 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1) :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp hS))
  have c4 : Continuous (fun u : ℝ => (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2) :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp hS))
  have hq : Continuous (fun u : ℝ => branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) := by
    unfold branchQ
    exact (hs.mul c1).mul c2
  have hqnn : ∀ u : ℝ, 0 ≤ branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2) := fun u => by
    obtain ⟨h1, h2, -, -⟩ := kern_isBranch_nonneg
      (branchSol_spec hF hC hγ hp (hspos u))
    unfold branchQ
    exact mul_nonneg (mul_nonneg (hspos u).le h1) h2
  have hL : Continuous (fun u : ℝ => Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2))) := by
    have hLc := (lem_app_de_scalar_ii hw.1).2.2.2.1
    exact hLc.comp_continuous hq (fun u => hqnn u)
  refine ⟨c3, c4, hL, fun u => ?_, fun u => ?_, fun u => kern_Lw_bounds hw (hqnn u)⟩
  · exact (kern_isBranch_nonneg (branchSol_spec hF hC hγ hp (hspos u))).2.2.1
  · exact (kern_isBranch_nonneg (branchSol_spec hF hC hγ hp (hspos u))).2.2.2

/-- Pointwise bounds `0 ≤ integrand ≤ x y /(ϱ+u²)` for the generic kernel integrand. -/
private lemma kg_bounds {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (ha : ∀ u, 0 ≤ a u)
    (hb : ∀ u, 0 ≤ b u) (hL0 : ∀ u, 0 ≤ L u) (hL1 : ∀ u, L u ≤ 1) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) (u : ℝ) :
    0 ≤ (ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) ∧
      (ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))
        ≤ x * y * (ϱ + u ^ 2)⁻¹ := by
  have hz : 0 < ϱ + u ^ 2 := by positivity
  have h1 : 0 < ϱ + u ^ 2 + a u * x := by
    have := mul_nonneg (ha u) hx
    linarith
  have h2 : 0 < ϱ + u ^ 2 + b u * y := by
    have := mul_nonneg (hb u) hy
    linarith
  have hxy : 0 ≤ x * y := mul_nonneg hx hy
  have hnum : 0 ≤ (ϱ + u ^ 2) * L u * x * y :=
    mul_nonneg (mul_nonneg (mul_nonneg hz.le (hL0 u)) hx) hy
  refine ⟨div_nonneg hnum (mul_pos h1 h2).le, ?_⟩
  rw [← div_eq_mul_inv, div_le_div_iff₀ (mul_pos h1 h2) hz]
  have hd : (ϱ + u ^ 2) * (ϱ + u ^ 2) ≤ (ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y) :=
    mul_le_mul (by linarith [mul_nonneg (ha u) hx]) (by linarith [mul_nonneg (hb u) hy])
      hz.le h1.le
  have hn : (ϱ + u ^ 2) * L u * x * y * (ϱ + u ^ 2) ≤ x * y * ((ϱ + u ^ 2) * (ϱ + u ^ 2)) := by
    have e : (ϱ + u ^ 2) * L u * x * y * (ϱ + u ^ 2) =
        (x * y * ((ϱ + u ^ 2) * (ϱ + u ^ 2))) * L u := by ring
    rw [e]
    exact mul_le_of_le_one_right (mul_nonneg hxy (mul_nonneg hz.le hz.le)) (hL1 u)
  calc (ϱ + u ^ 2) * L u * x * y * (ϱ + u ^ 2)
      ≤ x * y * ((ϱ + u ^ 2) * (ϱ + u ^ 2)) := hn
    _ ≤ x * y * ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) :=
        mul_le_mul_of_nonneg_left hd hxy

/-- Continuity in `u` of the generic kernel integrand. -/
private lemma kg_ucont {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (hac : Continuous a)
    (hbc : Continuous b) (hLc : Continuous L) (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Continuous (fun u : ℝ => (ϱ + u ^ 2) * L u * x * y /
      ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) := by
  refine Continuous.div ?_ ?_ ?_
  · fun_prop
  · fun_prop
  · intro u
    have h1 : 0 < ϱ + u ^ 2 + a u * x := by
      have := mul_nonneg (ha u) hx
      linarith [sq_nonneg u]
    have h2 : 0 < ϱ + u ^ 2 + b u * y := by
      have := mul_nonneg (hb u) hy
      linarith [sq_nonneg u]
    exact (mul_pos h1 h2).ne'

/-- Integrability on `(0,∞)` of the generic kernel integrand. -/
private lemma kg_integrable {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (hac : Continuous a)
    (hbc : Continuous b) (hLc : Continuous L) (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    (hL0 : ∀ u, 0 ≤ L u) (hL1 : ∀ u, L u ≤ 1) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    IntegrableOn (fun u : ℝ => (ϱ + u ^ 2) * L u * x * y /
      ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) (Ioi 0) := by
  have hg : IntegrableOn (fun u : ℝ => x * y * (ϱ + u ^ 2)⁻¹) (Ioi 0) :=
    (kern_ioi_integral hϱ).1.const_mul (x * y)
  refine Integrable.mono' hg (kg_ucont hϱ hac hbc hLc ha hb hx hy).aestronglyMeasurable.restrict ?_
  exact Filter.Eventually.of_forall fun u => by
    rw [Real.norm_of_nonneg (kg_bounds hϱ ha hb hL0 hL1 hx hy u).1]
    exact (kg_bounds hϱ ha hb hL0 hL1 hx hy u).2

/-- Sign and `ϱ`-uniform upper bound for the generic kernel integral. -/
private lemma kg_int_bounds {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (ha : ∀ u, 0 ≤ a u)
    (hb : ∀ u, 0 ≤ b u) (hL0 : ∀ u, 0 ≤ L u) (hL1 : ∀ u, L u ≤ 1) {x y : ℝ} (hx : 0 ≤ x)
    (hy : 0 ≤ y) :
    0 ≤ ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2) * L u * x * y /
        ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) ∧
      ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2) * L u * x * y /
        ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))
        ≤ x * y * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹) := by
  constructor
  · exact integral_nonneg fun u => (kg_bounds hϱ ha hb hL0 hL1 hx hy u).1
  · have hg : IntegrableOn (fun u : ℝ => x * y * (ϱ + u ^ 2)⁻¹) (Ioi 0) :=
      (kern_ioi_integral hϱ).1.const_mul (x * y)
    calc _ ≤ ∫ u in Ioi (0 : ℝ), x * y * (ϱ + u ^ 2)⁻¹ :=
          integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun u => (kg_bounds hϱ ha hb hL0 hL1 hx hy u).1)
            hg
            (Filter.Eventually.of_forall fun u => (kg_bounds hϱ ha hb hL0 hL1 hx hy u).2)
      _ = x * y * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹) := by
          rw [integral_const_mul, (kern_ioi_integral hϱ).2]

/-- Joint continuity of the generic kernel integral on `[0,∞)²`. -/
private lemma kg_cont {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (hac : Continuous a)
    (hbc : Continuous b) (hLc : Continuous L) (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    (hL0 : ∀ u, 0 ≤ L u) (hL1 : ∀ u, L u ≤ 1) {p0 : ℝ × ℝ} (hp0 : 0 ≤ p0.1 ∧ 0 ≤ p0.2) :
    ContinuousWithinAt (fun p : ℝ × ℝ => ∫ u in Ioi (0 : ℝ),
        (ϱ + u ^ 2) * L u * p.1 * p.2 / ((ϱ + u ^ 2 + a u * p.1) * (ϱ + u ^ 2 + b u * p.2)))
      (Ici 0 ×ˢ Ici 0) p0 := by
  have hA : ∀ᶠ p in 𝓝 p0, p.1 < p0.1 + 1 :=
    (continuous_fst.tendsto p0).eventually (gt_mem_nhds (by linarith [hp0.1]))
  have hB : ∀ᶠ p in 𝓝 p0, p.2 < p0.2 + 1 :=
    (continuous_snd.tendsto p0).eventually (gt_mem_nhds (by linarith [hp0.2]))
  refine continuousWithinAt_of_dominated
    (F := fun (p : ℝ × ℝ) (u : ℝ) => (ϱ + u ^ 2) * L u * p.1 * p.2 /
      ((ϱ + u ^ 2 + a u * p.1) * (ϱ + u ^ 2 + b u * p.2)))
    (bound := fun u : ℝ => (p0.1 + 1) * (p0.2 + 1) * (ϱ + u ^ 2)⁻¹) ?_ ?_ ?_ ?_
  · refine eventually_nhdsWithin_of_forall fun (p : ℝ × ℝ) hp => ?_
    have hp1 : 0 ≤ p.1 := Set.mem_Ici.mp (Set.mem_prod.mp hp).1
    have hp2 : 0 ≤ p.2 := Set.mem_Ici.mp (Set.mem_prod.mp hp).2
    exact (kg_ucont hϱ hac hbc hLc ha hb hp1 hp2).aestronglyMeasurable.restrict
  · filter_upwards [nhdsWithin_le_nhds (hA.and hB), self_mem_nhdsWithin] with p hp hpS
    have hp1 : 0 ≤ p.1 := Set.mem_Ici.mp (Set.mem_prod.mp hpS).1
    have hp2 : 0 ≤ p.2 := Set.mem_Ici.mp (Set.mem_prod.mp hpS).2
    refine Filter.Eventually.of_forall fun u => ?_
    have hb0 := kg_bounds hϱ ha hb hL0 hL1 hp1 hp2 u
    rw [Real.norm_of_nonneg hb0.1]
    refine hb0.2.trans ?_
    have hz : 0 < ϱ + u ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right (mul_le_mul hp.1.le hp.2.le hp2 (by linarith [hp0.1]))
      (inv_nonneg.mpr hz.le)
  · exact (kern_ioi_integral hϱ).1.const_mul ((p0.1 + 1) * (p0.2 + 1))
  · refine Filter.Eventually.of_forall fun u => ?_
    have h1 : 0 < ϱ + u ^ 2 + a u * p0.1 := by
      have := mul_nonneg (ha u) hp0.1
      linarith [sq_nonneg u]
    have h2 : 0 < ϱ + u ^ 2 + b u * p0.2 := by
      have := mul_nonneg (hb u) hp0.2
      linarith [sq_nonneg u]
    refine ContinuousAt.continuousWithinAt (ContinuousAt.div ?_ ?_ (mul_pos h1 h2).ne')
    · fun_prop
    · fun_prop

/-- Derivative in the first slot of the generic kernel integral, with the uniform bound
`|d| ≤ y ∫ (ϱ+u²)⁻¹`. The derivative is taken along `Ici 0` (one-sided at `0`). -/
private lemma kg_hasDeriv {ϱ : ℝ} (hϱ : 0 < ϱ) {a b L : ℝ → ℝ} (hac : Continuous a)
    (hbc : Continuous b) (hLc : Continuous L) (ha : ∀ u, 0 ≤ a u) (hb : ∀ u, 0 ≤ b u)
    (hL0 : ∀ u, 0 ≤ L u) (hL1 : ∀ u, L u ≤ 1) {x0 y : ℝ} (hx0 : 0 ≤ x0) (hy : 0 ≤ y) :
    ∃ d : ℝ, HasDerivWithinAt (fun x => ∫ u in Ioi (0 : ℝ),
        (ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) d
        (Ici 0) x0 ∧
      |d| ≤ y * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹) := by
  -- pointwise derivative in `x`
  have hP1 : ∀ u t : ℝ, 0 ≤ t → HasDerivAt (fun x : ℝ =>
      (ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)))
      ((ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) /
        ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2)) t := by
    intro u t ht
    have hz : 0 < ϱ + u ^ 2 := by positivity
    have hK : 0 < ϱ + u ^ 2 + b u * y := by
      have := mul_nonneg (hb u) hy
      linarith [sq_nonneg u]
    have hT : 0 < ϱ + u ^ 2 + a u * t := by
      have := mul_nonneg (ha u) ht
      linarith [sq_nonneg u]
    have hA : HasDerivAt (fun x : ℝ => (ϱ + u ^ 2) * L u * x * y)
        ((ϱ + u ^ 2) * L u * 1 * y) t :=
      ((hasDerivAt_id' t).const_mul ((ϱ + u ^ 2) * L u)).mul_const y
    have hB : HasDerivAt (fun x : ℝ => ϱ + u ^ 2 + a u * x) (a u * 1) t :=
      ((hasDerivAt_id' t).const_mul (a u)).const_add (ϱ + u ^ 2)
    have hden := hB.mul_const (ϱ + u ^ 2 + b u * y)
    have hq := hA.div hden (mul_pos hT hK).ne'
    convert hq using 1
    rw [div_eq_div_iff (mul_pos hK (pow_pos hT 2)).ne' (pow_pos (mul_pos hT hK) 2).ne']
    ring
  -- uniform pointwise bound on the derivative
  have hP2 : ∀ u t : ℝ, 0 ≤ t → ‖(ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) /
        ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2)‖ ≤ y * (ϱ + u ^ 2)⁻¹ := by
    intro u t ht
    have hz : 0 < ϱ + u ^ 2 := by positivity
    have hK : 0 < ϱ + u ^ 2 + b u * y := by
      have := mul_nonneg (hb u) hy
      linarith [sq_nonneg u]
    have hT : 0 < ϱ + u ^ 2 + a u * t := by
      have := mul_nonneg (ha u) ht
      linarith [sq_nonneg u]
    have hQ : 0 < (ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2 :=
      mul_pos hK (pow_pos hT 2)
    have hNn : 0 ≤ (ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg hz.le (hL0 u)) hy) hz.le
    rw [Real.norm_of_nonneg (div_nonneg hNn hQ.le), ← div_eq_mul_inv,
      div_le_div_iff₀ hQ hz]
    have hTle : ϱ + u ^ 2 ≤ ϱ + u ^ 2 + a u * t := by linarith [mul_nonneg (ha u) ht]
    have hKle : ϱ + u ^ 2 ≤ ϱ + u ^ 2 + b u * y := by linarith [mul_nonneg (hb u) hy]
    have hTT : (ϱ + u ^ 2) * (ϱ + u ^ 2) ≤ (ϱ + u ^ 2 + a u * t) * (ϱ + u ^ 2 + a u * t) :=
      mul_le_mul hTle hTle hz.le hT.le
    have hQle : (ϱ + u ^ 2) * ((ϱ + u ^ 2) * (ϱ + u ^ 2)) ≤
        (ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2 := by
      rw [show (ϱ + u ^ 2 + a u * t) ^ 2 = (ϱ + u ^ 2 + a u * t) * (ϱ + u ^ 2 + a u * t) from
        sq _]
      exact mul_le_mul hKle hTT (mul_nonneg hz.le hz.le) hK.le
    calc (ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) * (ϱ + u ^ 2)
        = (y * ((ϱ + u ^ 2) * ((ϱ + u ^ 2) * (ϱ + u ^ 2)))) * L u := by ring
      _ ≤ y * ((ϱ + u ^ 2) * ((ϱ + u ^ 2) * (ϱ + u ^ 2))) :=
          mul_le_of_le_one_right (mul_nonneg hy (mul_nonneg hz.le (mul_nonneg hz.le hz.le)))
            (hL1 u)
      _ ≤ y * ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2) :=
          mul_le_mul_of_nonneg_left hQle hy
  -- Lipschitz bound in `x` for each `u`
  have hMVT : ∀ u t1 t2 : ℝ, 0 ≤ t1 → 0 ≤ t2 →
      ‖(ϱ + u ^ 2) * L u * t2 * y / ((ϱ + u ^ 2 + a u * t2) * (ϱ + u ^ 2 + b u * y)) -
          (ϱ + u ^ 2) * L u * t1 * y / ((ϱ + u ^ 2 + a u * t1) * (ϱ + u ^ 2 + b u * y))‖ ≤
        (y * (ϱ + u ^ 2)⁻¹) * ‖t2 - t1‖ := by
    intro u t1 t2 h1 h2
    exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x : ℝ => (ϱ + u ^ 2) * L u * x * y /
        ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)))
      (f' := fun t : ℝ => (ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) /
        ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * t) ^ 2))
      (s := Ici 0)
      (fun t ht => (hP1 u t (Set.mem_Ici.mp ht)).hasDerivWithinAt)
      (fun t ht => hP2 u t (Set.mem_Ici.mp ht))
      (convex_Ici 0) (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr h2)
  refine ⟨∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) /
      ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * x0) ^ 2), ?_, ?_⟩
  · rw [hasDerivWithinAt_iff_tendsto_slope]
    have hlim : Tendsto (fun x => ∫ u in Ioi (0 : ℝ),
        ((ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) -
          (ϱ + u ^ 2) * L u * x0 * y / ((ϱ + u ^ 2 + a u * x0) * (ϱ + u ^ 2 + b u * y))) /
          (x - x0)) (𝓝[Ici 0 \ {x0}] x0)
        (𝓝 (∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2) * L u * y * (ϱ + u ^ 2) /
          ((ϱ + u ^ 2 + b u * y) * (ϱ + u ^ 2 + a u * x0) ^ 2))) := by
      refine tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => y * (ϱ + u ^ 2)⁻¹)
        ?_ ?_ ((kern_ioi_integral hϱ).1.const_mul y) ?_
      · refine eventually_nhdsWithin_of_forall fun x hx => ?_
        have hxS : 0 ≤ x := Set.mem_Ici.mp hx.1
        exact ((((kg_ucont hϱ hac hbc hLc ha hb hxS hy).sub
          (kg_ucont hϱ hac hbc hLc ha hb hx0 hy)).div_const (x - x0))).aestronglyMeasurable.restrict
      · refine eventually_nhdsWithin_of_forall fun x hx => Filter.Eventually.of_forall fun u => ?_
        have hxS : 0 ≤ x := Set.mem_Ici.mp hx.1
        have hne : x - x0 ≠ 0 := sub_ne_zero.mpr (fun h => hx.2 h)
        rw [norm_div, div_le_iff₀ (norm_pos_iff.mpr hne)]
        exact hMVT u x0 x hx0 hxS
      · refine Filter.Eventually.of_forall fun u => ?_
        have hT := hasDerivWithinAt_iff_tendsto_slope.mp
          ((hP1 u x0 hx0).hasDerivWithinAt (s := Ici 0))
        exact hT.congr (fun x => slope_def_field _ _ _)
    have hEq : (fun x => ∫ u in Ioi (0 : ℝ),
        ((ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y)) -
          (ϱ + u ^ 2) * L u * x0 * y / ((ϱ + u ^ 2 + a u * x0) * (ϱ + u ^ 2 + b u * y))) /
          (x - x0)) =ᶠ[𝓝[Ici 0 \ {x0}] x0]
        slope (fun x => ∫ u in Ioi (0 : ℝ),
          (ϱ + u ^ 2) * L u * x * y / ((ϱ + u ^ 2 + a u * x) * (ϱ + u ^ 2 + b u * y))) x0 := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxS : 0 ≤ x := Set.mem_Ici.mp hx.1
      have hne : x - x0 ≠ 0 := sub_ne_zero.mpr (fun h => hx.2 h)
      rw [slope_def_field, integral_div,
        integral_sub (kg_integrable hϱ hac hbc hLc ha hb hL0 hL1 hxS hy)
          (kg_integrable hϱ hac hbc hLc ha hb hL0 hL1 hx0 hy)]
    exact Tendsto.congr' hEq hlim
  · rw [← Real.norm_eq_abs]
    calc _ ≤ ∫ u in Ioi (0 : ℝ), y * (ϱ + u ^ 2)⁻¹ :=
          norm_integral_le_of_norm_le ((kern_ioi_integral hϱ).1.const_mul y)
            (Filter.Eventually.of_forall fun u => hP2 u x0 hx0)
      _ = y * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹) := by
          rw [integral_const_mul, (kern_ioi_integral hϱ).2]

/-- `√2/π · x y ∫₀^∞ (ϱ+u²)⁻¹ du = x y /√(2ϱ)` (constant identity for the kernel bounds). -/
private lemma kg_const {ϱ : ℝ} (hϱ : 0 < ϱ) (x y : ℝ) :
    Real.sqrt 2 / Real.pi * (x * y * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹)) = x * y / Real.sqrt (2 * ϱ) := by
  have hr : 0 < Real.sqrt ϱ := Real.sqrt_pos.mpr hϱ
  have h2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hk : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp
  linear_combination (x * y) * hk

/-- `cor:app-drift-kernel`(ii), parts (a)–(d) of the source, with the continuity clause. Snapshot
`cr-2026-10-23`. Source, verbatim:
```
\begin{corollary}[The drift kernel]\label{cor:app-drift-kernel}
Under \cref{assum:app-setup-regime}, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update and put $(E_\ridge)_{ij}\defeq u_i^\T\big(\EE\Gtilde-\Gtildebar_\ridge\big)v_j$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ and every $\ridge\in[\ridge_-,\ridge_+]$,
\begin{equation}\label{eqn:app-drift-projected}
\EE\big[u_i^\T\Gtilde v_j\big]=\frac{\sqrt2\,\mathfrak d(\mu_i,\lambda_j)}{\sqrt{2\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij}
=\frac{\mathfrak d(\mu_i,\lambda_j)}{\sqrt{\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij},
\end{equation}
and $\sup_{\ridge\in[\ridge_-,\ridge_+]}\big(\sum_{i,j}(E_\ridge)_{ij}^2\big)^{1/2}=\varepsilon_B\to0$.
Consequently the frozen-state drift \cref{eqn:app-setup-DV} of the update
$\Gtilde$ is
\begin{equation}\label{eqn:app-drift-Dij}
\cD_{ij}(t)=\frac{\mathfrak d_{ij}}{\sqrt{\cR(t)}}\,\CMscr Q_{ij}(t)+(u_i^\T\Dt v_j)(E_\ridge)_{ij},
\qquad \mathfrak d_{ij}\defeq\mathfrak d(\mu_i,\lambda_j),
\end{equation}
and for every bounded function $\phi$ on $[0,\infty)^2$,
\begin{equation}\label{eqn:app-drift-tested}
\Big|\sum_{i,j}\phi(\mu_i,\lambda_j)\,(u_i^\T\Dt v_j)\,(E_\ridge)_{ij}\Big|\le\norm\phi_\infty\,\norm{\Dt}_\F\,\varepsilon_B .
\end{equation}
\item For every $\ridge\in[\ridge_-,\ridge_+]$ the function $\mathfrak d$ is
continuous on $[0,\infty)^2$, vanishes when $\mu=0$ or $\lambda=0$, and satisfies
\begin{equation}\label{eqn:app-drift-kernel-bounds}
0\le\mathfrak d(\mu,\lambda)\le\frac{\mu\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\mu\mathfrak d(\mu,\lambda)}\le\frac{\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\lambda\mathfrak d(\mu,\lambda)}\le\frac{\mu}{\sqrt{2\ridge}},
\end{equation}
with one-sided derivatives at $0$; in particular $\mathfrak d$ is Lipschitz on
$[0,C_\Sigma]^2$ with constant $C_\Sigma/\sqrt{2\ridge_-}$ in each variable.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_kernel_ii {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    ContinuousOn (fun p : ℝ × ℝ => kernel w (specOutFM F) (specInFM F) ϱ p.1 p.2)
        (Ici 0 ×ˢ Ici 0) ∧
    (∀ lam : ℝ, kernel w (specOutFM F) (specInFM F) ϱ 0 lam = 0) ∧
    (∀ μ : ℝ, kernel w (specOutFM F) (specInFM F) ϱ μ 0 = 0) ∧
    (∀ μ lam : ℝ, 0 ≤ μ → 0 ≤ lam →
      0 ≤ kernel w (specOutFM F) (specInFM F) ϱ μ lam ∧
        kernel w (specOutFM F) (specInFM F) ϱ μ lam ≤ μ * lam / Real.sqrt (2 * ϱ)) ∧
    (∀ μ lam : ℝ, 0 ≤ μ → 0 ≤ lam →
      ∃ d : ℝ, HasDerivWithinAt (fun x => kernel w (specOutFM F) (specInFM F) ϱ x lam) d
          (Ici 0) μ ∧ |d| ≤ lam / Real.sqrt (2 * ϱ)) ∧
    (∀ μ lam : ℝ, 0 ≤ μ → 0 ≤ lam →
      ∃ d : ℝ, HasDerivWithinAt (fun y => kernel w (specOutFM F) (specInFM F) ϱ μ y) d
          (Ici 0) lam ∧ |d| ≤ μ / Real.sqrt (2 * ϱ)) := by
  obtain ⟨hac, hbc, hLc, ha, hb, hLb⟩ := kg_branch hC hγ hw F h hϱ
  have hL0 : ∀ u : ℝ, 0 ≤ Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) :=
    fun u => (hLb u).1
  have hL1 : ∀ u : ℝ, Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ≤ 1 :=
    fun u => (hLb u).2
  have hK : ∀ μ lam : ℝ, kernel w (specOutFM F) (specInFM F) ϱ μ lam = Real.sqrt 2 / Real.pi *
      ∫ u in Ioi (0 : ℝ), (ϱ + u ^ 2) * Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) *
        μ * lam / ((ϱ + u ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 * μ) *
        (ϱ + u ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.2 * lam)) :=
    fun _ _ => rfl
  simp only [hK]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (kg_cont hϱ hac hbc hLc ha hb hL0 hL1
      ⟨Set.mem_Ici.mp (Set.mem_prod.mp hp).1, Set.mem_Ici.mp (Set.mem_prod.mp hp).2⟩).const_mul _
  · intro lam
    simp
  · intro μ
    simp
  · intro μ lam hμ hlam
    obtain ⟨i0, i1⟩ := kg_int_bounds hϱ ha hb hL0 hL1 hμ hlam
    refine ⟨mul_nonneg (by positivity) i0, ?_⟩
    calc Real.sqrt 2 / Real.pi * _ ≤ Real.sqrt 2 / Real.pi * (μ * lam * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹)) :=
          mul_le_mul_of_nonneg_left i1 (by positivity)
      _ = μ * lam / Real.sqrt (2 * ϱ) := kg_const hϱ μ lam
  · intro μ lam hμ hlam
    obtain ⟨d', hd', hbd⟩ := kg_hasDeriv hϱ hac hbc hLc ha hb hL0 hL1 hμ hlam
    refine ⟨Real.sqrt 2 / Real.pi * d', hd'.const_mul _, ?_⟩
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / Real.pi)]
    calc Real.sqrt 2 / Real.pi * |d'| ≤ Real.sqrt 2 / Real.pi * (1 * lam * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹)) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left hbd (by positivity)
      _ = 1 * lam / Real.sqrt (2 * ϱ) := kg_const hϱ 1 lam
      _ = lam / Real.sqrt (2 * ϱ) := by ring
  · intro μ lam hμ hlam
    obtain ⟨d', hd', hbd⟩ := kg_hasDeriv hϱ hbc hac hLc hb ha hL0 hL1 hlam hμ
    refine ⟨Real.sqrt 2 / Real.pi * d', ?_, ?_⟩
    · convert hd'.const_mul (Real.sqrt 2 / Real.pi) using 1
      funext y
      congr 1
      congr 1
      funext u
      ring
    · rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.sqrt 2 / Real.pi)]
      calc Real.sqrt 2 / Real.pi * |d'| ≤ Real.sqrt 2 / Real.pi * (1 * μ * (Real.pi / 2 * (Real.sqrt ϱ)⁻¹)) := by
            rw [one_mul]; exact mul_le_mul_of_nonneg_left hbd (by positivity)
        _ = 1 * μ / Real.sqrt (2 * ϱ) := kg_const hϱ 1 μ
        _ = μ / Real.sqrt (2 * ϱ) := by ring

/-- `cor:app-drift-kernel`(ii), Lipschitz clause: on `[0,C_Σ]²`, `𝔡` is Lipschitz in each variable
with constant `C_Σ/√(2ϱ₋)`, uniformly for `ϱ ∈ [ϱ₋, ϱ₊]` (`ϱ₋ = ϱlo > 0`). Snapshot
`cr-2026-10-23`. Source, verbatim:
```
\begin{corollary}[The drift kernel]\label{cor:app-drift-kernel}
Under \cref{assum:app-setup-regime}, let $\Gtilde=\Qridge\ridge(\Mt)$ be the
frozen-state update and put $(E_\ridge)_{ij}\defeq u_i^\T\big(\EE\Gtilde-\Gtildebar_\ridge\big)v_j$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ and every $\ridge\in[\ridge_-,\ridge_+]$,
\begin{equation}\label{eqn:app-drift-projected}
\EE\big[u_i^\T\Gtilde v_j\big]=\frac{\sqrt2\,\mathfrak d(\mu_i,\lambda_j)}{\sqrt{2\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij}
=\frac{\mathfrak d(\mu_i,\lambda_j)}{\sqrt{\cR(t)}}\,(u_i^\T\Dt v_j)+(E_\ridge)_{ij},
\end{equation}
and $\sup_{\ridge\in[\ridge_-,\ridge_+]}\big(\sum_{i,j}(E_\ridge)_{ij}^2\big)^{1/2}=\varepsilon_B\to0$.
Consequently the frozen-state drift \cref{eqn:app-setup-DV} of the update
$\Gtilde$ is
\begin{equation}\label{eqn:app-drift-Dij}
\cD_{ij}(t)=\frac{\mathfrak d_{ij}}{\sqrt{\cR(t)}}\,\CMscr Q_{ij}(t)+(u_i^\T\Dt v_j)(E_\ridge)_{ij},
\qquad \mathfrak d_{ij}\defeq\mathfrak d(\mu_i,\lambda_j),
\end{equation}
and for every bounded function $\phi$ on $[0,\infty)^2$,
\begin{equation}\label{eqn:app-drift-tested}
\Big|\sum_{i,j}\phi(\mu_i,\lambda_j)\,(u_i^\T\Dt v_j)\,(E_\ridge)_{ij}\Big|\le\norm\phi_\infty\,\norm{\Dt}_\F\,\varepsilon_B .
\end{equation}
\item For every $\ridge\in[\ridge_-,\ridge_+]$ the function $\mathfrak d$ is
continuous on $[0,\infty)^2$, vanishes when $\mu=0$ or $\lambda=0$, and satisfies
\begin{equation}\label{eqn:app-drift-kernel-bounds}
0\le\mathfrak d(\mu,\lambda)\le\frac{\mu\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\mu\mathfrak d(\mu,\lambda)}\le\frac{\lambda}{\sqrt{2\ridge}},\qquad
\abs{\partial_\lambda\mathfrak d(\mu,\lambda)}\le\frac{\mu}{\sqrt{2\ridge}},
\end{equation}
with one-sided derivatives at $0$; in particular $\mathfrak d$ is Lipschitz on
$[0,C_\Sigma]^2$ with constant $C_\Sigma/\sqrt{2\ridge_-}$ in each variable.
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_kernel_ii_lip {CS γ ϱlo ϱhi : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    (hlo : 0 < ϱlo) (hle : ϱlo ≤ ϱhi)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    {ϱ : ℝ} (hϱ : ϱ ∈ Icc ϱlo ϱhi) :
    (∀ μ μ' lam : ℝ, μ ∈ Icc 0 CS → μ' ∈ Icc 0 CS → lam ∈ Icc 0 CS →
      |kernel w (specOutFM F) (specInFM F) ϱ μ lam - kernel w (specOutFM F) (specInFM F) ϱ μ' lam|
        ≤ CS / Real.sqrt (2 * ϱlo) * |μ - μ'|) ∧
    (∀ μ lam lam' : ℝ, μ ∈ Icc 0 CS → lam ∈ Icc 0 CS → lam' ∈ Icc 0 CS →
      |kernel w (specOutFM F) (specInFM F) ϱ μ lam - kernel w (specOutFM F) (specInFM F) ϱ μ lam'|
        ≤ CS / Real.sqrt (2 * ϱlo) * |lam - lam'|) := by
  have hϱpos : 0 < ϱ := lt_of_lt_of_le hlo hϱ.1
  obtain ⟨-, -, -, -, hD1, hD2⟩ := cor_app_drift_kernel_ii hC hγ hw F h hϱpos
  have hsq : 0 < Real.sqrt (2 * ϱlo) := Real.sqrt_pos.mpr (by linarith)
  have hmono : Real.sqrt (2 * ϱlo) ≤ Real.sqrt (2 * ϱ) :=
    Real.sqrt_le_sqrt (by linarith [hϱ.1])
  have hbnd : ∀ t : ℝ, 0 ≤ t → t ≤ CS → t / Real.sqrt (2 * ϱ) ≤ CS / Real.sqrt (2 * ϱlo) := by
    intro t ht htC
    calc t / Real.sqrt (2 * ϱ) ≤ t / Real.sqrt (2 * ϱlo) :=
          div_le_div_of_nonneg_left ht hsq hmono
      _ ≤ CS / Real.sqrt (2 * ϱlo) := div_le_div_of_nonneg_right htC hsq.le
  refine ⟨?_, ?_⟩
  · intro μ μ' lam hμ hμ' hlam
    have key : ∀ t : ℝ, ∃ d : ℝ, 0 ≤ t →
        HasDerivWithinAt (fun x => kernel w (specOutFM F) (specInFM F) ϱ x lam) d (Ici 0) t ∧
          |d| ≤ lam / Real.sqrt (2 * ϱ) := by
      intro t
      by_cases ht : 0 ≤ t
      · obtain ⟨d, h1, h2⟩ := hD1 t lam ht hlam.1
        exact ⟨d, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨0, fun h' => absurd h' ht⟩
    choose D hD using key
    have hf : ∀ x ∈ Icc 0 CS, HasDerivWithinAt
        (fun x => kernel w (specOutFM F) (specInFM F) ϱ x lam) (D x) (Icc 0 CS) x :=
      fun x hx => ((hD x hx.1).1).mono Set.Icc_subset_Ici_self
    have hbd : ∀ x ∈ Icc 0 CS, ‖D x‖ ≤ CS / Real.sqrt (2 * ϱlo) := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact (hD x hx.1).2.trans (hbnd lam hlam.1 hlam.2)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun x => kernel w (specOutFM F) (specInFM F) ϱ x lam) hf hbd (convex_Icc 0 CS) hμ hμ'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (kernel w (specOutFM F) (specInFM F) ϱ μ lam),
      abs_sub_comm μ μ'] at *
    exact hmvt
  · intro μ lam lam' hμ hlam hlam'
    have key : ∀ t : ℝ, ∃ d : ℝ, 0 ≤ t →
        HasDerivWithinAt (fun y => kernel w (specOutFM F) (specInFM F) ϱ μ y) d (Ici 0) t ∧
          |d| ≤ μ / Real.sqrt (2 * ϱ) := by
      intro t
      by_cases ht : 0 ≤ t
      · obtain ⟨d, h1, h2⟩ := hD2 μ t hμ.1 ht
        exact ⟨d, fun _ => ⟨h1, h2⟩⟩
      · exact ⟨0, fun h' => absurd h' ht⟩
    choose D hD using key
    have hf : ∀ x ∈ Icc 0 CS, HasDerivWithinAt
        (fun y => kernel w (specOutFM F) (specInFM F) ϱ μ y) (D x) (Icc 0 CS) x :=
      fun x hx => ((hD x hx.1).1).mono Set.Icc_subset_Ici_self
    have hbd : ∀ x ∈ Icc 0 CS, ‖D x‖ ≤ CS / Real.sqrt (2 * ϱlo) := by
      intro x hx
      rw [Real.norm_eq_abs]
      exact (hD x hx.1).2.trans (hbnd μ hμ.1 hμ.2)
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun y => kernel w (specOutFM F) (specInFM F) ϱ μ y) hf hbd (convex_Icc 0 CS) hlam hlam'
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (kernel w (specOutFM F) (specInFM F) ϱ μ lam),
      abs_sub_comm lam lam'] at *
    exact hmvt


private lemma kern_eig_one {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (hA : A.IsHermitian) (h1 : A = 1)
    (i : Fin k) : hA.eigenvalues i = 1 := by
  subst h1
  have hv := hA.mulVec_eigenvectorBasis i
  rw [Matrix.one_mulVec] at hv
  have hn := hA.eigenvectorBasis.orthonormal.1 i
  by_contra hne
  have h0 : (1 - hA.eigenvalues i) • (⇑(hA.eigenvectorBasis i)) = 0 := by
    rw [sub_smul, one_smul]; exact sub_eq_zero.2 hv
  rcases smul_eq_zero.1 h0 with h | h
  · exact hne (by linarith)
  · have h2 : hA.eigenvectorBasis i = 0 := by
      ext j
      exact congrFun h j
    rw [h2, norm_zero] at hn
    norm_num at hn

private lemma kern_int_nuIn (C : Covariances m n) (hSin : C.Sin = 1) (g : ℝ → ℝ) :
    ∫ x, g x ∂(Muon.nuIn C B) = (B : ℝ)⁻¹ * ((n : ℝ) * g 1) := by
  have hE : ∀ k, C.psdIn.isHermitian.eigenvalues k = 1 :=
    fun k => kern_eig_one C.Sin C.psdIn.isHermitian hSin k
  unfold Muon.nuIn
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac (by simp)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp [hE]

private lemma kern_lam_one (F : FrozenParams m n B) (hSin : F.C.Sin = 1) (SD : SpectralData F.C)
    (j : Fin n) : SD.lam j = 1 := by
  have hv : (fun k => SD.vIn k j) = SD.lam j • (fun k => SD.vIn k j) := by
    have := SD.eigIn j
    rwa [hSin, Matrix.one_mulVec] at this
  have hd : dotProduct (fun k => SD.vIn k j) (fun k => SD.vIn k j) = 1 := by
    have := congrFun (congrFun SD.hvIn j) j
    simpa [Matrix.mul_apply, dotProduct] using this
  have h3 := congrArg (fun w => dotProduct (fun k => SD.vIn k j) w) hv
  simp only [dotProduct_smul, smul_eq_mul] at h3
  rw [hd] at h3
  linarith

private lemma kern_inv_of_sol {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} (C : Covariances m n)
    (hSin : C.Sin = 1) (hB : 0 < B) (hn : 0 < n) (hν' : (ν' : Measure ℝ) = Muon.nuIn C B)
    {z : ℝ} (x : ℝ × ℝ × ℝ × ℝ) (hx : IsBranchSol F ν ν' z x) :
    ((B : ℝ) / (n : ℝ)) * x.2.1 = (z + x.2.2.2 * 1)⁻¹ := by
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, -, -, -, hσ', -, -⟩ := hx
  dsimp only at hσ' ⊢
  rw [hν'] at hσ'
  have key := kern_int_nuIn (B := B) C hSin (fun t => t / (c * t + z))
  rw [key] at hσ'
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hσ']
  field_simp
  try ring

private lemma kern_pt_alg (z L μ a σ' c B' n' : ℝ) (hk : (B' / n') * σ' = (z + c * 1)⁻¹) :
    z * L * μ * 1 / ((z + a * μ) * (z + c * 1)) = (B' / n') * (z * L * σ' * μ / (z + a * μ)) := by
  have hz : z + c * 1 = ((B' / n') * σ')⁻¹ := by rw [hk, inv_inv]
  rw [hz]
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

private lemma kern_fw_lead1 (q : ℝ) : Fw (leadW 1) q = J q := by
  unfold Fw
  rw [tsum_eq_single 0]
  · simp [leadW]
  · intro j hj
    simp [leadW, hj]

private lemma kern_lw_lead1 (q : ℝ) : Lw (leadW 1) q = J q := by
  unfold Lw
  rw [tsum_eq_single 0]
  · simp [leadW]
  · intro j hj
    simp [leadW, hj]

private lemma kern_adm1 : AdmissibleWeightFn (Fw (leadW 1)) := by
  have hw : WeightSeq (leadW 1) := by
    unfold WeightSeq
    refine ⟨fun j => ?_, ?_, ⟨0, by simp [leadW]⟩⟩
    · unfold leadW
      split_ifs <;> norm_num
    · exact (hasSum_ite_eq 0 (1 : ℝ)).summable
  exact Fw_admissible hw

private lemma kern_emaW_zero : Muon.emaW 0 = leadW 1 := by
  funext j
  unfold Muon.emaW leadW
  by_cases hj : j = 0
  · subst hj; simp
  · simp [hj, zero_pow hj]

/-- Private helper: the common form of `cor:app-drift-halfaniso`(i) and (iii) at `λ = 1`. -/
private lemma kern_halfaniso_eq {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hF : AdmissibleWeightFn (Fw w)) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (hSin : F.C.Sin = 1) (SD : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 < ϱ) (i : Fin m) :
    kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) 1 =
      Real.sqrt 2 * (B : ℝ) / (Real.pi * (n : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          (ϱ + u ^ 2) * Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) *
            (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.1 * SD.μ i /
            (ϱ + u ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 *
              SD.μ i) := by
  have hB : 0 < B := F.hB
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      subst h0
      have hA := F.hA
      simp [fro] at hA
    · exact h0
  have hB' : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp := spectral_mem_classK F h
  have hν' : ((specInFM F : FiniteMeasure ℝ) : Measure ℝ) = Muon.nuIn F.C B := rfl
  obtain ⟨hSo, hSi, hmax⟩ := h
  have hC' : 0 < CS := hC
  unfold kernel
  rw [show Real.sqrt 2 * (B : ℝ) / (Real.pi * (n : ℝ)) = Real.sqrt 2 / Real.pi * ((B : ℝ) / n)
    by ring, mul_assoc]
  congr 1
  rw [← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hz : 0 < ϱ + u ^ 2 := by
    have := sq_nonneg u
    linarith
  have hspec := branchSol_spec hF hC hγ hp hz
  have hinv := kern_inv_of_sol F.C hSin hB hn hν' _ hspec
  dsimp only
  generalize branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2) = x at hinv ⊢
  exact kern_pt_alg _ _ _ _ _ _ _ _ hinv

/-- `cor:app-drift-halfaniso`(i) (alias `rem:app-drift-halfaniso`): under `Σ_in = Id`, `𝔡_ij = 𝔡_i`
for every `j`, and `𝔡_i` has the integral form of part (i). Snapshot `cr-2026-10-23`. Source,
verbatim:
```
\begin{corollary}[Half-anisotropic input]\label{cor:app-drift-halfaniso}\label{rem:app-drift-halfaniso}
Under \cref{assum:app-setup-regime}, assume $\Sigmain=\Id_{\Nin}$, let
$\ridge\in[\ridge_-,\ridge_+]$, write $z=\ridge+u^2$, and put
$\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ the kernel is $\mathfrak d_{ij}=\mathfrak d_i$, and
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{z\,\Lw(q(-z))\,\tilde\sigma(-z)\,\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item The row drift of \cref{eqn:app-setup-row} is, with $E_\ridge$ as in
\cref{cor:app-drift-kernel},
\[
\sum_j\cD_{ij}(t)=\frac{\mathfrak d_i}{\sqrt{\cR(t)}}\,\CMscr Q_i(t)+\sum_j(u_i^\T\Dt v_j)(E_\ridge)_{ij}.
\]
\item At $\bmom=0$,
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{\tilde s_1(-z)\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item At $\bmom=0$, if $\zeta\mapsto(\tilde s_1(\zeta)\mu_i-\zeta)^{-1}$ is the
Stieltjes transform of a probability measure $\rho_i$ on $[0,\infty)$, then
\[
\mathfrak d_i=\frac{B}{\sqrt2\,\Nin}\int_{[0,\infty)}\frac{x}{\sqrt{x+\ridge}}\,\rho_i(dx).
\]
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_halfaniso_i {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (hSin : F.C.Sin = 1) (SD : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (∀ i j, kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) (SD.lam j) =
        kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) 1) ∧
    (∀ i, kernel w (specOutFM F) (specInFM F) ϱ (SD.μ i) 1 =
        Real.sqrt 2 * (B : ℝ) / (Real.pi * (n : ℝ)) *
          ∫ u in Ioi (0 : ℝ),
            (ϱ + u ^ 2) * Lw w (branchQ w (specOutFM F) (specInFM F) (ϱ + u ^ 2)) *
              (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.1 * SD.μ i /
              (ϱ + u ^ 2 + (branchSol (Fw w) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 *
                SD.μ i)) := by
  refine ⟨fun i j => ?_, fun i => kern_halfaniso_eq hC hγ (Fw_admissible hw.1) F h hSin SD hϱ i⟩
  rw [kern_lam_one F hSin SD j]

/-- `cor:app-drift-halfaniso`(iii) (alias `rem:app-drift-halfaniso`): at `β = 0` (the no-momentum
weights `Muon.emaW 0 = (1,0,0,…)`), `𝔡_i` has the form with `s̃₁(−z)` in place of the source
factor. Snapshot `cr-2026-10-23`. Source, verbatim:
```
\begin{corollary}[Half-anisotropic input]\label{cor:app-drift-halfaniso}\label{rem:app-drift-halfaniso}
Under \cref{assum:app-setup-regime}, assume $\Sigmain=\Id_{\Nin}$, let
$\ridge\in[\ridge_-,\ridge_+]$, write $z=\ridge+u^2$, and put
$\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ the kernel is $\mathfrak d_{ij}=\mathfrak d_i$, and
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{z\,\Lw(q(-z))\,\tilde\sigma(-z)\,\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item The row drift of \cref{eqn:app-setup-row} is, with $E_\ridge$ as in
\cref{cor:app-drift-kernel},
\[
\sum_j\cD_{ij}(t)=\frac{\mathfrak d_i}{\sqrt{\cR(t)}}\,\CMscr Q_i(t)+\sum_j(u_i^\T\Dt v_j)(E_\ridge)_{ij}.
\]
\item At $\bmom=0$,
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{\tilde s_1(-z)\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item At $\bmom=0$, if $\zeta\mapsto(\tilde s_1(\zeta)\mu_i-\zeta)^{-1}$ is the
Stieltjes transform of a probability measure $\rho_i$ on $[0,\infty)$, then
\[
\mathfrak d_i=\frac{B}{\sqrt2\,\Nin}\int_{[0,\infty)}\frac{x}{\sqrt{x+\ridge}}\,\rho_i(dx).
\]
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_halfaniso_iii {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (hSin : F.C.Sin = 1) (hβ : F.β = 0) (SD : SpectralData F.C) {ϱ : ℝ} (hϱ : 0 < ϱ)
    (i : Fin m) :
    kernel (Muon.emaW F.β) (specOutFM F) (specInFM F) ϱ (SD.μ i) 1 =
      Real.sqrt 2 * (B : ℝ) / (Real.pi * (n : ℝ)) *
        ∫ u in Ioi (0 : ℝ),
          (branchSol (Fw (Muon.emaW F.β)) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 * SD.μ i /
            (ϱ + u ^ 2 +
              (branchSol (Fw (Muon.emaW F.β)) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 *
                SD.μ i) := by
  have hp := spectral_mem_classK F h
  have hw0 : Muon.emaW F.β = leadW 1 := by rw [hβ, kern_emaW_zero]
  rw [hw0, kern_halfaniso_eq hC hγ kern_adm1 F h hSin SD hϱ i]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  have hz : 0 < ϱ + u ^ 2 := by
    have := sq_nonneg u
    linarith
  have hspec := branchSol_spec kern_adm1 hC hγ hp hz
  dsimp only
  unfold branchQ
  generalize branchSol (Fw (leadW 1)) (specOutFM F) (specInFM F) (ϱ + u ^ 2) = x at hspec ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, -, -, -, -, ha, -⟩ := hspec
  dsimp only at ha ⊢
  rw [kern_fw_lead1] at ha
  rw [kern_lw_lead1, ha]
  congr 1
  ring

/-- Private helper for `cor:app-drift-halfaniso`(iv): if `a ≥ 0` and `(ϱ+u²+a(u))⁻¹ = ∫(x+ϱ+u²)⁻¹ dρ`
for all `u`, with `ρ` a probability measure on `[0,∞)`, then `∫_{u>0} a/(ϱ+u²+a) du =
(π/2) ∫_{[0,∞)} x/√(x+ϱ) dρ`. Proved by Tonelli in lintegral form, so no integrability of
`x/√(x+ϱ)` is needed. -/
private lemma kern_iv_core {ϱ : ℝ} (hϱ : 0 < ϱ) {ρ : Measure ℝ} (hρ : IsProbabilityMeasure ρ)
    (hρ0 : ρ (Iio 0) = 0) {a : ℝ → ℝ} (ha : ∀ u, 0 ≤ a u)
    (hS : ∀ u : ℝ, (ϱ + u ^ 2 + a u)⁻¹ = ∫ x, (x + (ϱ + u ^ 2))⁻¹ ∂ρ) :
    ∫ u in Ioi (0 : ℝ), a u / (ϱ + u ^ 2 + a u) =
      Real.pi / 2 * ∫ x in Ici (0 : ℝ), x / Real.sqrt (x + ϱ) ∂ρ := by
  haveI := hρ
  have hae : ∀ᵐ x ∂ρ, x ∈ Ici (0 : ℝ) := by
    rw [ae_iff]
    convert hρ0 using 2
    ext x
    simp
  have hres : ρ.restrict (Ici (0 : ℝ)) = ρ := Measure.restrict_eq_self_of_ae_mem hae
  obtain ⟨G, hG⟩ : ∃ G : ℝ → ℝ → ℝ, ∀ u x, G u x = if 0 ≤ x then x / (x + (ϱ + u ^ 2)) else 0 :=
    ⟨_, fun _ _ => rfl⟩
  have hG0 : ∀ u x, 0 ≤ G u x := by
    intro u x
    rw [hG]
    split_ifs with hx
    · have hz : 0 < ϱ + u ^ 2 := by have := sq_nonneg u; linarith
      exact div_nonneg hx (by linarith)
    · exact le_rfl
  have hG1 : ∀ u x, G u x ≤ 1 := by
    intro u x
    rw [hG]
    split_ifs with hx
    · have hz : 0 < ϱ + u ^ 2 := by have := sq_nonneg u; linarith
      rw [div_le_one (by linarith)]
      linarith
    · exact zero_le_one
  have hGm : Measurable (fun p : ℝ × ℝ => G p.1 p.2) := by
    have e : (fun p : ℝ × ℝ => G p.1 p.2) = fun p : ℝ × ℝ =>
        if 0 ≤ p.2 then p.2 / (p.2 + (ϱ + p.1 ^ 2)) else 0 :=
      funext fun p => hG p.1 p.2
    rw [e]
    exact Measurable.ite (measurableSet_le measurable_const measurable_snd) (by fun_prop)
      measurable_const
  have hslice : ∀ u : ℝ, Measurable (fun x => G u x) := fun u =>
    hGm.comp (measurable_const.prodMk measurable_id)
  have hGint : ∀ u : ℝ, Integrable (fun x => G u x) ρ := fun u =>
    Integrable.mono' (integrable_const (1 : ℝ)) (hslice u).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hG0 u x)]
        exact hG1 u x)
  have hstep : ∀ u : ℝ, a u / (ϱ + u ^ 2 + a u) = ∫ x, G u x ∂ρ := by
    intro u
    have hz : 0 < ϱ + u ^ 2 := by have := sq_nonneg u; linarith
    have hza : 0 < ϱ + u ^ 2 + a u := by linarith [ha u]
    have hint : Integrable (fun x : ℝ => (x + (ϱ + u ^ 2))⁻¹) ρ := by
      refine Integrable.mono' (integrable_const (ϱ + u ^ 2)⁻¹)
        (by fun_prop : Measurable (fun x : ℝ => (x + (ϱ + u ^ 2))⁻¹)).aestronglyMeasurable ?_
      filter_upwards [hae] with x hx
      have hx' : 0 ≤ x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (by linarith))]
      exact inv_anti₀ hz (by linarith)
    have e1 : ∫ x, G u x ∂ρ = ∫ x, (1 - (ϱ + u ^ 2) * (x + (ϱ + u ^ 2))⁻¹) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      have hx' : 0 ≤ x := hx
      have hne : x + (ϱ + u ^ 2) ≠ 0 := (by linarith : (0 : ℝ) < x + (ϱ + u ^ 2)).ne'
      rw [hG, if_pos hx', div_eq_mul_inv]
      linear_combination inv_mul_cancel₀ hne
    have e2 : ∫ x, (1 - (ϱ + u ^ 2) * (x + (ϱ + u ^ 2))⁻¹) ∂ρ =
        1 - (ϱ + u ^ 2) * ∫ x, (x + (ϱ + u ^ 2))⁻¹ ∂ρ := by
      rw [integral_sub (integrable_const (1 : ℝ)) (hint.const_mul _), integral_const_mul,
        integral_const]
      simp
    have e3 : a u / (ϱ + u ^ 2 + a u) = 1 - (ϱ + u ^ 2) * (ϱ + u ^ 2 + a u)⁻¹ := by
      rw [div_eq_mul_inv]
      linear_combination inv_mul_cancel₀ hza.ne'
    rw [e3, hS u, e1, e2]
  have hΦ0 : ∀ u : ℝ, 0 ≤ ∫ x, G u x ∂ρ := fun u => integral_nonneg (hG0 u)
  have hΦm : Measurable (fun u : ℝ => ∫ x, G u x ∂ρ) :=
    (StronglyMeasurable.integral_prod_right (ν := ρ) (f := fun u x => G u x)
      hGm.stronglyMeasurable).measurable
  have hfu : ∀ u : ℝ, ∫⁻ x, ENNReal.ofReal (G u x) ∂ρ = ENNReal.ofReal (∫ x, G u x ∂ρ) :=
    fun u => (ofReal_integral_eq_lintegral_ofReal (hGint u) (ae_of_all _ (hG0 u))).symm
  have hm : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (G p.1 p.2)) := hGm.ennreal_ofReal
  have hΦ_eq : ∫ u in Ioi (0 : ℝ), ∫ x, G u x ∂ρ =
      (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (∫ x, G u x ∂ρ)).toReal := by
    rw [← integral_toReal hΦm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    exact setIntegral_congr_fun measurableSet_Ioi
      (fun u _ => (ENNReal.toReal_ofReal (hΦ0 u)).symm)
  have hinner : ∀ x : ℝ, 0 ≤ x → ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (G u x) =
      ENNReal.ofReal (Real.pi / 2 * (x / Real.sqrt (x + ϱ))) := by
    intro x hx
    have hpos : 0 < x + ϱ := by linarith
    have hfun : (fun u : ℝ => ENNReal.ofReal (G u x)) =
        fun u : ℝ => ENNReal.ofReal (x * (x + ϱ + u ^ 2)⁻¹) := by
      funext u
      rw [hG, if_pos hx, div_eq_mul_inv, show x + (ϱ + u ^ 2) = x + ϱ + u ^ 2 by ring]
    have hnn : ∀ u : ℝ, 0 ≤ x * (x + ϱ + u ^ 2)⁻¹ := fun u =>
      mul_nonneg hx (inv_nonneg.2 (by have := sq_nonneg u; linarith))
    have hint2 : IntegrableOn (fun u : ℝ => x * (x + ϱ + u ^ 2)⁻¹) (Ioi (0 : ℝ)) :=
      Integrable.const_mul (kern_ioi_integral hpos).1 x
    rw [hfun, ← ofReal_integral_eq_lintegral_ofReal hint2 (ae_of_all _ hnn), integral_const_mul,
      (kern_ioi_integral hpos).2]
    congr 1
    ring
  have hcongr : ∫⁻ x, (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (G u x)) ∂ρ =
      ∫⁻ x, ENNReal.ofReal (Real.pi / 2 * (x / Real.sqrt (x + ϱ))) ∂ρ := by
    apply lintegral_congr_ae
    filter_upwards [hae] with x hx
    exact hinner x hx
  have hhm : Measurable (fun x : ℝ => Real.pi / 2 * (x / Real.sqrt (x + ϱ))) := by fun_prop
  have hfinal : (∫⁻ x, ENNReal.ofReal (Real.pi / 2 * (x / Real.sqrt (x + ϱ))) ∂ρ).toReal =
      Real.pi / 2 * ∫ x in Ici (0 : ℝ), x / Real.sqrt (x + ϱ) ∂ρ := by
    rw [← integral_toReal hhm.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    have e5 : ∫ x, (ENNReal.ofReal (Real.pi / 2 * (x / Real.sqrt (x + ϱ)))).toReal ∂ρ =
        ∫ x, Real.pi / 2 * (x / Real.sqrt (x + ϱ)) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      have hx' : 0 ≤ x := hx
      exact ENNReal.toReal_ofReal
        (mul_nonneg (by positivity) (div_nonneg hx' (Real.sqrt_nonneg _)))
    rw [e5, integral_const_mul, hres]
  have hEq : ∫ u in Ioi (0 : ℝ), a u / (ϱ + u ^ 2 + a u) =
      ∫ u in Ioi (0 : ℝ), ∫ x, G u x ∂ρ :=
    setIntegral_congr_fun measurableSet_Ioi (fun u _ => hstep u)
  have hL : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (∫ x, G u x ∂ρ) =
      ∫⁻ u in Ioi (0 : ℝ), ∫⁻ x, ENNReal.ofReal (G u x) ∂ρ :=
    lintegral_congr (fun u => (hfu u).symm)
  rw [hEq, hΦ_eq, hL, lintegral_lintegral_swap (f := fun u x => ENNReal.ofReal (G u x)) hm.aemeasurable,
    hcongr, hfinal]

/-- `cor:app-drift-halfaniso`(iv) (alias `rem:app-drift-halfaniso`), for one output mode `i`: at
`β = 0`, if `ρ` is a probability measure on `[0,∞)` whose Stieltjes representation holds on the
negative axis for `μ_i`, then `𝔡_i = (B/(√2 N_in)) ∫_{[0,∞)} x/√(x+ϱ) ρ(dx)`.

The hypothesis `hStieltjes` is the negative-axis reading (`z = −ζ > 0`) of the source's hypothesis
on `ζ ↦ (s̃₁(ζ)μ_i − ζ)^{-1}`, which is ill-typed as written (card §6.8; `CORRECTIONS.md` row 4,
accepted). The measure `ρ` is one hypothesis variable per mode `i`. Snapshot `cr-2026-10-23`.
Source, verbatim:
```
\begin{corollary}[Half-anisotropic input]\label{cor:app-drift-halfaniso}\label{rem:app-drift-halfaniso}
Under \cref{assum:app-setup-regime}, assume $\Sigmain=\Id_{\Nin}$, let
$\ridge\in[\ridge_-,\ridge_+]$, write $z=\ridge+u^2$, and put
$\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ the kernel is $\mathfrak d_{ij}=\mathfrak d_i$, and
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{z\,\Lw(q(-z))\,\tilde\sigma(-z)\,\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item The row drift of \cref{eqn:app-setup-row} is, with $E_\ridge$ as in
\cref{cor:app-drift-kernel},
\[
\sum_j\cD_{ij}(t)=\frac{\mathfrak d_i}{\sqrt{\cR(t)}}\,\CMscr Q_i(t)+\sum_j(u_i^\T\Dt v_j)(E_\ridge)_{ij}.
\]
\item At $\bmom=0$,
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{\tilde s_1(-z)\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item At $\bmom=0$, if $\zeta\mapsto(\tilde s_1(\zeta)\mu_i-\zeta)^{-1}$ is the
Stieltjes transform of a probability measure $\rho_i$ on $[0,\infty)$, then
\[
\mathfrak d_i=\frac{B}{\sqrt2\,\Nin}\int_{[0,\infty)}\frac{x}{\sqrt{x+\ridge}}\,\rho_i(dx).
\]
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_halfaniso_iv {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    (F : FrozenParams m n B) (h : DriftBound F CS γ)
    (hSin : F.C.Sin = 1) (hβ : F.β = 0) (SD : SpectralData F.C) (i : Fin m)
    (ρ : Measure ℝ) (hρ : IsProbabilityMeasure ρ ∧ ρ (Iio 0) = 0)
    (hStieltjes : ∀ z : ℝ, 0 < z →
      (z + (branchSol (Fw (Muon.emaW F.β)) (specOutFM F) (specInFM F) z).2.2.1 * SD.μ i)⁻¹ =
        ∫ x, (x + z)⁻¹ ∂ρ)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    kernel (Muon.emaW F.β) (specOutFM F) (specInFM F) ϱ (SD.μ i) 1 =
      (B : ℝ) / (Real.sqrt 2 * (n : ℝ)) *
        ∫ x in Ici (0 : ℝ), x / Real.sqrt (x + ϱ) ∂ρ := by
  obtain ⟨hpr, hρ0⟩ := hρ
  have hw0 : Muon.emaW F.β = leadW 1 := by rw [hβ, kern_emaW_zero]
  rw [cor_app_drift_halfaniso_iii hC hγ F h hSin hβ SD hϱ i]
  rw [hw0] at hStieltjes ⊢
  have hnn : ∀ u : ℝ,
      0 ≤ (branchSol (Fw (leadW 1)) (specOutFM F) (specInFM F) (ϱ + u ^ 2)).2.2.1 * SD.μ i :=
    fun u => mul_nonneg (kern_isBranch_nonneg (branchSol_spec kern_adm1 hC hγ
      (spectral_mem_classK F h) (show (0 : ℝ) < ϱ + u ^ 2 by have := sq_nonneg u; linarith))).2.2.1
      (μ_nonneg SD i)
  have key := kern_iv_core hϱ hpr hρ0 hnn
    (fun u => hStieltjes (ϱ + u ^ 2) (by have := sq_nonneg u; linarith))
  rw [key]
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rcases eq_or_ne (n : ℝ) 0 with hn | hn
  · simp [hn]
  · have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hs0 : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.2 (by norm_num)).ne'
    field_simp
    linear_combination ((B : ℝ) * ∫ x in Ici (0 : ℝ), x / Real.sqrt (x + ϱ) ∂ρ) * hs2

/-! ### Helpers for `prop_app_drift_truncation_ii` (task P-C.4.P6) -/

private lemma trc_J_int {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun g : ℝ => g ^ 2 / (1 + x * g ^ 2)) (ProbabilityTheory.gaussianReal 0 1) := by
  refine Integrable.mono' (Muon.Foundations.gaussian_integrable_pow 2) ?_ ?_
  · exact (measurable_id.pow_const 2).div (by fun_prop) |>.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun g => ?_
    have hm := mul_nonneg hx (sq_nonneg g)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg g) (by linarith))]
    exact div_le_self (sq_nonneg g) (by linarith)

private lemma trc_J_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Muon.DetEquiv.J x := by
  unfold Muon.DetEquiv.J
  apply integral_nonneg
  intro g
  have hm := mul_nonneg hx (sq_nonneg g)
  exact div_nonneg (sq_nonneg g) (by linarith)

private lemma trc_J_le_one {x : ℝ} (hx : 0 ≤ x) : Muon.DetEquiv.J x ≤ 1 := by
  unfold Muon.DetEquiv.J
  calc (∫ g, g ^ 2 / (1 + x * g ^ 2) ∂(ProbabilityTheory.gaussianReal 0 1))
      ≤ ∫ g, g ^ 2 ∂(ProbabilityTheory.gaussianReal 0 1) :=
        integral_mono (trc_J_int hx) (Muon.Foundations.gaussian_integrable_pow 2)
          (fun g => by
            have hm := mul_nonneg hx (sq_nonneg g)
            exact div_le_self (sq_nonneg g) (by linarith))
    _ = 1 := Muon.Foundations.gaussian_moment_two

/-- `J` is `3`-Lipschitz on `[0,∞)` (private copy; `Drift.Scalar` is not imported). -/
private lemma trc_J_lip {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Muon.DetEquiv.J x - Muon.DetEquiv.J y| ≤ 3 * |x - y| := by
  unfold Muon.DetEquiv.J
  rw [← integral_sub (trc_J_int hx) (trc_J_int hy)]
  have h4 : ∫ g : ℝ, g ^ 4 ∂(ProbabilityTheory.gaussianReal 0 1) = 3 :=
    Muon.Foundations.gaussian_moment_four
  have key : ‖∫ g, (g ^ 2 / (1 + x * g ^ 2) - g ^ 2 / (1 + y * g ^ 2))
      ∂(ProbabilityTheory.gaussianReal 0 1)‖ ≤ ∫ g, g ^ 4 * |x - y|
        ∂(ProbabilityTheory.gaussianReal 0 1) := by
    refine norm_integral_le_of_norm_le
      ((Muon.Foundations.gaussian_integrable_pow 4).mul_const _)
      (Filter.Eventually.of_forall fun g => ?_)
    have ha : 1 ≤ 1 + x * g ^ 2 := by nlinarith [mul_nonneg hx (sq_nonneg g)]
    have hb : 1 ≤ 1 + y * g ^ 2 := by nlinarith [mul_nonneg hy (sq_nonneg g)]
    have hab : 1 ≤ (1 + x * g ^ 2) * (1 + y * g ^ 2) := by nlinarith
    have e : g ^ 2 / (1 + x * g ^ 2) - g ^ 2 / (1 + y * g ^ 2)
        = g ^ 4 * (y - x) / ((1 + x * g ^ 2) * (1 + y * g ^ 2)) := by
      field_simp
      ring
    rw [Real.norm_eq_abs, e, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ g ^ 4),
      abs_of_pos (by linarith : 0 < (1 + x * g ^ 2) * (1 + y * g ^ 2)), abs_sub_comm y x,
      div_le_iff₀ (by linarith)]
    have : 0 ≤ g ^ 4 * |x - y| := by positivity
    nlinarith
  rw [integral_mul_const, h4] at key
  rwa [Real.norm_eq_abs] at key

/-- Truncation keeps the weight class when some retained weight is nonzero. -/
private lemma trc_class {w : ℕ → ℝ} (hw : WeightClass w) {J : ℕ} (hJ : ∃ j ≤ J, w j ≠ 0) :
    WeightClass (truncW w J) := by
  obtain ⟨⟨hw0, hwS, -⟩, hw1, hwsum⟩ := hw
  have hle : ∀ j, truncW w J j ≤ w j := fun j => by
    unfold truncW; split_ifs <;> simp [hw0 j]
  have hnn : ∀ j, 0 ≤ truncW w J j := fun j => by
    unfold truncW; split_ifs <;> simp [hw0 j]
  have hS : Summable (truncW w J) := Summable.of_nonneg_of_le hnn hle hwS
  refine ⟨⟨hnn, hS, ?_⟩, fun j => (hle j).trans (hw1 j), ?_⟩
  · obtain ⟨j, hjJ, hj⟩ := hJ
    exact ⟨j, by unfold truncW; rw [if_pos hjJ]; exact hj⟩
  · exact (hS.tsum_le_tsum hle hwS).trans hwsum

private lemma trc_tail_eq {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha : Summable a) (J : ℕ) :
    (∑' j, if j ≤ J then (0:ℝ) else a j) = ∑' k, a (k + (J + 1)) := by
  have hs : Summable (fun j => if j ≤ J then (0:ℝ) else a j) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [ha0 j])
      (fun j => by split_ifs <;> simp [ha0 j]) ha
  rw [← hs.sum_add_tsum_nat_add (J + 1)]
  have h0 : ∑ i ∈ Finset.range (J + 1), (if i ≤ J then (0:ℝ) else a i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [Finset.mem_range] at hi
    simp [Nat.lt_succ_iff.mp hi]
  rw [h0, zero_add]
  congr 1
  ext k
  rw [if_neg (by omega)]

private lemma trc_tail_tendsto {a : ℕ → ℝ} (ha0 : ∀ j, 0 ≤ a j) (ha : Summable a) :
    Filter.Tendsto (fun J : ℕ => ∑' j, if j ≤ J then (0:ℝ) else a j) Filter.atTop (𝓝 0) := by
  have h := (tendsto_sum_nat_add a).comp (Filter.tendsto_add_atTop_nat 1)
  refine h.congr fun J => ?_
  simp only [Function.comp]
  rw [trc_tail_eq ha0 ha J]

/-- Generic tail comparison. -/
private lemma trc_gen {c f g : ℕ → ℝ} (hc : Summable c) (hf0 : ∀ j, 0 ≤ f j) (hfc : ∀ j, f j ≤ c j)
    (J : ℕ) (hg : ∀ j, g j = if j ≤ J then f j else 0) :
    0 ≤ ∑' j, f j - ∑' j, g j ∧
      ∑' j, f j - ∑' j, g j ≤ ∑' j, (if j ≤ J then (0:ℝ) else c j) := by
  have hc0 : ∀ j, 0 ≤ c j := fun j => (hf0 j).trans (hfc j)
  have hfs : Summable f := Summable.of_nonneg_of_le hf0 hfc hc
  have hg0 : ∀ j, 0 ≤ g j := fun j => by rw [hg]; split_ifs <;> simp [hf0 j]
  have hgf : ∀ j, g j ≤ f j := fun j => by rw [hg]; split_ifs <;> simp [hf0 j]
  have hgs : Summable g := Summable.of_nonneg_of_le hg0 hgf hfs
  have hts : Summable (fun j => if j ≤ J then (0:ℝ) else c j) :=
    Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [hc0 j])
      (fun j => by split_ifs <;> simp [hc0 j]) hc
  rw [← hfs.tsum_sub hgs]
  have hd : ∀ j, f j - g j = if j ≤ J then 0 else f j := fun j => by
    rw [hg]; split_ifs <;> simp
  simp only [hd]
  constructor
  · exact tsum_nonneg fun j => by split_ifs <;> simp [hf0 j]
  · refine Summable.tsum_le_tsum (fun j => ?_) ?_ hts
    · split_ifs
      · exact le_rfl
      · exact hfc j
    · exact Summable.of_nonneg_of_le (fun j => by split_ifs <;> simp [hf0 j])
        (fun j => by split_ifs <;> simp [hf0 j]) hfs

private lemma trc_sq_summable {w : ℕ → ℝ} (hw : WeightClass w) : Summable (fun j => w j ^ 2) :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _)
    (fun j => by nlinarith [hw.1.1 j, hw.2.1 j]) hw.1.2.1

private lemma trc_Fw_diff {w : ℕ → ℝ} (hw : WeightClass w) (J : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Fw w q - Fw (truncW w J) q ∧
      Fw w q - Fw (truncW w J) q ≤ ∑' j, (if j ≤ J then (0:ℝ) else w j ^ 2) := by
  have hq2 : ∀ j, 0 ≤ w j ^ 2 * q := fun j => mul_nonneg (sq_nonneg _) hq
  refine trc_gen (c := fun j => w j ^ 2) (f := fun j => w j ^ 2 * Muon.DetEquiv.J (w j ^ 2 * q))
    (g := fun j => truncW w J j ^ 2 * Muon.DetEquiv.J (truncW w J j ^ 2 * q))
    (trc_sq_summable hw) (fun j => mul_nonneg (sq_nonneg _) (trc_J_nonneg (hq2 j)))
    (fun j => mul_le_of_le_one_right (sq_nonneg _) (trc_J_le_one (hq2 j))) J (fun j => ?_)
  unfold truncW
  split_ifs <;> simp

private lemma trc_Lw_diff {w : ℕ → ℝ} (hw : WeightClass w) (J : ℕ) {q : ℝ} (hq : 0 ≤ q) :
    0 ≤ Lw w q - Lw (truncW w J) q ∧
      Lw w q - Lw (truncW w J) q ≤ ∑' j, (if j ≤ J then (0:ℝ) else w j) := by
  have hq2 : ∀ j, 0 ≤ w j ^ 2 * q := fun j => mul_nonneg (sq_nonneg _) hq
  refine trc_gen (c := fun j => w j) (f := fun j => w j * Muon.DetEquiv.J (w j ^ 2 * q))
    (g := fun j => truncW w J j * Muon.DetEquiv.J (truncW w J j ^ 2 * q))
    hw.1.2.1 (fun j => mul_nonneg (hw.1.1 j) (trc_J_nonneg (hq2 j)))
    (fun j => mul_le_of_le_one_right (hw.1.1 j) (trc_J_le_one (hq2 j))) J (fun j => ?_)
  unfold truncW
  split_ifs <;> simp

private lemma trc_Lw_lip {w : ℕ → ℝ} (hw : WeightClass w) {q q' : ℝ} (hq : 0 ≤ q) (hq' : 0 ≤ q') :
    |Lw w q - Lw w q'| ≤ 3 * |q - q'| := by
  have hq2 : ∀ j, 0 ≤ w j ^ 2 * q := fun j => mul_nonneg (sq_nonneg _) hq
  have hq2' : ∀ j, 0 ≤ w j ^ 2 * q' := fun j => mul_nonneg (sq_nonneg _) hq'
  have hws : Summable w := hw.1.2.1
  have hsa : Summable (fun j => w j * Muon.DetEquiv.J (w j ^ 2 * q)) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hw.1.1 j) (trc_J_nonneg (hq2 j)))
      (fun j => mul_le_of_le_one_right (hw.1.1 j) (trc_J_le_one (hq2 j))) hws
  have hsb : Summable (fun j => w j * Muon.DetEquiv.J (w j ^ 2 * q')) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (hw.1.1 j) (trc_J_nonneg (hq2' j)))
      (fun j => mul_le_of_le_one_right (hw.1.1 j) (trc_J_le_one (hq2' j))) hws
  have e : Lw w q - Lw w q' = ∑' j, (w j * Muon.DetEquiv.J (w j ^ 2 * q) -
      w j * Muon.DetEquiv.J (w j ^ 2 * q')) := (hsa.tsum_sub hsb).symm
  rw [e, ← Real.norm_eq_abs]
  have hg : HasSum (fun j => 3 * |q - q'| * w j) (3 * |q - q'| * ∑' j, w j) :=
    hws.hasSum.mul_left _
  refine (tsum_of_norm_bounded hg (fun j => ?_)).trans ?_
  · rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hw.1.1 j)]
    have h1 := trc_J_lip (hq2 j) (hq2' j)
    have h2 : |w j ^ 2 * q - w j ^ 2 * q'| = w j ^ 2 * |q - q'| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg _)]
    rw [h2] at h1
    have hwj : w j ^ 2 ≤ 1 := by nlinarith [hw.1.1 j, hw.2.1 j]
    have hab : 0 ≤ |q - q'| := abs_nonneg _
    calc w j * |Muon.DetEquiv.J (w j ^ 2 * q) - Muon.DetEquiv.J (w j ^ 2 * q')|
        ≤ w j * (3 * (w j ^ 2 * |q - q'|)) := mul_le_mul_of_nonneg_left h1 (hw.1.1 j)
      _ ≤ w j * (3 * (1 * |q - q'|)) := by
          apply mul_le_mul_of_nonneg_left _ (hw.1.1 j)
          nlinarith
      _ = 3 * |q - q'| * w j := by ring
  · have := hw.2.2
    have hab : 0 ≤ 3 * |q - q'| := by positivity
    nlinarith

private lemma trc_fro_add {p q : ℕ} (A B : Mat p q) : fro (A + B) ≤ fro A + fro B := by
  have hA := kern_fro_nonneg A
  have hB := kern_fro_nonneg B
  have hAB := kern_fro_nonneg (A + B)
  have h1 : fro (A + B) ^ 2 = ∑ i, ∑ j, A i j * (A + B) i j + ∑ i, ∑ j, B i j * (A + B) i j := by
    rw [kern_sq_sum_eq', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Matrix.add_apply]
    ring
  have h2 := kern_dot_le A (A + B)
  have h3 := kern_dot_le B (A + B)
  by_contra hcon
  push_neg at hcon
  nlinarith

private lemma trc_inv_diff {k : ℕ} (S : Mat k k) (hS : S.PosSemidef) {a b s : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : 0 < s) :
    (s • (1 : Mat k k) + a • S)⁻¹ - (s • (1 : Mat k k) + b • S)⁻¹ =
      (b - a) • ((s • (1 : Mat k k) + a • S)⁻¹ * S * (s • (1 : Mat k k) + b • S)⁻¹) := by
  have hua : IsUnit (s • (1 : Mat k k) + a • S).det :=
    isUnit_iff_ne_zero.mpr (kern_isUnit_det S hS ha hs)
  have hub : IsUnit (s • (1 : Mat k k) + b • S).det :=
    isUnit_iff_ne_zero.mpr (kern_isUnit_det S hS hb hs)
  set Ma : Mat k k := s • (1 : Mat k k) + a • S with hMa
  set Mb : Mat k k := s • (1 : Mat k k) + b • S with hMb
  have h1 : Ma⁻¹ * Ma = 1 := Matrix.nonsing_inv_mul Ma hua
  have h2 : Mb * Mb⁻¹ = 1 := Matrix.mul_nonsing_inv Mb hub
  have hd : Mb - Ma = (b - a) • S := by
    rw [hMa, hMb, sub_smul]
    abel
  calc Ma⁻¹ - Mb⁻¹ = Ma⁻¹ * (Mb * Mb⁻¹) - (Ma⁻¹ * Ma) * Mb⁻¹ := by rw [h1, h2]; simp
    _ = Ma⁻¹ * (Mb - Ma) * Mb⁻¹ := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
    _ = (b - a) • (Ma⁻¹ * S * Mb⁻¹) := by
        rw [hd]
        simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

private lemma trc_X_diff {m n : ℕ} (So : Mat m m) (Si : Mat n n) (hSo : So.PosSemidef)
    (hSi : Si.PosSemidef) (E : Mat m n) {CS : ℝ} (hC : 0 < CS) (hSo' : opNorm So ≤ CS)
    (hSi' : opNorm Si ≤ CS) (hE : fro E ≤ CS) {s a a' c c' : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (ha' : 0 ≤ a') (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    fro ((s • (1 : Mat m m) + a • So)⁻¹ * E * (s • (1 : Mat n n) + c • Si)⁻¹ -
      (s • (1 : Mat m m) + a' • So)⁻¹ * E * (s • (1 : Mat n n) + c' • Si)⁻¹) ≤
      CS ^ 2 / s ^ 3 * (|a - a'| + |c - c'|) := by
  set R := (s • (1 : Mat m m) + a • So)⁻¹ with hR
  set R' := (s • (1 : Mat m m) + a' • So)⁻¹ with hR'
  set Q := (s • (1 : Mat n n) + c • Si)⁻¹ with hQ
  set Q' := (s • (1 : Mat n n) + c' • Si)⁻¹ with hQ'
  have nR : opNorm R ≤ 1 / s := kern_inv_opNorm_le So hSo ha hs
  have nR' : opNorm R' ≤ 1 / s := kern_inv_opNorm_le So hSo ha' hs
  have nQ : opNorm Q ≤ 1 / s := kern_inv_opNorm_le Si hSi hc hs
  have nQ' : opNorm Q' ≤ 1 / s := kern_inv_opNorm_le Si hSi hc' hs
  have z1 := kern_opNorm_nonneg R
  have z2 := kern_opNorm_nonneg R'
  have z3 := kern_opNorm_nonneg Q
  have z4 := kern_opNorm_nonneg Q'
  have z5 := kern_opNorm_nonneg So
  have z6 := kern_opNorm_nonneg Si
  have z7 := kern_fro_nonneg E
  have hs1 : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
  have D1 : R - R' = (a' - a) • (R * So * R') := trc_inv_diff So hSo ha ha' hs
  have D2 : Q - Q' = (c' - c) • (Q * Si * Q') := trc_inv_diff Si hSi hc hc' hs
  have dec : R * E * Q - R' * E * Q' = (R - R') * E * Q + R' * E * (Q - Q') := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  have T1 : (R - R') * E * Q = (a' - a) • (R * (So * (R' * (E * Q)))) := by
    rw [D1]
    simp [Matrix.smul_mul, Matrix.mul_assoc]
  have T2 : R' * E * (Q - Q') = (c' - c) • ((((R' * E) * Q) * Si) * Q') := by
    rw [D2]
    simp [Matrix.mul_smul, Matrix.mul_assoc]
  have B1 : fro (R * (So * (R' * (E * Q)))) ≤ CS ^ 2 / s ^ 3 := by
    have e1 := kern_fro_mul_left R (So * (R' * (E * Q)))
    have e2 := kern_fro_mul_left So (R' * (E * Q))
    have e3 := kern_fro_mul_left R' (E * Q)
    have e4 := kern_fro_mul_right E Q
    calc fro (R * (So * (R' * (E * Q))))
        ≤ opNorm R * (opNorm So * (opNorm R' * (fro E * opNorm Q))) := by
          refine e1.trans (mul_le_mul_of_nonneg_left ?_ z1)
          refine e2.trans (mul_le_mul_of_nonneg_left ?_ z5)
          exact e3.trans (mul_le_mul_of_nonneg_left e4 z2)
      _ ≤ (1 / s) * (CS * ((1 / s) * (CS * (1 / s)))) := by gcongr
      _ = CS ^ 2 / s ^ 3 := by field_simp
  have B2 : fro ((((R' * E) * Q) * Si) * Q') ≤ CS ^ 2 / s ^ 3 := by
    have e1 := kern_fro_mul_right (((R' * E) * Q) * Si) Q'
    have e2 := kern_fro_mul_right ((R' * E) * Q) Si
    have e3 := kern_fro_mul_right (R' * E) Q
    have e4 := kern_fro_mul_left R' E
    calc fro ((((R' * E) * Q) * Si) * Q')
        ≤ (((opNorm R' * fro E) * opNorm Q) * opNorm Si) * opNorm Q' := by
          refine e1.trans (mul_le_mul_of_nonneg_right ?_ z4)
          refine e2.trans (mul_le_mul_of_nonneg_right ?_ z6)
          exact e3.trans (mul_le_mul_of_nonneg_right e4 z3)
      _ ≤ (((1 / s) * CS) * (1 / s) * CS) * (1 / s) := by gcongr
      _ = CS ^ 2 / s ^ 3 := by field_simp
  rw [dec, T1, T2]
  refine (trc_fro_add _ _).trans ?_
  rw [kern_fro_smul, kern_fro_smul]
  have hc0 : 0 ≤ CS ^ 2 / s ^ 3 := by positivity
  have f1 := mul_le_mul_of_nonneg_left B1 (abs_nonneg (a' - a))
  have f2 := mul_le_mul_of_nonneg_left B2 (abs_nonneg (c' - c))
  rw [abs_sub_comm a' a, abs_sub_comm c' c] at *
  nlinarith

private lemma trc_T_diff {CS γ : ℝ} (hC : 0 < CS) (hγ : 0 < γ) {w w' : ℕ → ℝ}
    (hw : WeightClass w) (hw' : WeightClass w') (F : FrozenParams m n B)
    (h : DriftBound F CS γ) {s : ℝ} (hs : 0 < s) :
    fro (Tcand w F (specOutFM F) (specInFM F) s - Tcand w' F (specOutFM F) (specInFM F) s) ≤
      CS / s * |Lw w (branchQ w (specOutFM F) (specInFM F) s) -
        Lw w' (branchQ w' (specOutFM F) (specInFM F) s)| +
      CS ^ 2 / s ^ 2 * (|(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.1| +
        |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.2|) := by
  have hp := spectral_mem_classK F h
  obtain ⟨hSo, hSi, -⟩ := h
  obtain ⟨h1, h2, h3, h4⟩ := kern_isBranch_nonneg
    (branchSol_spec (Fw_admissible hw.1) hC hγ hp hs)
  obtain ⟨h1', h2', h3', h4'⟩ := kern_isBranch_nonneg
    (branchSol_spec (Fw_admissible hw'.1) hC hγ hp hs)
  have hq : 0 ≤ branchQ w (specOutFM F) (specInFM F) s := by
    unfold branchQ; exact mul_nonneg (mul_nonneg hs.le h1) h2
  have hq' : 0 ≤ branchQ w' (specOutFM F) (specInFM F) s := by
    unfold branchQ; exact mul_nonneg (mul_nonneg hs.le h1') h2'
  obtain ⟨L0, L1⟩ := kern_Lw_bounds hw hq
  obtain ⟨L0', L1'⟩ := kern_Lw_bounds hw' hq'
  have hEG := kern_EG_fro_le F hC hSo hSi
  have hXd := trc_X_diff F.C.Sout F.C.Sin F.C.psdOut F.C.psdIn (EG F) hC hSo hSi hEG hs h3 h3' h4 h4'
  have hX : fro (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F
      * Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) ≤ (1 / s) * CS * (1 / s) := by
    have hR := kern_inv_opNorm_le F.C.Sout F.C.psdOut h3 hs
    have hRt := kern_inv_opNorm_le F.C.Sin F.C.psdIn h4 hs
    have hinv : 0 ≤ 1 / s := one_div_nonneg.mpr hs.le
    calc _ ≤ fro (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F)
          * opNorm (Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) := kern_fro_mul_right _ _
      _ ≤ (opNorm (Rbar (Fw w) (specOutFM F) (specInFM F) F.C s) * fro (EG F))
          * opNorm (Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s) :=
          mul_le_mul_of_nonneg_right (kern_fro_mul_left _ _) (kern_opNorm_nonneg _)
      _ ≤ ((1 / s) * CS) * (1 / s) :=
          mul_le_mul (mul_le_mul hR hEG (kern_fro_nonneg _) hinv) hRt (kern_opNorm_nonneg _)
            (mul_nonneg hinv hC.le)
  unfold Tcand
  set X := Rbar (Fw w) (specOutFM F) (specInFM F) F.C s * EG F
      * Rtbar (Fw w) (specOutFM F) (specInFM F) F.C s with hXdef
  set X' := Rbar (Fw w') (specOutFM F) (specInFM F) F.C s * EG F
      * Rtbar (Fw w') (specOutFM F) (specInFM F) F.C s with hXdef'
  set L := Lw w (branchQ w (specOutFM F) (specInFM F) s) with hL
  set L' := Lw w' (branchQ w' (specOutFM F) (specInFM F) s) with hL'
  have hXd' : fro (X - X') ≤ CS ^ 2 / s ^ 3 *
      (|(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.1| +
        |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.2|) := hXd
  have dec : (s * L) • X - (s * L') • X' = (s * (L - L')) • X + (s * L') • (X - X') := by
    rw [mul_sub, sub_smul, smul_sub]
    abel
  rw [dec]
  refine (trc_fro_add _ _).trans ?_
  rw [kern_fro_smul, kern_fro_smul, abs_mul, abs_of_pos hs, abs_mul, abs_of_pos hs,
    abs_of_nonneg L0']
  set Δ := (|(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.1| +
        |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2 -
        (branchSol (Fw w') (specOutFM F) (specInFM F) s).2.2.2|) with hΔ
  have hΔ0 : 0 ≤ Δ := by positivity
  have t1 : s * |L - L'| * fro X ≤ CS / s * |L - L'| := by
    calc s * |L - L'| * fro X ≤ s * |L - L'| * ((1 / s) * CS * (1 / s)) :=
          mul_le_mul_of_nonneg_left hX (by positivity)
      _ = CS / s * |L - L'| := by field_simp
  have t2 : s * L' * fro (X - X') ≤ CS ^ 2 / s ^ 2 * Δ := by
    calc s * L' * fro (X - X') ≤ s * 1 * (CS ^ 2 / s ^ 3 * Δ) :=
          mul_le_mul (mul_le_mul_of_nonneg_left L1' hs.le) hXd' (kern_fro_nonneg _) (by positivity)
      _ = CS ^ 2 / s ^ 2 * Δ := by field_simp
  linarith

private lemma trc_branch_eqs {F : ℝ → ℝ} {ν ν' : FiniteMeasure ℝ} {s : ℝ}
    {x : ℝ × ℝ × ℝ × ℝ} (h : IsBranchSol F ν ν' s x) :
    x.1 = ∫ t, t / (s + x.2.2.1 * t) ∂(ν : Measure ℝ) ∧
    x.2.1 = ∫ t, t / (s + x.2.2.2 * t) ∂(ν' : Measure ℝ) ∧
    x.2.2.1 = s * x.2.1 * F (s * x.1 * x.2.1) ∧
    x.2.2.2 = s * x.1 * F (s * x.1 * x.2.1) := by
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, -, -, e1, e2, e3, e4⟩ := h
  refine ⟨?_, ?_, e3, e4⟩
  · simpa [add_comm] using e1
  · simpa [add_comm] using e2

private lemma trc_sumPow_le {w : ℕ → ℝ} (hw : WeightClass w) : sumPow w 2 ≤ 1 := by
  unfold sumPow
  refine le_trans (Summable.tsum_le_tsum (fun j => ?_) (trc_sq_summable hw) hw.1.2.1) hw.2.2
  nlinarith [hw.1.1 j, hw.2.1 j]

private lemma trc_stab {CS γ ϱlo S0 : ℝ} (hC : 0 < CS) (hγ : 0 < γ) (hlo : 0 < ϱlo)
    {w : ℕ → ℝ} (hw : WeightClass w) :
    ∀ ε1 > 0, ∃ J1 : ℕ, ∀ J : ℕ, J1 ≤ J → ∀ (m' n' B' : ℕ) (F : FrozenParams m' n' B'),
      DriftBound F CS γ → ∀ s ∈ Icc ϱlo S0,
        |(branchSol (Fw w) (specOutFM F) (specInFM F) s).1 -
            (branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s).1| +
          |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.1 -
            (branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s).2.1| +
          |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1 -
            (branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s).2.2.1| +
          |(branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2 -
            (branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s).2.2.2| ≤ ε1 := by
  intro ε1 hε1
  have hF := Fw_admissible hw.1
  have hI : IsCompact (Icc ϱlo S0) := isCompact_Icc
  have hI0 : Icc ϱlo S0 ⊆ Ioi 0 := fun s hs => lt_of_lt_of_le hlo hs.1
  obtain ⟨δ, hδ, hstab⟩ := thm_app_de_branch_iii (𝔟 := γ * CS / ϱlo + γ * CS) hF hC hγ hI hI0
    ε1 hε1
  have hgC : 0 < γ * CS := mul_pos hγ hC
  have hten := trc_tail_tendsto (a := fun j => w j ^ 2) (fun j => sq_nonneg _)
    (trc_sq_summable hw)
  have hev1 : ∀ᶠ J : ℕ in Filter.atTop,
      (∑' j, if j ≤ J then (0:ℝ) else w j ^ 2) < δ / (γ * CS) :=
    hten.eventually (gt_mem_nhds (div_pos hδ hgC))
  obtain ⟨j0, hj0⟩ := hw.1.2.2
  have hev2 : ∀ᶠ J : ℕ in Filter.atTop, j0 ≤ J := Filter.eventually_ge_atTop j0
  obtain ⟨J1, hJ1⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
  refine ⟨J1, fun J hJ m' n' B' F h s hs => ?_⟩
  obtain ⟨hT, hjJ⟩ := hJ1 J hJ
  have hwJ : WeightClass (truncW w J) := trc_class hw ⟨j0, hjJ, hj0⟩
  have hp := spectral_mem_classK F h
  have hspos : 0 < s := lt_of_lt_of_le hlo hs.1
  have hspec := branchSol_spec (Fw_admissible hwJ.1) hC hγ hp hspos
  set x := branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s with hx
  obtain ⟨b1, b2, b3, b4, b5⟩ := (thm_app_de_branch_i_weight hwJ.1 hC hγ _ _ hp s hspos).2 x hspec
  obtain ⟨n1, n2, n3, n4⟩ := kern_isBranch_nonneg hspec
  obtain ⟨e1, e2, e3, e4⟩ := trc_branch_eqs hspec
  have hs1 : sumPow (truncW w J) 2 ≤ 1 := trc_sumPow_le hwJ
  have hbd : γ * CS / s ≤ γ * CS / ϱlo := div_le_div_of_nonneg_left hgC.le hlo hs.1
  have hgb : γ * CS ≤ γ * CS / ϱlo + γ * CS := by
    have : 0 ≤ γ * CS / ϱlo := by positivity
    linarith
  have hsv : s * x.2.1 ≤ γ * CS := by
    calc s * x.2.1 ≤ s * (γ * CS / s) := mul_le_mul_of_nonneg_left b2 hspos.le
      _ = γ * CS := by field_simp
  have hsu : s * x.1 ≤ γ * CS := by
    calc s * x.1 ≤ s * (γ * CS / s) := mul_le_mul_of_nonneg_left b1 hspos.le
      _ = γ * CS := by field_simp
  have hq0 : 0 ≤ s * x.1 * x.2.1 := mul_nonneg (mul_nonneg hspos.le n1) n2
  obtain ⟨d0, d1⟩ := trc_Fw_diff hw J hq0
  have hfin : ∀ y : ℝ, 0 ≤ y → y ≤ γ * CS → y * (∑' j, if j ≤ J then (0:ℝ) else w j ^ 2) ≤ δ := by
    intro y hy0 hy1
    have : y * (∑' j, if j ≤ J then (0:ℝ) else w j ^ 2) ≤ γ * CS * (δ / (γ * CS)) := by
      apply mul_le_mul hy1 hT.le (tsum_nonneg fun j => by split_ifs <;> positivity) hgC.le
    calc _ ≤ _ := this
      _ = δ := by field_simp
  have hres := hstab (specOutFM F) (specInFM F) hp s hs x.1 x.2.1 x.2.2.1 x.2.2.2
    ⟨n1, b1.trans (hbd.trans (by linarith))⟩ ⟨n2, b2.trans (hbd.trans (by linarith))⟩
    ⟨n3, b3.trans (by nlinarith)⟩ ⟨n4, b4.trans (by nlinarith)⟩
    (by rw [← e1]; simp; exact hδ.le)
    (by rw [← e2]; simp; exact hδ.le)
    (by
      rw [e3, ← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hspos.le n2), abs_sub_comm,
        abs_of_nonneg d0]
      calc s * x.2.1 * (Fw w (s * x.1 * x.2.1) - Fw (truncW w J) (s * x.1 * x.2.1))
          ≤ (s * x.2.1) * (∑' j, if j ≤ J then (0:ℝ) else w j ^ 2) :=
            mul_le_mul_of_nonneg_left d1 (mul_nonneg hspos.le n2)
        _ ≤ δ := hfin _ (mul_nonneg hspos.le n2) hsv)
    (by
      rw [e4, ← mul_sub, abs_mul, abs_of_nonneg (mul_nonneg hspos.le n1), abs_sub_comm,
        abs_of_nonneg d0]
      calc s * x.1 * (Fw w (s * x.1 * x.2.1) - Fw (truncW w J) (s * x.1 * x.2.1))
          ≤ (s * x.1) * (∑' j, if j ≤ J then (0:ℝ) else w j ^ 2) :=
            mul_le_mul_of_nonneg_left d1 (mul_nonneg hspos.le n1)
        _ ≤ δ := hfin _ (mul_nonneg hspos.le n1) hsu)
  linarith [abs_sub_comm x.1 (branchSol (Fw w) (specOutFM F) (specInFM F) s).1,
    abs_sub_comm x.2.1 (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.1,
    abs_sub_comm x.2.2.1 (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.1,
    abs_sub_comm x.2.2.2 (branchSol (Fw w) (specOutFM F) (specInFM F) s).2.2.2]

private lemma trc_T_unif {CS γ ϱlo S0 : ℝ} (hC : 0 < CS) (hγ : 0 < γ) (hlo : 0 < ϱlo)
    {w : ℕ → ℝ} (hw : WeightClass w) :
    ∀ ε' > 0, ∃ J2 : ℕ, ∀ J : ℕ, J2 ≤ J → ∀ (m' n' B' : ℕ) (F : FrozenParams m' n' B'),
      DriftBound F CS γ → ∀ s ∈ Icc ϱlo S0,
        fro (Tcand w F (specOutFM F) (specInFM F) s -
          Tcand (truncW w J) F (specOutFM F) (specInFM F) s) ≤ ε' := by
  intro ε' hε'
  set A : ℝ := CS / ϱlo with hA
  have hA0 : 0 < A := div_pos hC hlo
  set K : ℝ := 3 * γ * CS * A + A ^ 2 with hK
  have hK0 : 0 < K := by positivity
  have hε1 : 0 < ε' / (2 * K) := by positivity
  obtain ⟨J1, hJ1⟩ := trc_stab (S0 := S0) hC hγ hlo hw (ε' / (2 * K)) hε1
  have hten := trc_tail_tendsto (a := w) hw.1.1 hw.1.2.1
  have hε3 : 0 < ϱlo * ε' / (2 * CS) := by positivity
  have hev1 : ∀ᶠ J : ℕ in Filter.atTop,
      (∑' j, if j ≤ J then (0:ℝ) else w j) < ϱlo * ε' / (2 * CS) :=
    hten.eventually (gt_mem_nhds hε3)
  obtain ⟨j0, hj0⟩ := hw.1.2.2
  have hev2 : ∀ᶠ J : ℕ in Filter.atTop, j0 ≤ J := Filter.eventually_ge_atTop j0
  obtain ⟨J3, hJ3⟩ := Filter.eventually_atTop.1 (hev1.and hev2)
  refine ⟨max J1 J3, fun J hJ m' n' B' F h s hs => ?_⟩
  obtain ⟨hT, hjJ⟩ := hJ3 J (le_trans (le_max_right _ _) hJ)
  have hwJ : WeightClass (truncW w J) := trc_class hw ⟨j0, hjJ, hj0⟩
  have hst := hJ1 J (le_trans (le_max_left _ _) hJ) m' n' B' F h s hs
  have hp := spectral_mem_classK F h
  have hspos : 0 < s := lt_of_lt_of_le hlo hs.1
  have hdiff := trc_T_diff hC hγ hw hwJ F h hspos
  have hspecw := branchSol_spec (Fw_admissible hw.1) hC hγ hp hspos
  have hspecJ := branchSol_spec (Fw_admissible hwJ.1) hC hγ hp hspos
  obtain ⟨w1, w2, -, -, -⟩ := (thm_app_de_branch_i_weight hw.1 hC hγ _ _ hp s hspos).2 _ hspecw
  obtain ⟨j1, j2, -, -, -⟩ := (thm_app_de_branch_i_weight hwJ.1 hC hγ _ _ hp s hspos).2 _ hspecJ
  obtain ⟨m1, m2, -, -⟩ := kern_isBranch_nonneg hspecw
  obtain ⟨k1, k2, -, -⟩ := kern_isBranch_nonneg hspecJ
  set xw := branchSol (Fw w) (specOutFM F) (specInFM F) s with hxw
  set xJ := branchSol (Fw (truncW w J)) (specOutFM F) (specInFM F) s with hxJ
  have hgC : 0 < γ * CS := mul_pos hγ hC
  have hsw2 : s * xw.2.1 ≤ γ * CS := by
    calc s * xw.2.1 ≤ s * (γ * CS / s) := mul_le_mul_of_nonneg_left w2 hspos.le
      _ = γ * CS := by field_simp
  have hsJ1 : s * xJ.1 ≤ γ * CS := by
    calc s * xJ.1 ≤ s * (γ * CS / s) := mul_le_mul_of_nonneg_left j1 hspos.le
      _ = γ * CS := by field_simp
  have hqw : branchQ w (specOutFM F) (specInFM F) s = s * xw.1 * xw.2.1 := rfl
  have hqJ : branchQ (truncW w J) (specOutFM F) (specInFM F) s = s * xJ.1 * xJ.2.1 := rfl
  have hq0w : 0 ≤ s * xw.1 * xw.2.1 := mul_nonneg (mul_nonneg hspos.le m1) m2
  have hq0J : 0 ≤ s * xJ.1 * xJ.2.1 := mul_nonneg (mul_nonneg hspos.le k1) k2
  -- difference of `q`
  have hqd : |s * xw.1 * xw.2.1 - s * xJ.1 * xJ.2.1| ≤
      γ * CS * (|xw.1 - xJ.1| + |xw.2.1 - xJ.2.1|) := by
    have e : s * xw.1 * xw.2.1 - s * xJ.1 * xJ.2.1 =
        (s * xw.2.1) * (xw.1 - xJ.1) + (s * xJ.1) * (xw.2.1 - xJ.2.1) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul (s * xw.2.1), abs_mul (s * xJ.1), abs_of_nonneg (mul_nonneg hspos.le m2),
      abs_of_nonneg (mul_nonneg hspos.le k1)]
    have := mul_le_mul_of_nonneg_right hsw2 (abs_nonneg (xw.1 - xJ.1))
    have := mul_le_mul_of_nonneg_right hsJ1 (abs_nonneg (xw.2.1 - xJ.2.1))
    nlinarith
  have hL1 := trc_Lw_lip hw hq0w hq0J
  obtain ⟨-, hL2⟩ := trc_Lw_diff hw J hq0J
  obtain ⟨hL2a, -⟩ := trc_Lw_diff hw J hq0J
  have hLd : |Lw w (branchQ w (specOutFM F) (specInFM F) s) -
      Lw (truncW w J) (branchQ (truncW w J) (specOutFM F) (specInFM F) s)| ≤
      3 * (γ * CS * (|xw.1 - xJ.1| + |xw.2.1 - xJ.2.1|)) +
        ∑' j, (if j ≤ J then (0:ℝ) else w j) := by
    rw [hqw, hqJ]
    have e : Lw w (s * xw.1 * xw.2.1) - Lw (truncW w J) (s * xJ.1 * xJ.2.1) =
        (Lw w (s * xw.1 * xw.2.1) - Lw w (s * xJ.1 * xJ.2.1)) +
          (Lw w (s * xJ.1 * xJ.2.1) - Lw (truncW w J) (s * xJ.1 * xJ.2.1)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_of_nonneg hL2a]
    linarith
  -- assemble
  have hΔ := hst
  have a1 := abs_nonneg (xw.1 - xJ.1)
  have a2 := abs_nonneg (xw.2.1 - xJ.2.1)
  have a3 := abs_nonneg (xw.2.2.1 - xJ.2.2.1)
  have a4 := abs_nonneg (xw.2.2.2 - xJ.2.2.2)
  set ε1 := ε' / (2 * K) with hε1def
  have hCs : CS / s ≤ A := div_le_div_of_nonneg_left hC.le hlo hs.1
  have hCs2 : CS ^ 2 / s ^ 2 ≤ A ^ 2 := by
    rw [hA, div_pow]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (pow_le_pow_left₀ hlo.le hs.1 2)
  have hLd' : |Lw w (branchQ w (specOutFM F) (specInFM F) s) -
      Lw (truncW w J) (branchQ (truncW w J) (specOutFM F) (specInFM F) s)| ≤
      3 * γ * CS * ε1 + ϱlo * ε' / (2 * CS) := by
    have : |xw.1 - xJ.1| + |xw.2.1 - xJ.2.1| ≤ ε1 := by linarith
    have h3 : 3 * (γ * CS * (|xw.1 - xJ.1| + |xw.2.1 - xJ.2.1|)) ≤ 3 * γ * CS * ε1 := by
      nlinarith
    linarith
  have hD2 : |xw.2.2.1 - xJ.2.2.1| + |xw.2.2.2 - xJ.2.2.2| ≤ ε1 := by linarith
  refine hdiff.trans ?_
  have hL0 := abs_nonneg (Lw w (branchQ w (specOutFM F) (specInFM F) s) -
      Lw (truncW w J) (branchQ (truncW w J) (specOutFM F) (specInFM F) s))
  have p1 : CS / s * |Lw w (branchQ w (specOutFM F) (specInFM F) s) -
      Lw (truncW w J) (branchQ (truncW w J) (specOutFM F) (specInFM F) s)| ≤
      A * (3 * γ * CS * ε1 + ϱlo * ε' / (2 * CS)) :=
    mul_le_mul hCs hLd' hL0 hA0.le
  have p2 : CS ^ 2 / s ^ 2 * (|xw.2.2.1 - xJ.2.2.1| + |xw.2.2.2 - xJ.2.2.2|) ≤ A ^ 2 * ε1 :=
    mul_le_mul hCs2 hD2 (by positivity) (by positivity)
  have hfin : A * (3 * γ * CS * ε1 + ϱlo * ε' / (2 * CS)) + A ^ 2 * ε1 = ε' := by
    rw [hε1def, hK, hA]
    field_simp
    ring
  linarith

private lemma trc_fro_int {p q : ℕ} (T : ℝ → Mat p q) (g : ℝ → ℝ)
    (hint : ∀ i j, IntegrableOn (fun u : ℝ => T u i j) (Ioi 0))
    (hg : IntegrableOn g (Ioi 0)) (hle : ∀ u ∈ Ioi (0 : ℝ), fro (T u) ≤ g u) :
    fro (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), T u i j) ≤ ∫ u in Ioi (0 : ℝ), g u := by
  set G : Mat p q := Matrix.of fun i j => ∫ u in Ioi (0 : ℝ), T u i j with hG
  obtain ⟨hpi, hpe⟩ := kern_int_pair (fun i j => G i j) T hint
  have hsumint : ∑ i, ∑ j, G i j * G i j =
      ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, G i j * T u i j := by
    rw [hpe]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => rfl
  have hle2 : ∫ u in Ioi (0 : ℝ), ∑ i, ∑ j, G i j * T u i j ≤
      ∫ u in Ioi (0 : ℝ), fro G * g u := by
    refine setIntegral_mono_on hpi (hg.const_mul (fro G)) measurableSet_Ioi fun u hu => ?_
    calc _ ≤ fro G * fro (T u) := kern_dot_le _ _
      _ ≤ fro G * g u := mul_le_mul_of_nonneg_left (hle u hu) (kern_fro_nonneg _)
  rw [integral_const_mul] at hle2
  have hmain : fro G ^ 2 ≤ fro G * ∫ u in Ioi (0 : ℝ), g u := by
    rw [kern_sq_sum_eq' G, hsumint]
    exact hle2
  have hgnn : 0 ≤ ∫ u in Ioi (0 : ℝ), g u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => (kern_fro_nonneg _).trans (hle u hu)
  by_contra hcon
  rw [not_le] at hcon
  have hpos : 0 < fro G := lt_of_le_of_lt hgnn hcon
  nlinarith

private lemma trc_g_int {CS U ε' : ℝ} (hC : 0 < CS) (hU : 0 < U) :
    IntegrableOn (fun u : ℝ => Set.indicator (Ioc 0 U) (fun _ => ε') u +
      Set.indicator (Ioi U) (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹) u) (Ioi 0) ∧
    ∫ u in Ioi (0 : ℝ), (Set.indicator (Ioc 0 U) (fun _ => ε') u +
      Set.indicator (Ioi U) (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹) u) = ε' * U + 2 * CS * U⁻¹ := by
  have hrp : IntegrableOn (fun u : ℝ => u ^ (-2 : ℝ)) (Ioi U) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hU
  have hrpi : ∫ u in Ioi U, u ^ (-2 : ℝ) = U⁻¹ := by
    rw [integral_Ioi_rpow_of_lt (by norm_num) hU]
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
    ring
  have e2 : (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹) = fun u => 2 * CS * u ^ (-2 : ℝ) := by
    ext u
    rw [show (-2 : ℝ) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast, _root_.zpow_neg]
    norm_cast
  have i1 : IntegrableOn (fun _ : ℝ => ε') (Ioc 0 U) := integrableOn_const (by simp)
  have i2 : IntegrableOn (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹) (Ioi U) := by
    rw [e2]; exact hrp.const_mul _
  have s1 : Ioi (0 : ℝ) ∩ Ioc 0 U = Ioc 0 U := by
    ext x; simp only [mem_inter_iff, mem_Ioi, mem_Ioc]; constructor
    · exact fun h => h.2
    · exact fun h => ⟨h.1, h⟩
  have s2 : Ioi (0 : ℝ) ∩ Ioi U = Ioi U := by
    ext x; simp only [mem_inter_iff, mem_Ioi]; constructor
    · exact fun h => h.2
    · exact fun h => ⟨hU.trans h, h⟩
  have j1 : IntegrableOn (Set.indicator (Ioc 0 U) (fun _ : ℝ => ε')) (Ioi 0) :=
    (i1.integrable_indicator measurableSet_Ioc).integrableOn
  have j2 : IntegrableOn (Set.indicator (Ioi U) (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹)) (Ioi 0) :=
    (i2.integrable_indicator measurableSet_Ioi).integrableOn
  refine ⟨j1.add j2, ?_⟩
  rw [integral_add j1 j2, setIntegral_indicator measurableSet_Ioc,
    setIntegral_indicator measurableSet_Ioi, s1, s2, setIntegral_const, Real.volume_real_Ioc,
    e2, integral_const_mul, hrpi]
  rw [max_eq_left (by linarith)]
  simp
  ring

private lemma trc_fro_sub {p q : ℕ} (A B : Mat p q) : fro (A - B) ≤ fro A + fro B := by
  have : A - B = A + (-1 : ℝ) • B := by simp [sub_eq_add_neg]
  rw [this]
  refine (trc_fro_add _ _).trans ?_
  rw [kern_fro_smul]
  simp

/-- `prop:app-drift-truncation`(ii): for a fixed weight sequence `w` in the class of
`eqn:app-de-weightclass`, `lim_{J→∞} sup_B sup_ϱ ‖Ḡ_ϱ − Ḡ^{(J)}_ϱ‖_F = 0`, uniformly over all
frozen models satisfying `DriftBound` (the sup over dimensions `B` is inside the ∀). Stated in
ε–N form, so no `iSup` junk value enters (card §6.11). Snapshot `cr-2026-10-23`. Source, verbatim:
```
\begin{proposition}[History truncation]\label{prop:app-drift-truncation}
Under \cref{assum:app-setup-regime}, for $J\ge0$ let $\emaw j^{(J)}\defeq\emaw j\mathbf 1_{j\le J}$,
let $M^{(J)}=\sum_{j\le J}\emaw jG_{t+1-j}$ be the truncated buffer of
\cref{lem:app-setup-truncation}, and let $T^{(J)}$ and $\Gtildebar^{(J)}_\ridge$
be the candidates \cref{eqn:app-drift-H,eqn:app-drift-Gbar} built from the
solution of the system \cref{eqn:app-de-system} for the weights $\emaw{}^{(J)}$.
\begin{enumerate}[label=(\roman*)]
\item For every fixed $J$,
$\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\EE\,\Qridge\ridge(M^{(J)})-\Gtildebar^{(J)}_\ridge}_\F\to0$
as the dimension grows.
\item $\lim_{J\to\infty}\sup_B\sup_{\ridge\in[\ridge_-,\ridge_+]}\norm{\Gtildebar_\ridge-\Gtildebar^{(J)}_\ridge}_\F=0$,
where $\sup_B$ runs over the whole sequence of dimensions.
\item Consequently
\begin{equation}\label{eqn:app-drift-truncation}
\lim_{J\to\infty}\limsup_{B\to\infty}\sup_{\ridge\in[\ridge_-,\ridge_+]}
\norm{\EE\,\Qridge\ridge(\Mt)-\EE\,\Qridge\ridge(M^{(J)})}_\F=0 .
\end{equation}
\end{enumerate}
\end{proposition}
```
-/
theorem prop_app_drift_truncation_ii {CS γ ϱlo ϱhi : ℝ} (hC : 0 < CS) (hγ : 0 < γ)
    (hlo : 0 < ϱlo) (hle : ϱlo ≤ ϱhi) {w : ℕ → ℝ} (hw : WeightClass w) :
    ∀ ε > 0, ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∀ (m' n' B' : ℕ) (F : FrozenParams m' n' B'),
      DriftBound F CS γ → ∀ ϱ ∈ Icc ϱlo ϱhi,
        fro (Gbar w F (specOutFM F) (specInFM F) ϱ -
          Gbar (truncW w J) F (specOutFM F) (specInFM F) ϱ) ≤ ε := by
  intro ε hε
  obtain ⟨U, hUdef⟩ : ∃ U : ℝ, U = 8 * CS / ε := ⟨_, rfl⟩
  have hU0 : 0 < U := by rw [hUdef]; positivity
  obtain ⟨ε', hε'def⟩ : ∃ ε' : ℝ, ε' = ε / (4 * U) := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; positivity
  obtain ⟨J2, hJ2⟩ := trc_T_unif (S0 := ϱhi + U ^ 2) hC hγ hlo hw ε' hε'0
  obtain ⟨j0, hj0⟩ := hw.1.2.2
  refine ⟨max J2 j0, fun J hJ m' n' B' F h ϱ hϱ => ?_⟩
  have hJ2' : J2 ≤ J := le_trans (le_max_left _ _) hJ
  have hjJ : j0 ≤ J := le_trans (le_max_right _ _) hJ
  have hwJ : WeightClass (truncW w J) := trc_class hw ⟨j0, hjJ, hj0⟩
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hlo hϱ.1
  obtain ⟨hint1, -⟩ := gbar_integrable_bound hC hγ hw F h hϱ0
  obtain ⟨hint2, -⟩ := gbar_integrable_bound hC hγ hwJ F h hϱ0
  have hD : Gbar w F (specOutFM F) (specInFM F) ϱ -
      Gbar (truncW w J) F (specOutFM F) (specInFM F) ϱ =
      (2 / Real.pi) • Matrix.of fun i j => ∫ u in Ioi (0 : ℝ),
        (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) -
          Tcand (truncW w J) F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) i j := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Gbar, Matrix.of_apply, smul_eq_mul]
    rw [← mul_sub, ← integral_sub (hint1 i j) (hint2 i j)]
  rw [hD, kern_fro_smul]
  obtain ⟨hgi, hgv⟩ := trc_g_int (CS := CS) (U := U) (ε' := ε') hC hU0
  have hint : ∀ i j, IntegrableOn (fun u : ℝ =>
      (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) -
        Tcand (truncW w J) F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) i j) (Ioi 0) := by
    intro i j
    exact (hint1 i j).sub (hint2 i j)
  have hpt : ∀ u ∈ Ioi (0 : ℝ), fro (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) -
        Tcand (truncW w J) F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) ≤
      Set.indicator (Ioc 0 U) (fun _ => ε') u +
        Set.indicator (Ioi U) (fun u : ℝ => 2 * CS * (u ^ 2)⁻¹) u := by
    intro u hu
    have hu0 : 0 < u := hu
    have hs0 : 0 < ϱ + u ^ 2 := by positivity
    by_cases huU : u ≤ U
    · rw [Set.indicator_of_mem (show u ∈ Ioc 0 U from ⟨hu0, huU⟩),
        Set.indicator_of_notMem (show u ∉ Ioi U from fun hh => absurd huU (not_le.2 hh)), add_zero]
      refine hJ2 J hJ2' m' n' B' F h (ϱ + u ^ 2) ⟨by nlinarith [hϱ.1, sq_nonneg u], ?_⟩
      have : u ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ hu0.le huU 2
      linarith [hϱ.2]
    · rw [Set.indicator_of_notMem (show u ∉ Ioc 0 U from fun hh => huU hh.2),
        Set.indicator_of_mem (show u ∈ Ioi U from not_le.1 huU), zero_add]
      refine (trc_fro_sub _ _).trans ?_
      have a1 := thm_app_drift_mixed_ii_T hC hγ hw F h hs0
      have a2 := thm_app_drift_mixed_ii_T hC hγ hwJ F h hs0
      have hle2 : CS / (ϱ + u ^ 2) ≤ CS * (u ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) (by linarith)) hC.le
      linarith
  have key := trc_fro_int _ _ hint hgi hpt
  rw [hgv] at key
  have hpi : 2 / Real.pi ≤ 1 := by
    rw [div_le_one Real.pi_pos]
    linarith [Real.pi_gt_three]
  have hpi0 : 0 ≤ 2 / Real.pi := by positivity
  have e1 : ε' * U = ε / 4 := by rw [hε'def]; field_simp
  have e2 : 2 * CS * U⁻¹ = ε / 4 := by rw [hUdef]; field_simp; ring
  rw [e1, e2] at key
  have hfn := kern_fro_nonneg (Matrix.of fun i j => ∫ u in Ioi (0 : ℝ),
        (Tcand w F (specOutFM F) (specInFM F) (ϱ + u ^ 2) -
          Tcand (truncW w J) F (specOutFM F) (specInFM F) (ϱ + u ^ 2)) i j)
  rw [abs_of_nonneg hpi0]
  nlinarith

end Muon.Drift
