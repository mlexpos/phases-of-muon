import Mathlib
import Muon.Foundations.Conventions

/-!
# Foundations: nuclear-norm calculus (task L-0.5c)

Statements only; every proof is `sorry`. Proof routes are in
`muon/phases-of-muon/appendix-nodes/results/L-0.5c-interface.json`.

Snapshot `cr-2026-10-22`. Certificate `NuclearIdeal` (`EXTERNAL-RESULTS.md`; Bhatia IV.2.4,
(IV.40)), to be proved, not certified. Consumers: B `lem:app-de-lipschitz`, C rank lemmas,
E `lem:app-dyn-schatten`.

Nothing is redefined: `Muon.Mat`, `Muon.nuc`, `Muon.opNorm`, `Muon.outer` and `Muon.Vec` come
from `Muon.Foundations.Conventions`. The Euclidean norm of a vector is written explicitly as
`Real.sqrt (∑ i, x i ^ 2)`. Matrix `rank` is Mathlib's `Matrix.rank`.

The variational characterization `nuc K = max {tr(Uᵀ K) : opNorm U ≤ 1}` is stated as
`nuc_isGreatest_dual`; it is the main tool for the proof routes.
-/

open scoped Matrix MatrixOrder

noncomputable section

namespace Muon

/-! ## Elementary calculus -/

/-- Trace of the PSD square root of a Hermitian PSD matrix, as a sum over its roots of
characteristic polynomial (private helper). -/
private lemma trace_cfc_sqrt_eq_roots {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.IsHermitian) (hA0 : 0 ≤ A) :
    (CFC.sqrt A).trace = ((A.charpoly.roots).map Real.sqrt).sum := by
  have hcfc : CFC.sqrt A = hA.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt A hA0, cfcₙ_eq_cfc, hA.cfc_eq]
  rw [hcfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
  rw [hA.roots_charpoly_eq_eigenvalues₀]
  calc ∑ i, √(hA.eigenvalues i)
      = ∑ j : Fin (Fintype.card ι), √(hA.eigenvalues₀ j) :=
        Equiv.sum_comp _ (fun j => √(hA.eigenvalues₀ j))
    _ = _ := by rw [Finset.sum_eq_multiset_sum, Multiset.map_map]; rfl

/-- Sum of square roots of the roots of `(KKᵀ).charpoly` and `(KᵀK).charpoly` agree
(private helper; Sylvester identity `charpoly_mul_comm'`). -/
private lemma sqrt_roots_charpoly_mul_transpose_eq {m n : ℕ} (K : Mat m n) :
    (((K * Kᵀ).charpoly.roots).map Real.sqrt).sum
      = (((Kᵀ * K).charpoly.roots).map Real.sqrt).sum := by
  have hc := Matrix.charpoly_mul_comm' K Kᵀ
  have hne : ∀ k : ℕ, (Polynomial.X ^ k : Polynomial ℝ) ≠ 0 :=
    fun k => pow_ne_zero _ Polynomial.X_ne_zero
  have hP := (Matrix.charpoly_monic (K * Kᵀ)).ne_zero
  have hQ := (Matrix.charpoly_monic (Kᵀ * K)).ne_zero
  have hr := congrArg Polynomial.roots hc
  rw [Polynomial.roots_mul (mul_ne_zero (hne _) hP),
    Polynomial.roots_mul (mul_ne_zero (hne _) hQ),
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at hr
  have := congrArg (fun s => (s.map Real.sqrt).sum) hr
  simpa [Multiset.map_add, Multiset.sum_add, Multiset.nsmul_singleton, Multiset.map_replicate,
    Multiset.sum_replicate] using this

/-- Nonnegativity of the nuclear norm (task L-0.5c; no paper label; snapshot `cr-2026-10-22`).
Standard fact: `nuc K` is a sum of singular values, each `≥ 0`. -/
theorem nuc_nonneg {m n : ℕ} (K : Mat m n) : 0 ≤ nuc K := by
  unfold nuc
  unfold Finsupp.sum
  exact Finset.sum_nonneg fun i _ => LinearMap.singularValues_nonneg _ i

/-- Transpose invariance `‖Kᵀ‖_* = ‖K‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Standard fact: `Kᵀ` and `K` have the same singular values. -/
theorem nuc_transpose {m n : ℕ} (K : Mat m n) : nuc Kᵀ = nuc K := by
  rw [nuc_eq_trace_cfc_sqrt, nuc_eq_trace_cfc_sqrt, Matrix.transpose_transpose]
  have hA : (Kᵀ * K).IsHermitian := by simpa using Matrix.isHermitian_conjTranspose_mul_self K
  have hA0 : 0 ≤ Kᵀ * K := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hB : (K * Kᵀ).IsHermitian := by simpa using Matrix.isHermitian_mul_conjTranspose_self K
  have hB0 : 0 ≤ K * Kᵀ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_self_mul_conjTranspose K
  rw [trace_cfc_sqrt_eq_roots _ hB hB0, trace_cfc_sqrt_eq_roots _ hA hA0]
  exact sqrt_roots_charpoly_mul_transpose_eq K

/-- Homogeneity `‖c K‖_* = |c| ‖K‖_*` (task L-0.5c; no paper label; snapshot `cr-2026-10-22`).
Standard fact: singular values scale by `|c|`. -/
theorem nuc_smul {m n : ℕ} (c : ℝ) (K : Mat m n) : nuc (c • K) = |c| * nuc K := by
  rw [nuc_eq_trace_cfc_sqrt, nuc_eq_trace_cfc_sqrt]
  have hA0 : 0 ≤ Kᵀ * K := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hS : (c • K)ᵀ * (c • K) = (c * c) • (Kᵀ * K) := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hsq : CFC.sqrt ((c * c) • (Kᵀ * K)) = √(c * c) • CFC.sqrt (Kᵀ * K) := by
    have hSS : CFC.sqrt (Kᵀ * K) * CFC.sqrt (Kᵀ * K) = Kᵀ * K :=
      (CFC.sqrt_eq_iff _ _ hA0 (CFC.sqrt_nonneg _)).mp rfl
    refine (CFC.sqrt_eq_iff _ _ ?_ ?_).mpr ?_
    · exact smul_nonneg (mul_self_nonneg c) hA0
    · exact smul_nonneg (Real.sqrt_nonneg _) (CFC.sqrt_nonneg _)
    · rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (mul_self_nonneg c), hSS]
  rw [hS, hsq, Matrix.trace_smul, smul_eq_mul, Real.sqrt_mul_self_eq_abs]

/-! ### Private helpers for the variational characterization (task P-0.5c.P2) -/

private lemma sum_sq_mulVec_eq {p n : ℕ} (M : Matrix (Fin p) (Fin n) ℝ) (c : Fin n → ℝ) :
    ∑ k, (M *ᵥ c) k ^ 2 = ∑ i, ∑ j, (Mᵀ * M) i j * (c i * c j) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, sq,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

private lemma sum_sq_mulVec_le {m n : ℕ} (U : Mat m n) (x : Fin n → ℝ) :
    ∑ k, (U *ᵥ x) k ^ 2 ≤ opNorm U ^ 2 * ∑ i, x i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ≤ opNorm U * ‖WithLp.toLp 2 x‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm (WithLp.toLp 2 x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ x : Fin n → ℝ, ∑ k, (U *ᵥ x) k ^ 2 ≤ M ^ 2 * ∑ i, x i ^ 2) : opNorm U ≤ M := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  show ‖Matrix.toEuclideanLin U x‖ ≤ M * ‖x‖
  have hx := h (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin U x‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using hx
  nlinarith [norm_nonneg (Matrix.toEuclideanLin U x), mul_nonneg hM (norm_nonneg x)]

private lemma sqrt_trace_herm {n : ℕ} (A : Mat n n) (hA : A.IsHermitian) (hA0 : 0 ≤ A) :
    (CFC.sqrt A).trace = ∑ i, √(hA.eigenvalues i) := by
  have hcfc : CFC.sqrt A = hA.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt A hA0, cfcₙ_eq_cfc, hA.cfc_eq]
  rw [hcfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← mul_assoc, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]

/-- Eigen-decomposition data of `Kᵀ K` (private helper). -/
private lemma exists_svd_data {m n : ℕ} (K : Mat m n) :
    ∃ (V : Mat n n) (μ : Fin n → ℝ), Vᵀ * V = 1 ∧ V * Vᵀ = 1 ∧
      Vᵀ * (Kᵀ * K) * V = Matrix.diagonal μ ∧ (∀ i, 0 ≤ μ i) ∧ nuc K = ∑ i, √(μ i) := by
  have hA : (Kᵀ * K).IsHermitian := by simpa using Matrix.isHermitian_conjTranspose_mul_self K
  have hA0 : 0 ≤ Kᵀ * K := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  obtain ⟨V, hV⟩ : ∃ V : Mat n n, V = (hA.eigenvectorUnitary : Mat n n) := ⟨_, rfl⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin n → ℝ, μ = hA.eigenvalues := ⟨_, rfl⟩
  have hstar : star V = Vᵀ := by
    rw [hV, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  have hVV : Vᵀ * V = 1 := by rw [← hstar, hV, Unitary.coe_star_mul_self]
  have hVV' : V * Vᵀ = 1 := by rw [← hstar, hV, ← Unitary.coe_star, Unitary.coe_mul_star_self]
  have hspec : Kᵀ * K = V * Matrix.diagonal μ * Vᵀ := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← hV, hstar, ← hμ]
    rfl
  refine ⟨V, μ, hVV, hVV', ?_, fun i => ?_, ?_⟩
  · rw [hspec]
    calc Vᵀ * (V * Matrix.diagonal μ * Vᵀ) * V = (Vᵀ * V) * Matrix.diagonal μ * (Vᵀ * V) := by
          simp only [Matrix.mul_assoc]
      _ = Matrix.diagonal μ := by rw [hVV, Matrix.one_mul, Matrix.mul_one]
  · rw [hμ]
    exact (hA.posSemidef_iff_eigenvalues_nonneg.mp (Matrix.nonneg_iff_posSemidef.mp hA0)) i
  · rw [nuc_eq_trace_cfc_sqrt, sqrt_trace_herm _ hA hA0, hμ]

private lemma colsq_eq {p n : ℕ} (W : Mat p n) (μ : Fin n → ℝ) (h : Wᵀ * W = Matrix.diagonal μ)
    (i : Fin n) : ∑ k, W k i ^ 2 = μ i := by
  have h2 := congrFun (congrFun h i) i
  rw [Matrix.diagonal_apply_eq] at h2
  rw [← h2]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, sq]

private lemma trace_transpose_mul_eq {p n : ℕ} (Z W : Mat p n) :
    (Zᵀ * W).trace = ∑ i, ∑ k, Z k i * W k i := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

private lemma trace_mul_eq_sum {m n : ℕ} (U K : Mat m n) (V : Mat n n) (hV : V * Vᵀ = 1) :
    (Uᵀ * K).trace = ∑ i, ∑ k, (U * V) k i * (K * V) k i := by
  have e : Uᵀ * K = Uᵀ * K * V * Vᵀ := by
    rw [Matrix.mul_assoc (Uᵀ * K) V Vᵀ, hV, Matrix.mul_one]
  calc (Uᵀ * K).trace = (Uᵀ * K * V * Vᵀ).trace := by rw [← e]
    _ = (Vᵀ * (Uᵀ * K * V)).trace := Matrix.trace_mul_comm _ _
    _ = ((U * V)ᵀ * (K * V)).trace := by simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ∑ i, ∑ k, (U * V) k i * (K * V) k i := trace_transpose_mul_eq _ _

private lemma nuc_upper_aux {m n : ℕ} (K U : Mat m n) (hU : opNorm U ≤ 1) :
    (Uᵀ * K).trace ≤ nuc K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  rw [hnuc, trace_mul_eq_sum U K V hVV']
  apply Finset.sum_le_sum
  intro i _
  have hcol : ∑ k, V k i ^ 2 = 1 := colsq_eq V (fun _ => 1) (by
    rw [hVV]; ext a b; simp [Matrix.one_apply, Matrix.diagonal_apply]) i
  have hZ : ∑ k, (U * V) k i ^ 2 ≤ 1 := by
    have h1 := sum_sq_mulVec_le U (fun k => V k i)
    have e : ∀ k, (U * V) k i = (U *ᵥ fun k => V k i) k := fun k => by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
    have h0 : 0 ≤ opNorm U := by unfold opNorm; exact norm_nonneg _
    have hcol' : ∑ j, (fun k => V k i) j ^ 2 = 1 := hcol
    have h2 : ∑ k, (U *ᵥ fun k => V k i) k ^ 2 ≤ 1 := by
      calc _ ≤ opNorm U ^ 2 * ∑ j, (fun k => V k i) j ^ 2 := h1
        _ = opNorm U ^ 2 * 1 := by rw [hcol']
        _ ≤ 1 := by nlinarith
    simp only [e]
    exact h2
  have hW2 : ∑ k, (K * V) k i ^ 2 = μ i := colsq_eq (K * V) μ hWW i
  calc ∑ k, (U * V) k i * (K * V) k i ≤ |∑ k, (U * V) k i * (K * V) k i| := le_abs_self _
    _ ≤ √((∑ k, (U * V) k i ^ 2) * ∑ k, (K * V) k i ^ 2) :=
        Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)
    _ ≤ √(μ i) := Real.sqrt_le_sqrt (by rw [hW2]; exact mul_le_of_le_one_left (hμ i) hZ)

private lemma nuc_attained_aux {m n : ℕ} (K : Mat m n) :
    ∃ U : Mat m n, opNorm U ≤ 1 ∧ (Uᵀ * K).trace = nuc K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  obtain ⟨s, hs⟩ : ∃ s : Fin n → ℝ, ∀ i, s i = if 0 < μ i then (√(μ i))⁻¹ else 0 :=
    ⟨_, fun i => rfl⟩
  have hms : ∀ i, μ i * s i ^ 2 ≤ 1 := by
    intro i
    by_cases h : 0 < μ i
    · rw [hs i, if_pos h, inv_pow, Real.sq_sqrt (hμ i), mul_inv_cancel₀ h.ne']
    · have h0 : μ i = 0 := le_antisymm (not_lt.mp h) (hμ i)
      rw [hs i, if_neg h, h0]; norm_num
  have hsμ : ∀ i, s i * μ i = √(μ i) := by
    intro i
    by_cases h : 0 < μ i
    · rw [hs i, if_pos h, inv_mul_eq_div, div_eq_iff (Real.sqrt_pos.mpr h).ne']
      exact (Real.mul_self_sqrt (hμ i)).symm
    · have h0 : μ i = 0 := le_antisymm (not_lt.mp h) (hμ i)
      rw [hs i, if_neg h, h0]; simp
  refine ⟨(K * V) * Matrix.diagonal s * Vᵀ, ?_, ?_⟩
  · apply opNorm_le_of_sq _ 1 zero_le_one
    intro x
    have hUx : ((K * V) * Matrix.diagonal s * Vᵀ) *ᵥ x
        = (K * V) *ᵥ (Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have hy : ∑ k, (Vᵀ *ᵥ x) k ^ 2 = ∑ i, x i ^ 2 := by
      rw [sum_sq_mulVec_eq, Matrix.transpose_transpose, hVV']
      simp [Matrix.one_apply, sq]
    rw [hUx, sum_sq_mulVec_eq (K * V), hWW, one_pow, one_mul]
    calc ∑ i, ∑ j, Matrix.diagonal μ i j * ((Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) i
            * (Matrix.diagonal s *ᵥ (Vᵀ *ᵥ x)) j)
        = ∑ i, μ i * (s i * (Vᵀ *ᵥ x) i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [Matrix.diagonal_apply, Matrix.mulVec_diagonal, sq]
      _ = ∑ i, (μ i * s i ^ 2) * (Vᵀ *ᵥ x) i ^ 2 := Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (Vᵀ *ᵥ x) i ^ 2 := Finset.sum_le_sum fun i _ =>
          mul_le_of_le_one_left (sq_nonneg _) (hms i)
      _ = ∑ i, x i ^ 2 := hy
  · have hUV : ((K * V) * Matrix.diagonal s * Vᵀ) * V = (K * V) * Matrix.diagonal s := by
      rw [Matrix.mul_assoc, hVV, Matrix.mul_one]
    rw [trace_mul_eq_sum _ K V hVV', hUV, hnuc]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcs := colsq_eq (K * V) μ hWW i
    calc ∑ k, ((K * V) * Matrix.diagonal s) k i * (K * V) k i
        = s i * ∑ k, (K * V) k i ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Matrix.mul_diagonal]; ring
      _ = s i * μ i := by rw [hcs]
      _ = √(μ i) := hsμ i

private lemma trace_smul_mul_transpose {m n : ℕ} (A : Mat m n) (B : Mat n m) (t : ℝ) :
    ((t • A)ᵀ * Bᵀ).trace = t * (A * B).trace := by
  have hT : (Aᵀ * Bᵀ).trace = (A * B).trace := by
    rw [← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]
  rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, hT]

private lemma opNorm_smul_le_one {m n : ℕ} (A : Mat m n) (t : ℝ)
    (ht : t ^ 2 * opNorm A ^ 2 ≤ 1) : opNorm (t • A) ≤ 1 := by
  apply opNorm_le_of_sq _ 1 zero_le_one
  intro x
  have e : ∑ k, ((t • A) *ᵥ x) k ^ 2 = t ^ 2 * ∑ k, (A *ᵥ x) k ^ 2 := by
    rw [Matrix.smul_mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [e, one_pow, one_mul]
  have hS : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc t ^ 2 * ∑ k, (A *ᵥ x) k ^ 2 ≤ t ^ 2 * (opNorm A ^ 2 * ∑ i, x i ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_sq_mulVec_le A x) (sq_nonneg t)
    _ = (t ^ 2 * opNorm A ^ 2) * ∑ i, x i ^ 2 := by ring
    _ ≤ 1 * ∑ i, x i ^ 2 := mul_le_mul_of_nonneg_right ht hS
    _ = ∑ i, x i ^ 2 := one_mul _

open scoped Matrix.Norms.L2Operator in
private lemma eq_zero_of_opNorm_eq_zero {m n : ℕ} (A : Mat m n) (h : opNorm A = 0) : A = 0 := by
  rw [opNorm_eq_norm] at h
  exact norm_eq_zero.mp h


/-- Triangle inequality `‖K + L‖_* ≤ ‖K‖_* + ‖L‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Standard fact: a norm, from the variational characterization. -/
theorem nuc_add_le {m n : ℕ} (K L : Mat m n) : nuc (K + L) ≤ nuc K + nuc L := by
  obtain ⟨U, hU, htr⟩ := nuc_attained_aux (K + L)
  rw [← htr, Matrix.mul_add, Matrix.trace_add]
  exact add_le_add (nuc_upper_aux K U hU) (nuc_upper_aux L U hU)

/-! ## Variational characterization and trace duality -/

/-- Dual variational characterization (task L-0.5c; no paper label; snapshot `cr-2026-10-22`).
`‖K‖_*` is the maximum of `tr(Uᵀ K)` over all `U` with `‖U‖ ≤ 1`, and the maximum is attained.
Standard fact: `U` is the polar factor of an SVD of `K`; the upper bound follows from the
singular-value decomposition. -/
theorem nuc_isGreatest_dual {m n : ℕ} (K : Mat m n) :
    IsGreatest {t : ℝ | ∃ U : Mat m n, opNorm U ≤ 1 ∧ t = (Uᵀ * K).trace} (nuc K) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨U, hU, h⟩ := nuc_attained_aux K
    exact ⟨U, hU, h.symm⟩
  · rintro t ⟨U, hU, rfl⟩
    exact nuc_upper_aux K U hU

/-- Trace duality `|tr(A B)| ≤ ‖A‖ ‖B‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Source: `section.tex` l.1230 ("By trace duality
`\abs{\Tr(TX)}\le\norm T\norm X_*`"), with a general rectangular pair `A : m × n`, `B : n × m`. -/
theorem trace_mul_le_opNorm_mul_nuc {m n : ℕ} (A : Mat m n) (B : Mat n m) :
    |(A * B).trace| ≤ opNorm A * nuc B := by
  have key : ∀ U : Mat m n, opNorm U ≤ 1 → (Uᵀ * Bᵀ).trace ≤ nuc B := by
    intro U hU
    have h := nuc_upper_aux Bᵀ U hU
    rwa [nuc_transpose] at h
  have hnn : (0 : ℝ) ≤ opNorm A := by unfold opNorm; exact norm_nonneg _
  rcases eq_or_lt_of_le hnn with hc | hc
  · have hA := eq_zero_of_opNorm_eq_zero A hc.symm
    rw [← hc, hA]
    simp
  · have hc' : opNorm A ≠ 0 := hc.ne'
    have h1 := key _ (opNorm_smul_le_one A (opNorm A)⁻¹
      (le_of_eq (by rw [inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc')])))
    have h2 := key _ (opNorm_smul_le_one A (-(opNorm A)⁻¹)
      (le_of_eq (by rw [neg_sq, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hc')])))
    rw [trace_smul_mul_transpose] at h1 h2
    have f1 : (A * B).trace ≤ opNorm A * nuc B := by
      have := mul_le_mul_of_nonneg_left h1 hnn
      rwa [← mul_assoc, mul_inv_cancel₀ hc', one_mul] at this
    have f2 : -(A * B).trace ≤ opNorm A * nuc B := by
      have := mul_le_mul_of_nonneg_left h2 hnn
      have e : opNorm A * (-(opNorm A)⁻¹ * (A * B).trace) = -(A * B).trace := by
        field_simp
      rw [e] at this
      exact this
    exact abs_le.mpr ⟨by linarith, f1⟩

/-! ## Ideal property -/

open scoped Matrix.Norms.L2Operator in
private lemma opNorm_nonneg_aux {m n : ℕ} (K : Mat m n) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
private lemma opNorm_transpose_aux {m n : ℕ} (K : Mat m n) : opNorm Kᵀ = opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

open scoped Matrix.Norms.L2Operator in
private lemma opNorm_mul_le_aux {m n p : ℕ} (A : Mat m n) (B : Mat n p) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

/-- Left ideal property `‖A B‖_* ≤ ‖A‖ ‖B‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Source: Bhatia IV.2.4 and (IV.40), the one-sided case. -/
theorem nuc_mul_le_left {m n p : ℕ} (A : Mat m n) (B : Mat n p) :
    nuc (A * B) ≤ opNorm A * nuc B := by
  obtain ⟨U, hU, htr⟩ := nuc_attained_aux (A * B)
  have hTA : opNorm Aᵀ = opNorm A := opNorm_transpose_aux A
  have hAU : opNorm (Aᵀ * U) ≤ opNorm A := by
    calc opNorm (Aᵀ * U) ≤ opNorm Aᵀ * opNorm U := opNorm_mul_le_aux _ _
      _ ≤ opNorm A * 1 := by
        rw [hTA]
        exact mul_le_mul_of_nonneg_left hU (opNorm_nonneg_aux A)
      _ = opNorm A := mul_one _
  have e : Uᵀ * (A * B) = (Aᵀ * U)ᵀ * B := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [← htr, e]
  have h := trace_mul_le_opNorm_mul_nuc (Aᵀ * U)ᵀ B
  rw [opNorm_transpose_aux] at h
  exact le_trans (le_abs_self _) (le_trans h (mul_le_mul_of_nonneg_right hAU (nuc_nonneg B)))

/-- Right ideal property `‖B A‖_* ≤ ‖B‖_* ‖A‖` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Source: Bhatia IV.2.4 and (IV.40), the other one-sided case. -/
theorem nuc_mul_le_right {m n p : ℕ} (B : Mat m n) (A : Mat n p) :
    nuc (B * A) ≤ nuc B * opNorm A := by
  have h := nuc_mul_le_left Aᵀ Bᵀ
  rw [← Matrix.transpose_mul] at h
  simp only [nuc_transpose, opNorm_transpose_aux] at h
  rw [mul_comm]
  exact h

/-- Three-factor ideal bound `‖X Y Z‖_* ≤ ‖X‖ ‖Y‖_* ‖Z‖` (task L-0.5c; no paper label;
snapshot `cr-2026-10-22`). Source: Bhatia IV.2.4 and (IV.40); used by
`lem:app-de-lipschitz` (`section.tex` l.1104). Corollary of the two one-sided bounds. -/
theorem nuc_mul_three_le {m n p q : ℕ} (X : Mat m n) (Y : Mat n p) (Z : Mat p q) :
    nuc (X * Y * Z) ≤ opNorm X * nuc Y * opNorm Z := by
  have h1 := nuc_mul_le_right (X * Y) Z
  have h2 := nuc_mul_le_left X Y
  exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (opNorm_nonneg_aux Z))

/-! ## Comparison with the operator norm and rank -/

/-- Gram form in a spectral frame (private helper): if `Wᵀ W = diag μ` then
`‖W y‖² = ∑ μ_i y_i²`. -/
private lemma sum_sq_diag_aux {p n : ℕ} (W : Mat p n) (μ : Fin n → ℝ)
    (hWW : Wᵀ * W = Matrix.diagonal μ) (y : Vec n) :
    ∑ k, (W *ᵥ y) k ^ 2 = ∑ i, μ i * y i ^ 2 := by
  rw [sum_sq_mulVec_eq, hWW]
  simp [Matrix.diagonal_apply, sq]

/-- Quadratic form of `Kᵀ K` in an eigenframe `V` of `Kᵀ K` (private helper). -/
private lemma sum_sq_K_eq {m n : ℕ} (K : Mat m n) (V : Mat n n) (μ : Fin n → ℝ)
    (hVV' : V * Vᵀ = 1) (hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ) (x : Vec n) :
    ∑ k, (K *ᵥ x) k ^ 2 = ∑ i, μ i * (Vᵀ *ᵥ x) i ^ 2 := by
  have hx : (K * V) *ᵥ (Vᵀ *ᵥ x) = K *ᵥ x := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hVV', Matrix.mul_one]
  rw [← hx]
  exact sum_sq_diag_aux _ _ hWW _

/-- Operator norm bounded by nuclear norm `‖K‖ ≤ ‖K‖_*` (task L-0.5c; no paper label; snapshot
`cr-2026-10-22`). Standard fact: the largest singular value is at most the sum of all. -/
theorem opNorm_le_nuc {m n : ℕ} (K : Mat m n) : opNorm K ≤ nuc K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  have hμle : ∀ i, μ i ≤ nuc K ^ 2 := by
    intro i
    have h1 : √(μ i) ≤ nuc K := by
      rw [hnuc]
      exact Finset.single_le_sum (fun j _ => Real.sqrt_nonneg _) (Finset.mem_univ i)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    rwa [Real.sq_sqrt (hμ i)] at h2
  refine opNorm_le_of_sq K (nuc K) (nuc_nonneg K) ?_
  intro x
  rw [sum_sq_K_eq K V μ hVV' hWW x]
  have hy : ∑ i, (Vᵀ *ᵥ x) i ^ 2 = ∑ i, x i ^ 2 := by
    rw [sum_sq_mulVec_eq, Matrix.transpose_transpose, hVV']
    simp [Matrix.one_apply, sq]
  calc ∑ i, μ i * (Vᵀ *ᵥ x) i ^ 2 ≤ ∑ i, nuc K ^ 2 * (Vᵀ *ᵥ x) i ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hμle i) (sq_nonneg _)
    _ = nuc K ^ 2 * ∑ i, x i ^ 2 := by rw [← hy, Finset.mul_sum]

/-- Nuclear norm bounded by rank times operator norm `‖K‖_* ≤ rank K · ‖K‖` (task L-0.5c;
no paper label; snapshot `cr-2026-10-22`). Standard fact: at most `rank K` singular values are
nonzero and each is at most `‖K‖`. Used by the rank lemmas of section C. -/
theorem nuc_le_rank_mul_opNorm {m n : ℕ} (K : Mat m n) :
    nuc K ≤ (Matrix.rank K : ℝ) * opNorm K := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := exists_svd_data K
  have hWW : (K * V)ᵀ * (K * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  -- each singular value is at most `‖K‖`: test on the i-th column of `V`
  have hopμ : ∀ i, √(μ i) ≤ opNorm K := by
    intro i
    have hyx : ∀ j, (Vᵀ *ᵥ (fun k => V k i)) j = if j = i then 1 else 0 := by
      intro j
      have h := congrFun (congrFun hVV j) i
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.mulVec, dotProduct] using h
    have hxn : ∑ k, (fun k => V k i) k ^ 2 = 1 := by
      have h := congrFun (congrFun hVV i) i
      simpa [Matrix.mul_apply, Matrix.one_apply, sq] using h
    have e := sum_sq_K_eq K V μ hVV' hWW (fun k => V k i)
    simp only [hyx] at e
    simp at e
    have hμi : μ i ≤ opNorm K ^ 2 := by
      calc μ i = ∑ k, (K *ᵥ fun k => V k i) k ^ 2 := e.symm
        _ ≤ opNorm K ^ 2 * ∑ k, (fun k => V k i) k ^ 2 := sum_sq_mulVec_le K (fun k => V k i)
        _ = opNorm K ^ 2 := by rw [hxn, mul_one]
    calc √(μ i) ≤ √(opNorm K ^ 2) := Real.sqrt_le_sqrt hμi
      _ = opNorm K := Real.sqrt_sq (by unfold opNorm; exact norm_nonneg _)
  -- rank of `K` is the number of nonzero singular values
  have hrk : Matrix.rank K = (Finset.univ.filter (fun i => μ i ≠ 0)).card := by
    have hVu : IsUnit V.det := Matrix.isUnit_det_of_right_inverse hVV'
    have hVTu : IsUnit Vᵀ.det := Matrix.isUnit_det_of_right_inverse hVV
    have hc : (Kᵀ * K).rank = (Matrix.diagonal μ).rank := by
      rw [← hWV, Matrix.rank_mul_eq_left_of_isUnit_det V (Vᵀ * (Kᵀ * K)) hVu,
        Matrix.rank_mul_eq_right_of_isUnit_det Vᵀ (Kᵀ * K) hVTu]
    rw [← Matrix.rank_transpose_mul_self K, hc, Matrix.rank_diagonal, Fintype.card_subtype]
  have hsum : ∑ i, √(μ i) = ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), √(μ i) :=
    (Finset.sum_filter_of_ne (p := fun i => μ i ≠ 0) fun i _ h hμ0 =>
      h (by rw [hμ0, Real.sqrt_zero])).symm
  rw [hnuc, hsum]
  calc ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), √(μ i)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => μ i ≠ 0), opNorm K :=
        Finset.sum_le_sum fun i _ => hopμ i
    _ = ((Finset.univ.filter (fun i => μ i ≠ 0)).card : ℝ) * opNorm K := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Matrix.rank K : ℝ) * opNorm K := by rw [hrk]

/-! ## Rank-one matrices -/

/-- Nuclear norm of an outer product `‖x ⊗ y‖_* = ‖x‖ ‖y‖` (task L-0.5c; no paper label;
snapshot `cr-2026-10-22`). Here `x ⊗ y = Muon.outer x y = x yᵀ` and the Euclidean norms are
written as `Real.sqrt (∑ i, x i ^ 2)` and `Real.sqrt (∑ j, y j ^ 2)`. The outer product has
rank at most one, with its single nonzero singular value equal to `‖x‖ ‖y‖`. -/
theorem nuc_outer {m n : ℕ} (x : Vec m) (y : Vec n) :
    nuc (outer x y) = Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ j, y j ^ 2) := by
  obtain ⟨V, μ, hVV, hVV', hWV, hμ, hnuc⟩ := exists_svd_data (outer x y)
  have hWW : (outer x y * V)ᵀ * (outer x y * V) = Matrix.diagonal μ := by
    rw [← hWV]; simp only [Matrix.transpose_mul, Matrix.mul_assoc]
  set s : ℝ := ∑ i, x i ^ 2 with hs_def
  set t : ℝ := ∑ j, y j ^ 2 with ht_def
  set z : Vec n := Vᵀ *ᵥ y with hz_def
  -- `outer x y * V = x (Vᵀ y)ᵀ`, a rank-one matrix
  have hW : ∀ k i, (outer x y * V) k i = x k * z i := by
    intro k i
    simp only [Matrix.mul_apply, outer, Matrix.vecMulVec_apply, hz_def, Matrix.mulVec,
      dotProduct, Matrix.transpose_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => by ring
  have hgram : ∀ i j, ((outer x y * V)ᵀ * (outer x y * V)) i j = s * (z i * z j) := by
    intro i j
    rw [Matrix.mul_apply, hs_def, Finset.sum_mul]
    simp only [Matrix.transpose_apply, hW]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hμe : ∀ i, μ i = s * (z i * z i) := by
    intro i
    have e := congrFun (congrFun hWW i) i
    rw [Matrix.diagonal_apply_eq, hgram] at e
    exact e.symm
  have hcross : ∀ i j, i ≠ j → μ i * μ j = 0 := by
    intro i j hij
    have e := congrFun (congrFun hWW i) j
    rw [Matrix.diagonal_apply_ne μ hij, hgram] at e
    rw [hμe i, hμe j]
    calc s * (z i * z i) * (s * (z j * z j)) = (s * (z i * z j)) * (s * (z i * z j)) := by ring
      _ = 0 := by rw [e, zero_mul]
  have hz : ∑ i, z i ^ 2 = t := by
    rw [ht_def, hz_def, sum_sq_mulVec_eq, Matrix.transpose_transpose, hVV']
    simp [Matrix.one_apply, sq]
  have hμsum : ∑ i, μ i = s * t := by
    rw [← hz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hμe i]; ring
  have hcross' : ∀ i j, j ≠ i → √(μ i) * √(μ j) = 0 := fun i j hj => by
    rw [← Real.sqrt_mul (hμ i), hcross i j (Ne.symm hj), Real.sqrt_zero]
  have hsq : (∑ i, √(μ i)) ^ 2 = s * t := by
    rw [← hμsum]
    calc (∑ i, √(μ i)) ^ 2 = ∑ i, ∑ j, √(μ i) * √(μ j) := by rw [sq, Finset.sum_mul_sum]
      _ = ∑ i, μ i := Finset.sum_congr rfl fun i _ => by
          rw [Finset.sum_eq_single (f := fun j => √(μ i) * √(μ j)) i
              (fun j _ hj => hcross' i j hj) (fun h => absurd (Finset.mem_univ i) h),
            Real.mul_self_sqrt (hμ i)]
  have hnn : 0 ≤ nuc (outer x y) := nuc_nonneg _
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hnsq : nuc (outer x y) ^ 2 = s * t := by rw [hnuc]; exact hsq
  calc nuc (outer x y) = √(nuc (outer x y) ^ 2) := (Real.sqrt_sq hnn).symm
    _ = √(s * t) := by rw [hnsq]
    _ = √s * √t := Real.sqrt_mul hs0 t

end Muon

end
