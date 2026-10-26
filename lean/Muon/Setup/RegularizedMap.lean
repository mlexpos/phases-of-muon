import Muon.Setup.Basic
import Muon.Foundations.SVD
import Muon.Foundations.OperatorLipschitz
import Muon.Foundations.Nuclear

/-!
# Appendix A: the regularized SignSVD map (filter, contour, scaling)

Snapshot `cr-2026-10-23`. Source: `sections/01-setup/section.tex`: `lem:app-setup-filter` (l.281–295),
`lem:app-setup-contour` (l.352–358), `prop:app-setup-scaling` (l.378–389). Card:
`sections/01-setup/CARD.md` §2 (`Q`), §3 rows, §5 row L-A.2.

The map `Q` (`eqn:app-setup-Q`) is not redefined here: every statement uses `Muon.Q` from
`Muon.Foundations.Conventions`, whose bridge lemma `Q_eq_inv_sqrt_mul` is reused as is.
Proof bodies are `sorry` until the SVD and operator-Lipschitz foundations (L-A.F1, L-A.F2) land,
except where noted.

Reading of `Q_ϱ` at `ϱ = 0` and of the indices: `Real.rpow` gives `φ_ϱ(0) = 0`, the paper's
convention; in `prop:app-setup-scaling`(iii) the Lean sequences are shifted, `M (t+1) = M_t`,
`M 0 = M_{-1}`, and `G t = G_{t+1}` (an arbitrary sequence, so the reindexing is harmless).
-/

noncomputable section

open scoped Matrix MatrixOrder
open Matrix MeasureTheory Filter Topology Set

namespace Muon.Setup

/-! ## Filter bounds and Lipschitz estimate (`lem:app-setup-filter`) -/

/-- Helper: if `A X = 0` then `f(A) X = f(0) X` for self-adjoint `A` (Lagrange interpolation
on the finite spectrum together with `0`). -/
private lemma cfc_mul_eq_smul_of_mul_eq_zero_aux {n : ℕ} (f : ℝ → ℝ) (A X : Mat n n)
    (hA : IsSelfAdjoint A) (hX : A * X = 0) :
    cfc f A * X = f 0 • X := by
  classical
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  set T : Finset ℝ := insert 0 hfin.toFinset with hT
  have hinj : Set.InjOn (id : ℝ → ℝ) (T : Set ℝ) := Set.injOn_id _
  set p : Polynomial ℝ := Lagrange.interpolate T id f with hp
  have hcongr : cfc f A = cfc p.eval A := by
    refine cfc_congr' fun x hx => ?_
    have hxT : x ∈ T := Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hx)
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj hxT
    simpa [hp] using this.symm
  have h0 : p.eval 0 = f 0 := by
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj
      (Finset.mem_insert_self 0 _)
    simpa [hp] using this
  rw [hcongr, cfc_polynomial p A hA, Polynomial.aeval_eq_sum_range, Finset.sum_mul,
    Finset.sum_range_succ']
  have hz : ∀ i : ℕ, (p.coeff (i + 1) • A ^ (i + 1)) * X = 0 := by
    intro i
    rw [Matrix.smul_mul, pow_succ, Matrix.mul_assoc, hX, Matrix.mul_zero, smul_zero]
  simp only [hz, Finset.sum_const_zero, zero_add, pow_zero]
  rw [Matrix.smul_mul, Matrix.one_mul, ← h0, Polynomial.coeff_zero_eq_eval_zero]

private lemma cfc_mulVec_eq_smul_aux {n : ℕ} (f : ℝ → ℝ) (A : Mat n n) (c : ℝ) (x : Vec n)
    (hA : IsSelfAdjoint A) (hx : A *ᵥ x = c • x) : cfc f A *ᵥ x = f c • x := by
  classical
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  set T : Finset ℝ := insert c hfin.toFinset with hT
  have hinj : Set.InjOn (id : ℝ → ℝ) (T : Set ℝ) := Set.injOn_id _
  set p : Polynomial ℝ := Lagrange.interpolate T id f with hp
  have hcongr : cfc f A = cfc p.eval A := by
    refine cfc_congr' fun y hy => ?_
    have hyT : y ∈ T := Finset.mem_insert_of_mem (hfin.mem_toFinset.mpr hy)
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj hyT
    simpa [hp] using this.symm
  have hc : p.eval c = f c := by
    have := Lagrange.eval_interpolate_at_node (s := T) (v := id) (r := f) hinj
      (Finset.mem_insert_self c _)
    simpa [hp] using this
  have hpow : ∀ i : ℕ, (A ^ i) *ᵥ x = c ^ i • x := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [pow_succ, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul, ih, smul_smul, pow_succ,
        mul_comm]
  rw [hcongr, cfc_polynomial p A hA, Polynomial.aeval_eq_sum_range, Matrix.sum_mulVec]
  simp only [Matrix.smul_mulVec, hpow, smul_smul]
  rw [← Finset.sum_smul, ← hc, Polynomial.eval_eq_sum_range]

private lemma svd_mulVec_aux {m n r : ℕ} (K : Mat m n) (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) (l : Fin r) :
    K *ᵥ q l = s l • p l ∧ Kᵀ *ᵥ p l = s l • q l := by
  constructor
  · rw [hK, Matrix.sum_mulVec]
    simp only [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, hq, smul_smul]
    simp [Finset.sum_ite_eq', mul_comm]
  · rw [hK, Matrix.transpose_sum, Matrix.sum_mulVec]
    simp only [Matrix.transpose_smul, Matrix.smul_mulVec, Matrix.transpose_vecMulVec,
      Matrix.vecMulVec_mulVec, hp, smul_smul]
    simp [Finset.sum_ite_eq', mul_comm]

private lemma Q_eq_svd_aux {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) {r : ℕ} (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n) (hs : ∀ k, 0 < s k)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (q k) := by
  have hsa : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set φ : ℝ → ℝ := fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ)) with hφ
  set C := cfc φ (Kᵀ * K) with hC
  have hCt : Cᵀ = C := by
    have h : IsSelfAdjoint C := cfc_predicate φ (Kᵀ * K)
    have h2 := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  have hvec : ∀ l, vecMul (q l) C = φ (s l ^ 2) • q l := by
    intro l
    obtain ⟨h1, h2⟩ := svd_mulVec_aux K s p q hp hq hK l
    have hev : (Kᵀ * K) *ᵥ q l = (s l ^ 2) • q l := by
      rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_smul, h2, smul_smul, sq]
    rw [← Matrix.mulVec_transpose, hCt]
    exact cfc_mulVec_eq_smul_aux φ _ _ _ hsa hev
  unfold Q
  rw [← hC, hK]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.smul_mul, Matrix.vecMulVec_mul, hvec k, Matrix.vecMulVec_smul, smul_smul]
  congr 1
  have hpos : 0 ≤ s k ^ 2 + ϱ := by positivity
  simp only [hφ]
  rw [Real.rpow_neg hpos, ← Real.sqrt_eq_rpow, div_eq_mul_inv]


private lemma svd_fro_sq_aux {m n r : ℕ} (c : Fin r → ℝ) (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) :
    fro (∑ k, c k • outer (p k) (q k)) ^ 2 = ∑ k, c k ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  have hrow : ∀ i : Fin m, ∑ j : Fin n, ‖(∑ k, c k • outer (p k) (q k)) i j‖ ^ 2
      = ∑ k, c k ^ 2 * p k i ^ 2 := by
    intro i
    have h1 : ∀ j, (∑ k, c k • outer (p k) (q k)) i j = (∑ k, (c k * p k i) • q k) j := by
      intro j
      simp [Matrix.sum_apply, Finset.sum_apply, Matrix.vecMulVec_apply, mul_assoc]
    have h2 : (∑ k, (c k * p k i) • q k) ⬝ᵥ (∑ k, (c k * p k i) • q k) = ∑ k, c k ^ 2 * p k i ^ 2 := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dotProduct_sum]
      simp only [smul_dotProduct, dotProduct_smul, hq, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
    rw [← h2]
    simp only [dotProduct, h1, Real.norm_eq_abs, sq_abs]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have := hp k k
  simp only [if_true, dotProduct] at this
  rw [← Finset.mul_sum]
  simp only [sq] at this ⊢
  rw [this, mul_one]


private lemma bessel_aux {n r : ℕ} (q : Fin r → Vec n)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) (x : Vec n) :
    ∑ k, (q k ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set y : Vec n := x - ∑ k, (q k ⬝ᵥ x) • q k with hy
  have h0 : 0 ≤ y ⬝ᵥ y := by
    simp only [dotProduct, ← sq]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hx1 : x ⬝ᵥ (∑ k, (q k ⬝ᵥ x) • q k) = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_smul, dotProduct_comm x (q k), smul_eq_mul, sq]
  have hx2 : (∑ k, (q k ⬝ᵥ x) • q k) ⬝ᵥ (∑ k, (q k ⬝ᵥ x) • q k) = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dotProduct_sum]
    simp only [smul_dotProduct, dotProduct_smul, hq, smul_eq_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    ring
  have hexp : y ⬝ᵥ y = x ⬝ᵥ x - ∑ k, (q k ⬝ᵥ x) ^ 2 := by
    have hx1' : (∑ k, (q k ⬝ᵥ x) • q k) ⬝ᵥ x = ∑ k, (q k ⬝ᵥ x) ^ 2 := by
      rw [dotProduct_comm]; exact hx1
    rw [hy, sub_dotProduct, dotProduct_sub, dotProduct_sub, hx1, hx2, hx1']
    ring
  linarith

private lemma svd_opNorm_le_aux {m n r : ℕ} (c : Fin r → ℝ) (hc : ∀ k, |c k| ≤ 1)
    (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) :
    opNorm (∑ k, c k • outer (p k) (q k)) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  set M : Mat m n := ∑ k, c k • outer (p k) (q k) with hM
  have hcoe : ∀ z : EuclideanSpace ℝ (Fin n),
      ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) z : Fin m → ℝ)
        = M *ᵥ (z : Fin n → ℝ) := by
    intro z
    simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
  have hMx : M *ᵥ (x : Fin n → ℝ) = ∑ k, (c k * (q k ⬝ᵥ (x : Fin n → ℝ))) • p k := by
    rw [hM, Matrix.sum_mulVec]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul]
  have hcoe' : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) x) i
      = (M *ᵥ (x : Fin n → ℝ)) i := fun i => congrFun (hcoe x) i
  have hnorm : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) x‖ ^ 2
      = ∑ k, (c k * (q k ⬝ᵥ (x : Fin n → ℝ))) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp only [hcoe']
    rw [hMx]
    have h2 : (∑ k, (c k * (q k ⬝ᵥ (x : Fin n → ℝ))) • p k) ⬝ᵥ
        (∑ k, (c k * (q k ⬝ᵥ (x : Fin n → ℝ))) • p k)
        = ∑ k, (c k * (q k ⬝ᵥ (x : Fin n → ℝ))) ^ 2 := by
      rw [sum_dotProduct]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [dotProduct_sum]
      simp only [smul_dotProduct, dotProduct_smul, hp, smul_eq_mul, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring
    rw [← h2]
    simp [dotProduct, sq]
  have hxn : ‖x‖ ^ 2 = (x : Fin n → ℝ) ⬝ᵥ (x : Fin n → ℝ) := by
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [dotProduct, sq]
  have hle : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin M)) x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [hnorm, hxn]
    refine le_trans (Finset.sum_le_sum fun k _ => ?_) (bessel_aux q hq _)
    rw [mul_pow]
    have : c k ^ 2 ≤ 1 := by
      have := hc k
      nlinarith [abs_nonneg (c k), sq_abs (c k)]
    nlinarith [sq_nonneg (q k ⬝ᵥ (x : Fin n → ℝ))]
  rw [one_mul]
  exact le_of_sq_le_sq (by simpa using hle) (norm_nonneg _)


/-- `lem:app-setup-filter`, part (i). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.281–295:

    \begin{lemma}[Filter bounds and Lipschitz estimate]\label{lem:app-setup-filter}
    Let $K,L\in\R^{\Nout\times\Nin}$.
    \begin{enumerate}[label=(\roman*)]
    \item For $\ridge\ge0$: $\norm{\Qridge\ridge(K)}\le1$ and
    $\norm{\Qridge\ridge(K)}_\F^2\le\rank K\le\min(\Nout,\Nin)$, with equality
    $\norm{\Qridge0(K)}_\F^2=\rank K$.
    \item For $\ridge\ge0$, if $P\in\R^{\Nout\times\Nout}$ and $P'\in\R^{\Nin\times\Nin}$
    are orthogonal projections with $K=PKP'$, then $\Qridge\ridge(K)=P\Qridge\ridge(K)P'$.
    \item For $\ridge>0$,
    \begin{equation}\label{eqn:app-setup-lipschitz}
    \norm{\Qridge\ridge(K)-\Qridge\ridge(L)}_\F\le\ridge^{-1/2}\norm{K-L}_\F .
    \end{equation}
    \item $\Qridge\ridge(K)\to\Qridge0(K)$ as $\ridge\downarrow0$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_setup_filter_i {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) :
    opNorm (Q ϱ K) ≤ 1 ∧ fro (Q ϱ K) ^ 2 ≤ (K.rank : ℝ) ∧ K.rank ≤ min m n ∧
      fro (Q 0 K) ^ 2 = (K.rank : ℝ) := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  have hs : ∀ k : Fin K.rank, 0 < (Matrix.toEuclideanLin K).singularValues (k : ℕ) :=
    fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.2
  have hQ : ∀ ϱ' : ℝ, 0 ≤ ϱ' → Q ϱ' K = ∑ k : Fin K.rank,
      ((Matrix.toEuclideanLin K).singularValues (k : ℕ) /
        Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + ϱ')) • outer (p k) (r k) :=
    fun ϱ' h => Q_eq_svd_aux ϱ' h K _ p r hs hp hr hK
  have hc : ∀ k : Fin K.rank, ∀ ϱ' : ℝ, 0 ≤ ϱ' →
      0 ≤ (Matrix.toEuclideanLin K).singularValues (k : ℕ) /
        Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + ϱ') ∧
      (Matrix.toEuclideanLin K).singularValues (k : ℕ) /
        Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + ϱ') ≤ 1 := by
    intro k ϱ' h
    have h0 := hs k
    have hpos : 0 < Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + ϱ') :=
      Real.sqrt_pos.mpr (by positivity)
    refine ⟨div_nonneg h0.le hpos.le, (div_le_one hpos).mpr ?_⟩
    calc (Matrix.toEuclideanLin K).singularValues (k : ℕ)
        = Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2) :=
          (Real.sqrt_sq h0.le).symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  have hrank : K.rank ≤ min m n := le_min (Matrix.rank_le_height K) (Matrix.rank_le_width K)
  refine ⟨?_, ?_, hrank, ?_⟩
  · rw [hQ ϱ hϱ]
    exact svd_opNorm_le_aux _ (fun k => by
      rw [abs_of_nonneg (hc k ϱ hϱ).1]; exact (hc k ϱ hϱ).2) p r hp hr
  · rw [hQ ϱ hϱ, svd_fro_sq_aux _ p r hp hr]
    calc ∑ k : Fin K.rank, ((Matrix.toEuclideanLin K).singularValues (k : ℕ) /
          Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + ϱ)) ^ 2
        ≤ ∑ _k : Fin K.rank, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
          have := hc k ϱ hϱ
          nlinarith [this.1, this.2]
      _ = (K.rank : ℝ) := by simp
  · rw [hQ 0 le_rfl, svd_fro_sq_aux _ p r hp hr]
    have h1 : ∀ k : Fin K.rank, ((Matrix.toEuclideanLin K).singularValues (k : ℕ) /
          Real.sqrt ((Matrix.toEuclideanLin K).singularValues (k : ℕ) ^ 2 + 0)) = 1 := by
      intro k
      rw [add_zero, Real.sqrt_sq (hs k).le, div_self (hs k).ne']
    rw [Finset.sum_congr rfl (fun k _ => by rw [h1 k])]
    simp


/-- `lem:app-setup-filter`, part (ii). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.281–295:

    \begin{lemma}[Filter bounds and Lipschitz estimate]\label{lem:app-setup-filter}
    Let $K,L\in\R^{\Nout\times\Nin}$.
    \begin{enumerate}[label=(\roman*)]
    \item For $\ridge\ge0$: $\norm{\Qridge\ridge(K)}\le1$ and
    $\norm{\Qridge\ridge(K)}_\F^2\le\rank K\le\min(\Nout,\Nin)$, with equality
    $\norm{\Qridge0(K)}_\F^2=\rank K$.
    \item For $\ridge\ge0$, if $P\in\R^{\Nout\times\Nout}$ and $P'\in\R^{\Nin\times\Nin}$
    are orthogonal projections with $K=PKP'$, then $\Qridge\ridge(K)=P\Qridge\ridge(K)P'$.
    \item For $\ridge>0$,
    \begin{equation}\label{eqn:app-setup-lipschitz}
    \norm{\Qridge\ridge(K)-\Qridge\ridge(L)}_\F\le\ridge^{-1/2}\norm{K-L}_\F .
    \end{equation}
    \item $\Qridge\ridge(K)\to\Qridge0(K)$ as $\ridge\downarrow0$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_setup_filter_ii {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n)
    (P : Mat m m) (P' : Mat n n) (hP : Pᵀ = P) (hP2 : P * P = P)
    (hP' : P'ᵀ = P') (hP'2 : P' * P' = P') (hK : K = P * K * P') :
    Q ϱ K = P * Q ϱ K * P' := by
  have hKP' : K * P' = K := by
    calc K * P' = (P * K * P') * P' := by rw [← hK]
      _ = P * K * (P' * P') := by simp only [Matrix.mul_assoc]
      _ = K := by rw [hP'2, ← hK]
  have hPK : P * K = K := by
    calc P * K = P * (P * K * P') := by rw [← hK]
      _ = (P * P) * K * P' := by simp only [Matrix.mul_assoc]
      _ = K := by rw [hP2, ← hK]
  have hsa : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hA : (Kᵀ * K) * (1 - P') = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, hKP', sub_self]
  have hKB : K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) * (1 - P') = 0 := by
    rw [Matrix.mul_assoc, cfc_mul_eq_smul_of_mul_eq_zero_aux _ _ _ hsa hA, Matrix.mul_smul,
      Matrix.mul_sub, Matrix.mul_one, hKP', sub_self, smul_zero]
  have hMP : K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) * P'
      = K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) := by
    have h := hKB
    rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h
    exact h.symm
  have h2 : P * (K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K))
      = K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K) := by
    rw [← Matrix.mul_assoc, hPK]
  unfold Q
  rw [h2, hMP]


private lemma abs_entry_le_fro_aux {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    |A i j| ≤ fro A := by
  unfold fro
  refine Real.le_sqrt_of_sq_le ?_
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  have : |A i j| ^ 2 = ‖A i j‖ ^ 2 := by rw [Real.norm_eq_abs]
  linarith

open scoped Matrix.Norms.Frobenius in
private lemma fro_add_le_aux {m n : ℕ} (A B : Mat m n) : fro (A + B) ≤ fro A + fro B := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]
  exact norm_add_le A B

private lemma fro_sub_le_aux {m n : ℕ} (A B C : Mat m n) :
    fro (A - C) ≤ fro (A - B) + fro (B - C) := by
  have := fro_add_le_aux (A - B) (B - C)
  rwa [sub_add_sub_cancel] at this

private lemma continuous_fro_sub_aux {m n : ℕ} (K0 : Mat m n) :
    Continuous (fun K : Mat m n => fro (K - K0)) := by
  unfold fro
  refine Real.continuous_sqrt.comp ?_
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  have : Continuous fun K : Mat m n => (K - K0) i j := by
    simp only [Matrix.sub_apply]
    exact (continuous_id.matrix_elem i j).sub continuous_const
  exact this.norm.pow 2

private lemma continuousAt_Q_rho_aux {m n : ℕ} (K : Mat m n) (ϱ0 : ℝ) (hϱ0 : 0 < ϱ0) :
    ContinuousAt (fun ϱ : ℝ => Q ϱ K) ϱ0 := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  set s : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hs_def
  have hspos : ∀ k : Fin K.rank, 0 < s k := fun k =>
    Muon.Foundations.singularValues_pos_of_lt_rank K k.isLt
  have hQ : ∀ ϱ : ℝ, 0 ≤ ϱ →
      Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (r k) :=
    fun ϱ hϱ => Q_eq_svd_aux ϱ hϱ K s p r hspos hp hr hK
  have hcoef : ∀ k : Fin K.rank,
      ContinuousAt (fun ϱ : ℝ => s k / Real.sqrt (s k ^ 2 + ϱ)) ϱ0 := by
    intro k
    have hcont : ContinuousAt (fun ϱ : ℝ => Real.sqrt (s k ^ 2 + ϱ)) ϱ0 :=
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt
    have hne : Real.sqrt (s k ^ 2 + ϱ0) ≠ 0 := by
      rw [Real.sqrt_ne_zero']
      have := pow_pos (hspos k) 2
      linarith
    exact ContinuousAt.div continuousAt_const hcont hne
  have hT : ContinuousAt (fun ϱ : ℝ => ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (r k)) ϱ0 :=
    tendsto_finsetSum _ fun k _ => (hcoef k).smul continuousAt_const
  refine hT.congr ?_
  filter_upwards [Ici_mem_nhds hϱ0] with ϱ hϱ
  exact (hQ ϱ hϱ).symm


/-- `lem:app-setup-filter`, part (iii). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.281–295:

    \begin{lemma}[Filter bounds and Lipschitz estimate]\label{lem:app-setup-filter}
    Let $K,L\in\R^{\Nout\times\Nin}$.
    \begin{enumerate}[label=(\roman*)]
    \item For $\ridge\ge0$: $\norm{\Qridge\ridge(K)}\le1$ and
    $\norm{\Qridge\ridge(K)}_\F^2\le\rank K\le\min(\Nout,\Nin)$, with equality
    $\norm{\Qridge0(K)}_\F^2=\rank K$.
    \item For $\ridge\ge0$, if $P\in\R^{\Nout\times\Nout}$ and $P'\in\R^{\Nin\times\Nin}$
    are orthogonal projections with $K=PKP'$, then $\Qridge\ridge(K)=P\Qridge\ridge(K)P'$.
    \item For $\ridge>0$,
    \begin{equation}\label{eqn:app-setup-lipschitz}
    \norm{\Qridge\ridge(K)-\Qridge\ridge(L)}_\F\le\ridge^{-1/2}\norm{K-L}_\F .
    \end{equation}
    \item $\Qridge\ridge(K)\to\Qridge0(K)$ as $\ridge\downarrow0$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_setup_filter_iii {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) (K L : Mat m n) :
    fro (Q ϱ K - Q ϱ L) ≤ ϱ ^ (-(1 / 2 : ℝ)) * fro (K - L) :=
  Muon.Foundations.fro_Q_sub_Q_le hϱ K L


/-- `lem:app-setup-filter`, part (iv). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.281–295:

    \begin{lemma}[Filter bounds and Lipschitz estimate]\label{lem:app-setup-filter}
    Let $K,L\in\R^{\Nout\times\Nin}$.
    \begin{enumerate}[label=(\roman*)]
    \item For $\ridge\ge0$: $\norm{\Qridge\ridge(K)}\le1$ and
    $\norm{\Qridge\ridge(K)}_\F^2\le\rank K\le\min(\Nout,\Nin)$, with equality
    $\norm{\Qridge0(K)}_\F^2=\rank K$.
    \item For $\ridge\ge0$, if $P\in\R^{\Nout\times\Nout}$ and $P'\in\R^{\Nin\times\Nin}$
    are orthogonal projections with $K=PKP'$, then $\Qridge\ridge(K)=P\Qridge\ridge(K)P'$.
    \item For $\ridge>0$,
    \begin{equation}\label{eqn:app-setup-lipschitz}
    \norm{\Qridge\ridge(K)-\Qridge\ridge(L)}_\F\le\ridge^{-1/2}\norm{K-L}_\F .
    \end{equation}
    \item $\Qridge\ridge(K)\to\Qridge0(K)$ as $\ridge\downarrow0$.
    \end{enumerate}
    \end{lemma}
-/
theorem lem_app_setup_filter_iv {m n : ℕ} (K : Mat m n) :
    Tendsto (fun ϱ : ℝ => Q ϱ K) (𝓝[>] 0) (𝓝 (Q 0 K)) := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  set s : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hs_def
  have hspos : ∀ k : Fin K.rank, 0 < s k := fun k =>
    Muon.Foundations.singularValues_pos_of_lt_rank K k.isLt
  have hQ : ∀ ϱ : ℝ, 0 ≤ ϱ →
      Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (r k) :=
    fun ϱ hϱ => Q_eq_svd_aux ϱ hϱ K s p r hspos hp hr hK
  have hQ0 : Q 0 K = ∑ k, outer (p k) (r k) := by
    rw [hQ 0 le_rfl]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h1 : s k / Real.sqrt (s k ^ 2 + 0) = 1 := by
      rw [add_zero, Real.sqrt_sq (hspos k).le, div_self (hspos k).ne']
    rw [h1, one_smul]
  have hcoef : ∀ k : Fin K.rank,
      Tendsto (fun ϱ : ℝ => s k / Real.sqrt (s k ^ 2 + ϱ)) (𝓝 0) (𝓝 1) := by
    intro k
    have hcont : ContinuousAt (fun ϱ : ℝ => Real.sqrt (s k ^ 2 + ϱ)) 0 :=
      (Real.continuous_sqrt.comp (continuous_const.add continuous_id)).continuousAt
    have hne : Real.sqrt (s k ^ 2 + 0) ≠ 0 := by
      rw [add_zero, Real.sqrt_ne_zero']
      exact pow_pos (hspos k) 2
    have hc : ContinuousAt (fun ϱ : ℝ => s k / Real.sqrt (s k ^ 2 + ϱ)) 0 :=
      ContinuousAt.div continuousAt_const hcont hne
    have h := hc.tendsto
    have hval : s k / Real.sqrt (s k ^ 2 + 0) = 1 := by
      rw [add_zero, Real.sqrt_sq (hspos k).le, div_self (hspos k).ne']
    rwa [hval] at h
  have hT : Tendsto (fun ϱ : ℝ => ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (r k))
      (𝓝 0) (𝓝 (∑ k, (1 : ℝ) • outer (p k) (r k))) :=
    tendsto_finset_sum _ fun k _ => (hcoef k).smul_const _
  rw [hQ0, show (∑ k, outer (p k) (r k)) = ∑ k, (1 : ℝ) • outer (p k) (r k) by
    simp only [one_smul]]
  refine Tendsto.congr' ?_ (hT.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with ϱ hϱ
  exact (hQ ϱ (Set.mem_Ioi.mp hϱ).le).symm



/-! ## Integral representation (`lem:app-setup-contour`) -/

private lemma integral_inv_b_add_sq_aux (b : ℝ) (hb : 0 < b) :
    ∫ u in Ioi (0 : ℝ), (b + u ^ 2)⁻¹ = Real.pi / (2 * Real.sqrt b) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have h : ∀ u : ℝ, (b + u ^ 2)⁻¹ = b⁻¹ * (1 + ((Real.sqrt b)⁻¹ * u) ^ 2)⁻¹ := by
    intro u
    rw [mul_pow, inv_pow, hsq]
    field_simp
  have hc := integral_comp_mul_left_Ioi (fun y : ℝ => (1 + y ^ 2)⁻¹) 0 (inv_pos.mpr hs)
  simp only [mul_zero, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul,
    inv_inv] at hc
  simp_rw [h]
  rw [integral_const_mul, hc]
  field_simp
  rw [hsq]

private lemma outer_mul_outer_aux {m n r : ℕ} (s : Fin r → ℝ) (p : Fin r → Vec m)
    (q : Fin r → Vec n) (k l : Fin r) :
    (s k • outer (p k) (q k)) * (s l • outer (q l) (p l))
      = (s k * s l * (q k ⬝ᵥ q l)) • outer (p k) (p l) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    smul_smul, smul_smul]

private lemma KKt_eq_aux {m n r : ℕ} (K : Mat m n) (s : Fin r → ℝ) (p : Fin r → Vec m)
    (q : Fin r → Vec n) (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    K * Kᵀ = ∑ k, (s k ^ 2) • outer (p k) (p k) := by
  rw [hK, Matrix.transpose_sum]
  simp only [Matrix.transpose_smul, Matrix.transpose_vecMulVec]
  rw [Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_sum]
  rw [Finset.sum_congr rfl fun l _ => outer_mul_outer_aux s p q k l]
  simp only [hq, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  rw [sq]

private lemma pd_aux {m n : ℕ} (K : Mat m n) (c : ℝ) (hc : 0 < c) :
    IsUnit (K * Kᵀ + c • (1 : Mat m m)) := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Kᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
    exact this
  rw [add_comm]
  exact ((Matrix.PosDef.one.smul hc).add_posSemidef h1).isUnit

private lemma outer_mul_outer_gen {m n : ℕ} (α β : ℝ) (u v w : Vec m) (x : Vec n) :
    (α • outer u v) * (β • outer w x) = (α * β * (v ⬝ᵥ w)) • outer u x := by
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    smul_smul, smul_smul]

private lemma inv_mul_K_aux {m n r : ℕ} (K : Mat m n) (c : ℝ) (hc : 0 < c) (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    (K * Kᵀ + c • (1 : Mat m m))⁻¹ * K = ∑ k, (s k / (s k ^ 2 + c)) • outer (p k) (q k) := by
  set X : Mat m n := ∑ k, (s k / (s k ^ 2 + c)) • outer (p k) (q k) with hX
  have hne : ∀ k, s k ^ 2 + c ≠ 0 := fun k => by
    have := sq_nonneg (s k); linarith
  have h1 : (∑ k, (s k ^ 2) • outer (p k) (p k)) * X
      = ∑ k, (s k ^ 2 * (s k / (s k ^ 2 + c))) • outer (p k) (q k) := by
    rw [hX, Matrix.sum_mul]
    simp only [Matrix.mul_sum, outer_mul_outer_gen, hp, mul_ite, mul_one, mul_zero, ite_smul,
      zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have h2 : (c • (1 : Mat m m)) * X = ∑ k, (c * (s k / (s k ^ 2 + c))) • outer (p k) (q k) := by
    rw [hX, Matrix.smul_mul, Matrix.one_mul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul]
  have hmul : (K * Kᵀ + c • (1 : Mat m m)) * X = K := by
    rw [KKt_eq_aux K s p q hq hK, Matrix.add_mul, h1, h2, ← Finset.sum_add_distrib, hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_smul]
    congr 1
    field_simp [hne k]
  have hU := (Matrix.isUnit_iff_isUnit_det _).mp (pd_aux K c hc)
  calc (K * Kᵀ + c • (1 : Mat m m))⁻¹ * K
      = (K * Kᵀ + c • (1 : Mat m m))⁻¹ * ((K * Kᵀ + c • (1 : Mat m m)) * X) := by rw [hmul]
    _ = X := by rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hU, Matrix.one_mul]


private lemma integrable_inv_b_aux (b : ℝ) (hb : 0 < b) :
    IntegrableOn (fun u : ℝ => (b + u ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsq : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have h : (fun u : ℝ => (b + u ^ 2)⁻¹)
      = fun u : ℝ => b⁻¹ * (fun y : ℝ => (1 + y ^ 2)⁻¹) ((Real.sqrt b)⁻¹ * u) := by
    funext u
    simp only
    rw [mul_pow, inv_pow, hsq]
    field_simp
  rw [h]
  exact ((integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hs.ne')).const_mul _).integrableOn

private lemma integrable_term_aux (s ϱ : ℝ) (hϱ : 0 < ϱ) :
    IntegrableOn (fun u : ℝ => s / (s ^ 2 + (ϱ + u ^ 2))) (Ioi (0 : ℝ)) := by
  have hb : 0 < s ^ 2 + ϱ := by positivity
  have h : (fun u : ℝ => s / (s ^ 2 + (ϱ + u ^ 2))) = fun u : ℝ => s * (s ^ 2 + ϱ + u ^ 2)⁻¹ := by
    funext u
    rw [← add_assoc, div_eq_mul_inv]
  rw [h]
  exact (integrable_inv_b_aux _ hb).const_mul s

private lemma integral_term_aux (s ϱ : ℝ) (hϱ : 0 < ϱ) :
    ∫ u in Ioi (0 : ℝ), s / (s ^ 2 + (ϱ + u ^ 2))
      = s * (Real.pi / (2 * Real.sqrt (s ^ 2 + ϱ))) := by
  have hb : 0 < s ^ 2 + ϱ := by positivity
  have h : ∀ u : ℝ, s / (s ^ 2 + (ϱ + u ^ 2)) = s * (s ^ 2 + ϱ + u ^ 2)⁻¹ := by
    intro u
    rw [← add_assoc, div_eq_mul_inv]
  simp_rw [h]
  rw [integral_const_mul, integral_inv_b_add_sq_aux _ hb]

private lemma nuc_outer_unit_aux {m n : ℕ} (x : Vec m) (y : Vec n) (hx : x ⬝ᵥ x = 1)
    (hy : y ⬝ᵥ y = 1) : nuc (outer x y) = 1 := by
  have h1 : ∑ i, x i ^ 2 = 1 := by simpa [dotProduct, sq] using hx
  have h2 : ∑ j, y j ^ 2 = 1 := by simpa [dotProduct, sq] using hy
  rw [nuc_outer, h1, h2, Real.sqrt_one, one_mul]

private lemma nuc_finset_sum_le_aux {m n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat m n) :
    nuc (∑ k ∈ s, f k) ≤ ∑ k ∈ s, nuc (f k) := by
  classical
  have h0 : nuc (0 : Mat m n) = 0 := by simpa using nuc_smul (0 : ℝ) (0 : Mat m n)
  induction s using Finset.induction_on with
  | empty => simp [h0]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (nuc_add_le _ _).trans (by linarith)

private lemma trace_outer_mul_outer_aux {m n : ℕ} (p p' : Vec m) (q q' : Vec n) :
    (outer q p * outer p' q').trace = (p ⬝ᵥ p') * (q ⬝ᵥ q') := by
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul,
    Matrix.trace_smul, Matrix.trace_vecMulVec, smul_eq_mul]

private lemma nuc_sum_outer_eq_aux {m n r : ℕ} (a : Fin r → ℝ) (ha : ∀ k, 0 ≤ a k)
    (p : Fin r → Vec m) (q : Fin r → Vec n)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0) :
    nuc (∑ k, a k • outer (p k) (q k)) = ∑ k, a k := by
  apply le_antisymm
  · refine (nuc_finset_sum_le_aux _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [nuc_smul, nuc_outer_unit_aux _ _ (by simpa using hp k k) (by simpa using hq k k),
      abs_of_nonneg (ha k), mul_one]
  · have hU : opNorm (∑ k, (fun _ : Fin r => (1 : ℝ)) k • outer (p k) (q k)) ≤ 1 :=
      svd_opNorm_le_aux _ (fun _ => by norm_num) p q hp hq
    simp only [one_smul] at hU
    refine (nuc_isGreatest_dual _).2 ⟨∑ k, outer (p k) (q k), hU, ?_⟩
    simp [Matrix.transpose_sum, Matrix.sum_mul, Matrix.mul_sum, Matrix.mul_smul,
      Matrix.trace_sum, Matrix.trace_smul, Matrix.transpose_vecMulVec,
      trace_outer_mul_outer_aux, hp, hq, Finset.sum_ite_eq]

/-- `lem:app-setup-contour`. Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.352–358:

    \begin{lemma}[Integral representation]\label{lem:app-setup-contour}
    For every $K\in\R^{\Nout\times\Nin}$ and $\ridge>0$,
    \begin{equation}\label{eqn:app-setup-contour}
    \Qridge{\ridge}(K)=\frac2\pi\int_0^\infty\big(KK^\T+(\ridge+u^2)\Id_{\Nout}\big)^{-1}K\,du ,
    \end{equation}
    and $\int_0^\infty\norm{(KK^\T+(\ridge+u^2)\Id)^{-1}K}_*\,du\le\tfrac\pi2\min(\Nout,\Nin)$.
    \end{lemma}
-/
theorem lem_app_setup_contour {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) (K : Mat m n) :
    (∀ i j, Q ϱ K i j = (2 / Real.pi) *
        ∫ u in Ioi (0 : ℝ), ((K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K) i j) ∧
    (∀ i j, IntegrableOn
        (fun u : ℝ => ((K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K) i j) (Ioi (0 : ℝ))) ∧
    IntegrableOn (fun u : ℝ => nuc ((K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K))
      (Ioi (0 : ℝ)) ∧
    ∫ u in Ioi (0 : ℝ), nuc ((K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K) ≤
      Real.pi / 2 * (min m n : ℝ) := by
  obtain ⟨p, r, hp, hr, hK⟩ := Muon.Foundations.svd_rect_exists K
  set s : Fin K.rank → ℝ := fun k => (Matrix.toEuclideanLin K).singularValues (k : ℕ) with hsdef
  have hpos : ∀ k, 0 < s k := fun k => Muon.Foundations.singularValues_pos_of_lt_rank K k.2
  have hrank : K.rank ≤ min m n := le_min (Matrix.rank_le_height K) (Matrix.rank_le_width K)
  have hQ : Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (r k) :=
    Q_eq_svd_aux ϱ hϱ.le K s p r hpos hp hr hK
  have hM : ∀ u : ℝ, (K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K
      = ∑ k, (s k / (s k ^ 2 + (ϱ + u ^ 2))) • outer (p k) (r k) :=
    fun u => inv_mul_K_aux K (ϱ + u ^ 2) (by positivity) s p r hp hr hK
  have hint : ∀ k, IntegrableOn (fun u : ℝ => s k / (s k ^ 2 + (ϱ + u ^ 2))) (Ioi (0 : ℝ)) :=
    fun k => integrable_term_aux (s k) ϱ hϱ
  have hnn : ∀ k (u : ℝ), 0 ≤ s k / (s k ^ 2 + (ϱ + u ^ 2)) := fun k u =>
    div_nonneg (hpos k).le (by positivity)
  have hnucM : ∀ u : ℝ, nuc ((K * Kᵀ + (ϱ + u ^ 2) • (1 : Mat m m))⁻¹ * K)
      = ∑ k, s k / (s k ^ 2 + (ϱ + u ^ 2)) := fun u => by
    rw [hM u]
    exact nuc_sum_outer_eq_aux _ (fun k => hnn k u) p r hp hr
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hQ]
    simp only [hM, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun k _ => Integrable.mul_const (hint k) _)]
    simp only [integral_mul_const, integral_term_aux _ _ hϱ]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp [Real.pi_pos.ne']
  · intro i j
    simp only [hM, Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact integrable_finsetSum _ fun k _ => Integrable.mul_const (hint k) _
  · simp only [hnucM]
    exact integrable_finsetSum _ fun k _ => hint k
  · simp only [hnucM]
    rw [integral_finsetSum _ (fun k _ => hint k)]
    simp only [integral_term_aux _ _ hϱ]
    have hterm : ∀ k, s k * (Real.pi / (2 * Real.sqrt (s k ^ 2 + ϱ))) ≤ Real.pi / 2 := by
      intro k
      have hq0 : 0 < Real.sqrt (s k ^ 2 + ϱ) := Real.sqrt_pos.mpr (by positivity)
      have hle : s k ≤ Real.sqrt (s k ^ 2 + ϱ) :=
        calc s k = Real.sqrt (s k ^ 2) := (Real.sqrt_sq (hpos k).le).symm
          _ ≤ Real.sqrt (s k ^ 2 + ϱ) := Real.sqrt_le_sqrt (by linarith)
      have hratio : s k / Real.sqrt (s k ^ 2 + ϱ) ≤ 1 := (div_le_one hq0).mpr hle
      calc s k * (Real.pi / (2 * Real.sqrt (s k ^ 2 + ϱ)))
          = (Real.pi / 2) * (s k / Real.sqrt (s k ^ 2 + ϱ)) := by
            field_simp
        _ ≤ (Real.pi / 2) * 1 := mul_le_mul_of_nonneg_left hratio (by positivity)
        _ = Real.pi / 2 := mul_one _
    calc ∑ k, s k * (Real.pi / (2 * Real.sqrt (s k ^ 2 + ϱ)))
        ≤ ∑ _k : Fin K.rank, Real.pi / 2 := Finset.sum_le_sum fun k _ => hterm k
      _ = (K.rank : ℝ) * (Real.pi / 2) := by simp
      _ ≤ (min m n : ℝ) * (Real.pi / 2) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hrank) (by positivity)
      _ = Real.pi / 2 * (min m n : ℝ) := mul_comm _ _

/-! ## Scaling, physical ridge and heavy ball (`prop:app-setup-scaling`) -/

private lemma rpow_scale_aux (a y : ℝ) (ha : 0 < a) (hy : 0 ≤ y) :
    (a ^ 2 * y) ^ (-(1 / 2 : ℝ)) = a⁻¹ * y ^ (-(1 / 2 : ℝ)) := by
  rw [Real.mul_rpow (by positivity) hy]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
  norm_num [Real.rpow_neg_one]

private lemma cfc_scale_aux {n : ℕ} (ϱ a : ℝ) (ha : 0 < a) (hϱ : 0 ≤ ϱ) (A : Mat n n)
    (hsa : IsSelfAdjoint A) (hsp : ∀ x ∈ spectrum ℝ A, 0 ≤ x) :
    cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) ((a ^ 2) • A)
      = a⁻¹ • cfc (fun x : ℝ => (x + ϱ / a ^ 2) ^ (-(1 / 2 : ℝ))) A := by
  have ha0 : a ≠ 0 := ha.ne'
  have hfin : (spectrum ℝ A).Finite := Matrix.finite_real_spectrum
  have hcont : ∀ g : ℝ → ℝ, ContinuousOn g (spectrum ℝ A) := fun g => hfin.continuousOn g
  have h1 : cfc (fun x : ℝ => a⁻¹ * (x + ϱ / a ^ 2) ^ (-(1 / 2 : ℝ))) A
      = a⁻¹ • cfc (fun x : ℝ => (x + ϱ / a ^ 2) ^ (-(1 / 2 : ℝ))) A :=
    cfc_const_mul _ _ _ (hcont _)
  have h2 : cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) ((a ^ 2) • A)
      = cfc (fun x : ℝ => a⁻¹ * (x + ϱ / a ^ 2) ^ (-(1 / 2 : ℝ))) A := by
    rw [← cfc_comp_const_mul (a ^ 2) (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) A
      ((hfin.image (fun x : ℝ => a ^ 2 * x)).continuousOn _) hsa]
    refine cfc_congr fun x hx => ?_
    have hx0 := hsp x hx
    have hy : (0 : ℝ) ≤ x + ϱ / a ^ 2 := by
      have := div_nonneg hϱ (sq_nonneg a)
      linarith
    have he : a ^ 2 * x + ϱ = a ^ 2 * (x + ϱ / a ^ 2) := by
      field_simp
    change (a ^ 2 * x + ϱ) ^ (-(1 / 2 : ℝ)) = a⁻¹ * (x + ϱ / a ^ 2) ^ (-(1 / 2 : ℝ))
    rw [he, rpow_scale_aux a _ ha hy]
  exact h2.trans h1



/-- `prop:app-setup-scaling`, part (i). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.378–389:

    \begin{proposition}[Scaling, physical ridge and heavy ball]\label{prop:app-setup-scaling}
    Let $K\in\R^{\Nout\times\Nin}$, $\ridge\ge0$ and $a>0$.
    \begin{enumerate}[label=(\roman*)]
    \item $\Qridge{\ridge}(aK)=\Qridge{\ridge/a^2}(K)$.
    \item If $\cR>0$ and $\ridgephys\defeq2\cR\,\ridge$, then
    $\Qridge{\ridgephys}\big(\sqrt{2\cR}\,K\big)=\Qridge{\ridge}(K)$.
    \item Let $(G_{t+1})_{t\ge0}$ be any sequence of matrices, $\bmom\in[0,1)$, and
    let $M_t=\bmom M_{t-1}+(1-\bmom)G_{t+1}$ and $H_t=\bmom H_{t-1}+G_{t+1}$ for
    $t\ge0$ with $H_{-1}=M_{-1}/(1-\bmom)$. Then $H_t=M_t/(1-\bmom)$ for all
    $t\ge-1$, and $\Qridge{\ridge}(H_t)=\Qridge{(1-\bmom)^2\ridge}(M_t)$.
    \end{enumerate}
    \end{proposition}
-/
theorem prop_app_setup_scaling_i {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) (a : ℝ)
    (ha : 0 < a) :
    Q ϱ (a • K) = Q (ϱ / a ^ 2) K := by
  have hsa : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hA0 : 0 ≤ Kᵀ * K := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hsp : ∀ x ∈ spectrum ℝ (Kᵀ * K), 0 ≤ x := fun x hx => spectrum_nonneg_of_nonneg hA0 hx
  have hsmul : (a • K)ᵀ * (a • K) = (a ^ 2) • (Kᵀ * K) := by
    rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sq]
  unfold Q
  rw [hsmul, cfc_scale_aux ϱ a ha hϱ (Kᵀ * K) hsa hsp, Matrix.mul_smul, Matrix.smul_mul,
    smul_smul, inv_mul_cancel₀ ha.ne', one_smul]


/-- `prop:app-setup-scaling`, part (ii). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.378–389:

    \begin{proposition}[Scaling, physical ridge and heavy ball]\label{prop:app-setup-scaling}
    Let $K\in\R^{\Nout\times\Nin}$, $\ridge\ge0$ and $a>0$.
    \begin{enumerate}[label=(\roman*)]
    \item $\Qridge{\ridge}(aK)=\Qridge{\ridge/a^2}(K)$.
    \item If $\cR>0$ and $\ridgephys\defeq2\cR\,\ridge$, then
    $\Qridge{\ridgephys}\big(\sqrt{2\cR}\,K\big)=\Qridge{\ridge}(K)$.
    \item Let $(G_{t+1})_{t\ge0}$ be any sequence of matrices, $\bmom\in[0,1)$, and
    let $M_t=\bmom M_{t-1}+(1-\bmom)G_{t+1}$ and $H_t=\bmom H_{t-1}+G_{t+1}$ for
    $t\ge0$ with $H_{-1}=M_{-1}/(1-\bmom)$. Then $H_t=M_t/(1-\bmom)$ for all
    $t\ge-1$, and $\Qridge{\ridge}(H_t)=\Qridge{(1-\bmom)^2\ridge}(M_t)$.
    \end{enumerate}
    \end{proposition}
-/
theorem prop_app_setup_scaling_ii {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) (R : ℝ)
    (hR : 0 < R) :
    Q (2 * R * ϱ) (Real.sqrt (2 * R) • K) = Q ϱ K := by
  have hR0 : R ≠ 0 := hR.ne'
  have ha : 0 < Real.sqrt (2 * R) := Real.sqrt_pos.mpr (by linarith)
  have h2 : Real.sqrt (2 * R) ^ 2 = 2 * R := Real.sq_sqrt (by linarith)
  have hϱ' : 0 ≤ 2 * R * ϱ := mul_nonneg (by linarith) hϱ
  rw [prop_app_setup_scaling_i (2 * R * ϱ) hϱ' K _ ha, h2]
  congr 1
  field_simp


/-- `prop:app-setup-scaling`, part (iii). Snapshot `cr-2026-10-23`. Statement, verbatim from `section.tex` l.378–389:

    \begin{proposition}[Scaling, physical ridge and heavy ball]\label{prop:app-setup-scaling}
    Let $K\in\R^{\Nout\times\Nin}$, $\ridge\ge0$ and $a>0$.
    \begin{enumerate}[label=(\roman*)]
    \item $\Qridge{\ridge}(aK)=\Qridge{\ridge/a^2}(K)$.
    \item If $\cR>0$ and $\ridgephys\defeq2\cR\,\ridge$, then
    $\Qridge{\ridgephys}\big(\sqrt{2\cR}\,K\big)=\Qridge{\ridge}(K)$.
    \item Let $(G_{t+1})_{t\ge0}$ be any sequence of matrices, $\bmom\in[0,1)$, and
    let $M_t=\bmom M_{t-1}+(1-\bmom)G_{t+1}$ and $H_t=\bmom H_{t-1}+G_{t+1}$ for
    $t\ge0$ with $H_{-1}=M_{-1}/(1-\bmom)$. Then $H_t=M_t/(1-\bmom)$ for all
    $t\ge-1$, and $\Qridge{\ridge}(H_t)=\Qridge{(1-\bmom)^2\ridge}(M_t)$.
    \end{enumerate}
    \end{proposition}
-/
theorem prop_app_setup_scaling_iii {m n : ℕ} (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ϱ : ℝ)
    (hϱ : 0 ≤ ϱ) (G : ℕ → Mat m n) (M H : ℕ → Mat m n)
    (hM : ∀ t, M (t + 1) = β • M t + (1 - β) • G t)
    (hH0 : H 0 = (1 - β)⁻¹ • M 0)
    (hH : ∀ t, H (t + 1) = β • H t + G t) :
    (∀ t, H t = (1 - β)⁻¹ • M t) ∧
      ∀ t, Q ϱ (H t) = Q ((1 - β) ^ 2 * ϱ) (M t) := by
  have hc0 : (1 - β) ≠ 0 := (sub_pos.mpr hβ1).ne'
  have hcinv : (1 - β)⁻¹ * (1 - β) = 1 := inv_mul_cancel₀ hc0
  have hHM : ∀ t, H t = (1 - β)⁻¹ • M t := by
    intro t
    induction t with
    | zero => exact hH0
    | succ t ih =>
      rw [hH, ih, hM]
      simp only [smul_add, smul_smul]
      rw [mul_comm β, hcinv, one_smul]
  refine ⟨hHM, fun t => ?_⟩
  have hinv : (0 : ℝ) < (1 - β)⁻¹ := inv_pos.mpr (sub_pos.mpr hβ1)
  rw [hHM t, prop_app_setup_scaling_i ϱ hϱ (M t) _ hinv]
  congr 1
  rw [inv_pow, div_inv_eq_mul, mul_comm ϱ]

/-! ## Helpers: SVD form, measurability, continuity -/

/-- Helper (not a label): the SVD form of `Q_ϱ` (`eqn:app-setup-Q`, first display, l.262–266),
for any decomposition `K = ∑ₖ sₖ pₖ ⊗ rₖ` with `sₖ > 0` and orthonormal families `(pₖ)`, `(rₖ)`. -/
theorem Q_eq_svd {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) {r : ℕ} (s : Fin r → ℝ)
    (p : Fin r → Vec m) (q : Fin r → Vec n) (hs : ∀ k, 0 < s k)
    (hp : ∀ k l, p k ⬝ᵥ p l = if k = l then 1 else 0)
    (hq : ∀ k l, q k ⬝ᵥ q l = if k = l then 1 else 0)
    (hK : K = ∑ k, s k • outer (p k) (q k)) :
    Q ϱ K = ∑ k, (s k / Real.sqrt (s k ^ 2 + ϱ)) • outer (p k) (q k) := by
  exact Q_eq_svd_aux ϱ hϱ K s p q hs hp hq hK

private lemma continuousOn_Q_pos_aux {m n : ℕ} :
    ContinuousOn (fun p : ℝ × Mat m n => Q p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) := by
  rintro ⟨ϱ0, K0⟩ ⟨hϱ0, -⟩
  have hϱ0' : (0 : ℝ) < ϱ0 := hϱ0
  refine ContinuousAt.continuousWithinAt ?_
  show Tendsto (fun p : ℝ × Mat m n => Q p.1 p.2) (𝓝 (ϱ0, K0)) (𝓝 (Q ϱ0 K0))
  set Q0 := Q ϱ0 K0 with hQ0
  have hfst : Tendsto (fun p : ℝ × Mat m n => p.1) (𝓝 (ϱ0, K0)) (𝓝 ϱ0) :=
    (continuous_fst.tendsto (ϱ0, K0))
  have hsnd : Tendsto (fun p : ℝ × Mat m n => p.2) (𝓝 (ϱ0, K0)) (𝓝 K0) :=
    (continuous_snd.tendsto (ϱ0, K0))
  have hpos : ∀ᶠ p : ℝ × Mat m n in 𝓝 (ϱ0, K0), 0 < p.1 :=
    hfst.eventually (Ioi_mem_nhds hϱ0')
  -- term 1
  have h1 : Tendsto (fun p : ℝ × Mat m n => p.1 ^ (-(1 / 2 : ℝ)) * fro (p.2 - K0))
      (𝓝 (ϱ0, K0)) (𝓝 0) := by
    have ha : Tendsto (fun p : ℝ × Mat m n => p.1 ^ (-(1 / 2 : ℝ))) (𝓝 (ϱ0, K0))
        (𝓝 (ϱ0 ^ (-(1 / 2 : ℝ)))) :=
      ((Real.continuousAt_rpow_const _ _ (Or.inl hϱ0'.ne')).tendsto).comp hfst
    have hb : Tendsto (fun p : ℝ × Mat m n => fro (p.2 - K0)) (𝓝 (ϱ0, K0)) (𝓝 0) := by
      have := ((continuous_fro_sub_aux K0).continuousAt (x := K0)).tendsto.comp hsnd
      have h0 : fro (K0 - K0) = 0 := by simp [fro]
      rw [h0] at this
      exact this
    simpa using ha.mul hb
  -- term 2
  have h2 : Tendsto (fun p : ℝ × Mat m n => fro (Q p.1 K0 - Q0)) (𝓝 (ϱ0, K0)) (𝓝 0) := by
    have hc := (continuousAt_Q_rho_aux K0 ϱ0 hϱ0').tendsto
    have := ((continuous_fro_sub_aux Q0).continuousAt (x := Q ϱ0 K0)).tendsto.comp (hc.comp hfst)
    have h0 : fro (Q ϱ0 K0 - Q0) = 0 := by simp [fro, hQ0]
    rw [h0] at this
    exact this
  have hg : Tendsto (fun p : ℝ × Mat m n => fro (Q p.1 p.2 - Q0)) (𝓝 (ϱ0, K0)) (𝓝 0) := by
    have h12 := h1.add h2
    rw [add_zero] at h12
    refine squeeze_zero' ?_ ?_ h12
    · exact Eventually.of_forall fun p => Real.sqrt_nonneg _
    · filter_upwards [hpos] with p hp
      exact (fro_sub_le_aux _ (Q p.1 K0) _).trans
        (add_le_add (lem_app_setup_filter_iii p.1 hp p.2 K0) le_rfl)
  change Tendsto (fun p : ℝ × Mat m n => (Q p.1 p.2 : Fin m → Fin n → ℝ)) (𝓝 (ϱ0, K0))
    (𝓝 (Q0 : Fin m → Fin n → ℝ))
  refine tendsto_pi_nhds.2 fun i => ?_
  refine tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun p => dist_nonneg) (fun p => ?_) hg
  rw [Real.dist_eq]
  exact abs_entry_le_fro_aux (Q p.1 p.2 - Q0) i j

/-- Helper (not a label): `(ϱ, K) ↦ Q_ϱ(K)` is Borel on `[0, ∞) × Mat m n`. Needed by the
update measurability in `cor:app-setup-augmented` (`Q` is Borel; stated nowhere in the paper). -/
theorem measurable_Q {m n : ℕ} :
    Measurable (fun p : Ici (0 : ℝ) × Mat m n => Q (p.1 : ℝ) p.2) := by
  set F : ℕ → Ici (0 : ℝ) × Mat m n → Mat m n :=
    fun k p => Q (max (p.1 : ℝ) (1 / ((k : ℝ) + 1))) p.2 with hF
  have hFc : ∀ k, Continuous (F k) := by
    intro k
    have hk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hg : Continuous fun p : Ici (0 : ℝ) × Mat m n =>
        ((max (p.1 : ℝ) (1 / ((k : ℝ) + 1)), p.2) : ℝ × Mat m n) :=
      ((continuous_subtype_val.comp continuous_fst).max continuous_const).prodMk continuous_snd
    refine (continuousOn_Q_pos_aux (m := m) (n := n)).comp_continuous hg fun p => ?_
    exact ⟨lt_of_lt_of_le hk (le_max_right _ _), Set.mem_univ _⟩
  haveI : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  refine measurable_of_tendsto_metrizable (f := F) (fun k => (hFc k).measurable) ?_
  rw [tendsto_pi_nhds]
  intro p
  have hp0 : (0 : ℝ) ≤ p.1 := p.1.2
  rcases hp0.eq_or_lt with h0 | hpos
  · have hlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Eventually.of_forall fun k => by
        show (0 : ℝ) < 1 / ((k : ℝ) + 1)
        positivity
    have h4 := (lem_app_setup_filter_iv p.2).comp hlim
    have hp1 : ((p.1 : ℝ)) = 0 := h0.symm
    simp only [hF, hp1]
    refine Tendsto.congr (fun k => ?_) h4
    simp only [Function.comp]
    rw [max_eq_right (by positivity : (0 : ℝ) ≤ 1 / ((k : ℝ) + 1))]
  · have hev : ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 1) < (p.1 : ℝ) :=
      (tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hpos))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    simp only [hF]
    rw [max_eq_left hk.le]

/-- Helper (not a label): `(ϱ, K) ↦ Q_ϱ(K)` is jointly continuous on `(0, ∞) × Mat m n`
(`Q_0` is discontinuous in `K`, so the continuity domain is `ϱ > 0`). -/
theorem continuousOn_Q_pos {m n : ℕ} :
    ContinuousOn (fun p : ℝ × Mat m n => Q p.1 p.2) (Ioi (0 : ℝ) ×ˢ univ) :=
  continuousOn_Q_pos_aux

end Muon.Setup

end
