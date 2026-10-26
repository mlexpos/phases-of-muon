import Muon.Setup.Model
import Muon.Foundations.UniformIntegrability

/-!
# Appendix A: residual law (`lem:app-setup-residual`)

Work package L-A.9 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/01-setup/section.tex` l.930–943.

Independent of the frozen model: the statements concern only the bilinear residual
`d = zᵀ A w` of independent standard Gaussian vectors `z`, `w`. Shared objects are reused:
`Muon.Setup.resid` (`Muon/Setup/Model.lean`), `Muon.fro`, `Muon.opNorm`,
`Muon.Foundations.stdGaussianPi`. Singular values are Mathlib's `LinearMap.singularValues`
(0-indexed). The paper's `α_k` over all `k` is the sum over `Finset.range (min m n)`, since
the remaining singular values vanish. Every theorem has proof `sorry`.
-/

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Muon.Setup

open Muon

/-- Joint law `N(0, I_m) ⊗ N(0, I_n)` of a pair `(z, w)` of independent standard Gaussian
vectors (the `z ∼ N(0, Id_{N_out})`, `w ∼ N(0, Id_{N_in})` of `lem:app-setup-residual`). -/
def gaussPair (m n : ℕ) : Measure (Vec m × Vec n) :=
  (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)

instance (m n : ℕ) : IsProbabilityMeasure (gaussPair m n) := by
  unfold gaussPair
  infer_instance

/-- `α_k`: the `k`-th singular value of a real matrix, 0-indexed, from Mathlib's
`LinearMap.singularValues` (`α_1 ≥ α_2 ≥ ⋯` in the paper's 1-indexing). -/
def svals {m n : ℕ} (A : Mat m n) (k : ℕ) : ℝ :=
  (Matrix.toEuclideanLin A).singularValues k

/-- `∏_k (1 + θ² α_k²)^{-1/2}`, the real product of `lem:app-setup-residual`(ii). -/
def residCharProd {m n : ℕ} (A : Mat m n) (θ : ℝ) : ℝ :=
  ∏ k ∈ Finset.range (min m n), (1 + θ ^ 2 * svals A k ^ 2) ^ (-(1 / 2 : ℝ))

/-! ### Private helpers for `lem_app_setup_residual_i` (task P-A.9.P1) -/

private theorem stdG_map_neg (n : ℕ) :
    (Muon.Foundations.stdGaussianPi n).map (fun z : Vec n => -z)
      = Muon.Foundations.stdGaussianPi n := by
  unfold Muon.Foundations.stdGaussianPi
  have h := Measure.pi_map_pi (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun _ => fun x : ℝ => -x) (fun _ => measurable_neg.aemeasurable)
  have e : (fun z : Vec n => -z) = fun z i => (fun x : ℝ => -x) (z i) := rfl
  rw [e, h]
  congr 1
  funext i
  rw [gaussianReal_map_neg]; simp

private theorem lin_law {m : ℕ} (v : Vec m) :
    (Muon.Foundations.stdGaussianPi m).map (fun z : Vec m => dotProduct z v)
      = (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt (dotProduct v v) * x) := by
  have h := Muon.Foundations.stdGaussianPi_linear_map m v
  have e : (fun z : Vec m => dotProduct z v) = fun z => ∑ i, z i * v i := rfl
  rw [e, h, gaussianReal_map_const_mul]
  have hv : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : dotProduct v v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
  congr 1
  · simp
  · apply NNReal.eq
    simp only [NNReal.coe_mk, Real.coe_toNNReal _ hv, mul_one]
    rw [hd, Real.sq_sqrt hv]


private theorem cond_moment {m : ℕ} (v : Vec m) (p : ℕ) :
    Integrable (fun z : Vec m => (dotProduct z v) ^ (2 * p)) (Muon.Foundations.stdGaussianPi m) ∧
    ∫ z, (dotProduct z v) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi m)
      = ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) * (dotProduct v v) ^ p := by
  have hm : Measurable (fun z : Vec m => dotProduct z v) := by
    unfold dotProduct; fun_prop
  have hmc : Measurable (fun x : ℝ => Real.sqrt (dotProduct v v) * x) := by fun_prop
  set c := Real.sqrt (dotProduct v v) with hc
  have hc2 : c ^ 2 = dotProduct v v := Real.sq_sqrt (by
    have : dotProduct v v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
    rw [this]; exact Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hL := lin_law v
  constructor
  · have h1 : Integrable (fun x : ℝ => x ^ (2 * p)) ((gaussianReal 0 1).map (fun x : ℝ => c * x)) := by
      rw [integrable_map_measure (by fun_prop) hmc.aemeasurable]
      have := (Muon.Foundations.gaussian_integrable_pow (2 * p)).const_mul (c ^ (2 * p))
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp [mul_pow]
    rw [← hL, integrable_map_measure (by fun_prop) hm.aemeasurable] at h1
    exact h1
  · have h1 : ∫ x, x ^ (2 * p) ∂((gaussianReal 0 1).map (fun x : ℝ => c * x))
        = ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) * (dotProduct v v) ^ p := by
      rw [integral_map hmc.aemeasurable (by fun_prop)]
      simp_rw [mul_pow]
      rw [integral_const_mul, Muon.Foundations.gaussian_moment_even, ← hc2, ← pow_mul, mul_comm]
    rw [← hL, integral_map hm.aemeasurable (by fun_prop)] at h1
    exact h1


private theorem res_toEuclideanLin_coe {m n : ℕ} (A : Mat m n) (x : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toEuclideanLin A x : Fin m → ℝ) = A *ᵥ (x : Fin n → ℝ) := by
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply]

private theorem res_adjoint_coe {m n : ℕ} (A : Mat m n) (x : EuclideanSpace ℝ (Fin m)) :
    ((Matrix.toEuclideanLin A).adjoint x : Fin n → ℝ) = Aᴴ *ᵥ (x : Fin m → ℝ) := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, res_toEuclideanLin_coe]

private theorem res_dot_K_K {m n : ℕ} (K : Mat m n) (u v : Fin n → ℝ) :
    (K *ᵥ u) ⬝ᵥ (K *ᵥ v) = u ⬝ᵥ ((Kᴴ * K) *ᵥ v) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.vecMul_transpose]

private theorem spectral {m n : ℕ} (A : Mat m n) :
    ∃ (μ : Fin n → ℝ) (u : Fin n → Vec n),
      (∀ j, μ j = svals A (j : ℕ) ^ 2) ∧
      (∀ j l, dotProduct (u j) (u l) = if j = l then 1 else 0) ∧
      (∀ i k, ∑ j, u j i * u j k = if i = k then 1 else 0) ∧
      (∀ j, (Aᵀ * A) *ᵥ u j = μ j • u j) := by
  classical
  let T := Matrix.toEuclideanLin A
  have hn : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n := finrank_euclideanSpace_fin
  have hS := LinearMap.isSymmetric_adjoint_comp_self T
  let w := hS.eigenvectorBasis hn
  let μ := hS.eigenvalues hn
  have hsq : ∀ j : Fin n, μ j = T.singularValues j ^ 2 := fun j =>
    (T.sq_singularValues_fin hn j).symm
  have hev : ∀ j : Fin n, (T.adjoint ∘ₗ T) (w j) = μ j • w j := fun j =>
    hS.apply_eigenvectorBasis hn j
  have hAv : ∀ j : Fin n, (Aᴴ * A) *ᵥ (w j : Fin n → ℝ) = μ j • (w j : Fin n → ℝ) := by
    intro j
    have h2 := congrArg (fun x : EuclideanSpace ℝ (Fin n) => (x : Fin n → ℝ)) (hev j)
    simp only [LinearMap.comp_apply] at h2
    rw [res_adjoint_coe, res_toEuclideanLin_coe, Matrix.mulVec_mulVec] at h2
    simpa using h2
  have horth : ∀ j l : Fin n, (w j : Fin n → ℝ) ⬝ᵥ (w l : Fin n → ℝ) = if j = l then 1 else 0 := by
    intro j l
    have h := (orthonormal_iff_ite.mp w.orthonormal) j l
    rw [EuclideanSpace.inner_eq_star_dotProduct] at h
    rw [dotProduct_comm, ← h]
    simp only [dotProduct, star_trivial]
  have hcomp : ∀ i k : Fin n, ∑ j, (w j : Fin n → ℝ) i * (w j : Fin n → ℝ) k
      = if i = k then 1 else 0 := by
    intro i k
    have hU := (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_unitary w
    rw [Matrix.mem_unitaryGroup_iff] at hU
    have h := congrFun (congrFun hU i) k
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, star_trivial, Matrix.one_apply] at h
    simpa [Module.Basis.toMatrix_apply, OrthonormalBasis.coe_toBasis_repr_apply,
      EuclideanSpace.basisFun_repr] using h
  refine ⟨μ, fun j => (w j : Fin n → ℝ), hsq, horth, hcomp, ?_⟩
  intro j
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hAv j


private theorem spec_entry {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) (u : Fin n → Vec n)
    (hc : ∀ i k, ∑ j, u j i * u j k = if i = k then 1 else 0)
    (hM : ∀ j, M *ᵥ u j = μ j • u j) (i k : Fin n) :
    M i k = ∑ j, μ j * (u j i * u j k) := by
  have h1 : M i k = ∑ l, M i l * (if l = k then 1 else 0) := by
    simp
  have h2 : ∀ l, (if l = k then (1 : ℝ) else 0) = ∑ j, u j l * u j k := by
    intro l; rw [hc l k]
  have h3 : ∀ j, (M *ᵥ u j) i = μ j * u j i := fun j => by rw [hM j]; simp
  calc M i k = ∑ l, M i l * ∑ j, u j l * u j k := by
        rw [h1]; exact Finset.sum_congr rfl fun l _ => by rw [h2]
    _ = ∑ j, (∑ l, M i l * u j l) * u j k := by
        simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ j, μ j * (u j i * u j k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have := h3 j
        simp only [Matrix.mulVec, dotProduct] at this
        rw [this]; ring

private theorem spec_quad {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) (u : Fin n → Vec n)
    (hE : ∀ i k, M i k = ∑ j, μ j * (u j i * u j k)) (w : Vec n) :
    ∑ i, ∑ k, w i * M i k * w k = ∑ j, μ j * (dotProduct w (u j)) ^ 2 := by
  have e1 : ∀ i k, w i * M i k * w k = ∑ j, μ j * ((u j i * w i) * (u j k * w k)) := by
    intro i k
    rw [hE, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e1]
  have e2 : ∀ i, ∑ k, ∑ j, μ j * ((u j i * w i) * (u j k * w k))
      = ∑ j, ∑ k, μ j * ((u j i * w i) * (u j k * w k)) := fun i => Finset.sum_comm
  simp_rw [e2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [dotProduct, sq, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

private theorem spec_trace {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) (u : Fin n → Vec n)
    (ho : ∀ j l, dotProduct (u j) (u l) = if j = l then 1 else 0)
    (hE : ∀ i k, M i k = ∑ j, μ j * (u j i * u j k)) :
    M.trace = ∑ j, μ j := by
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [hE]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := ho j j
  simp only [dotProduct, ite_true] at this
  have e : ∑ i, μ j * (u j i * u j i) = μ j * ∑ i, u j i * u j i := by rw [Finset.mul_sum]
  rw [e, this, mul_one]

private theorem spec_trace_sq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) (u : Fin n → Vec n)
    (ho : ∀ j l, dotProduct (u j) (u l) = if j = l then 1 else 0)
    (hM : ∀ j, M *ᵥ u j = μ j • u j) (hs : M.transpose = M)
    (hE : ∀ i k, M i k = ∑ j, μ j * (u j i * u j k)) :
    (M * M).trace = ∑ j, μ j ^ 2 := by
  have hsym : ∀ i k, M k i = M i k := fun i k => by
    have := congrFun (congrFun hs i) k
    simpa using this
  have h1 : ∀ i, (M * M) i i = ∑ k, M i k * M i k := fun i => by
    rw [Matrix.mul_apply]; exact Finset.sum_congr rfl fun k _ => by rw [hsym]
  simp only [Matrix.trace, Matrix.diag, h1]
  have h2 : ∀ i, ∑ k, M i k * M i k = ∑ j, μ j ^ 2 * (u j i) ^ 2 := by
    intro i
    calc ∑ k, M i k * M i k = ∑ k, (∑ j, μ j * (u j i * u j k)) * M i k := by
          exact Finset.sum_congr rfl fun k _ => by rw [← hE]
      _ = ∑ j, μ j * u j i * ∑ k, M i k * u j k := by
          simp_rw [Finset.sum_mul, Finset.mul_sum]; rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
      _ = ∑ j, μ j ^ 2 * (u j i) ^ 2 := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have := congrFun (hM j) i
          simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
          rw [this]; ring
  simp_rw [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := ho j j
  simp only [dotProduct, ite_true] at this
  have e : ∑ i, μ j ^ 2 * u j i ^ 2 = μ j ^ 2 * ∑ i, u j i * u j i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, this, mul_one]


private theorem jensen_N {n : ℕ} (μ : Fin n → ℝ) (u : Fin n → Vec n) (N : Vec n → ℝ)
    (hμ0 : ∀ j, 0 ≤ μ j) (hμ1 : ∑ j, μ j = 1)
    (ho : ∀ j, dotProduct (u j) (u j) = 1)
    (hN : ∀ w, N w = ∑ j, μ j * (dotProduct w (u j)) ^ 2) (hNc : Continuous N) (p : ℕ) :
    Integrable (fun w => (N w) ^ p) (Muon.Foundations.stdGaussianPi n) ∧
    ∫ w, (N w) ^ p ∂(Muon.Foundations.stdGaussianPi n)
      ≤ ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) := by
  have hpt : ∀ w, (N w) ^ p ≤ ∑ j, μ j * (dotProduct w (u j)) ^ (2 * p) := by
    intro w
    rw [hN w]
    have := (convexOn_pow p).map_sum_le (t := Finset.univ) (w := μ)
      (p := fun j => (dotProduct w (u j)) ^ 2) (fun j _ => hμ0 j) hμ1
      (fun j _ => Set.mem_Ici.2 (sq_nonneg _))
    simp only [smul_eq_mul] at this
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [← pow_mul, mul_comm 2 p]
  have hN0 : ∀ w, 0 ≤ (N w) ^ p := by
    intro w
    rw [hN w]
    exact pow_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hμ0 j) (sq_nonneg _)) p
  have hint : Integrable (fun w => ∑ j, μ j * (dotProduct w (u j)) ^ (2 * p))
      (Muon.Foundations.stdGaussianPi n) :=
    integrable_finsetSum _ fun j _ => (cond_moment (u j) p).1.const_mul _
  refine ⟨hint.mono' (hNc.pow p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_), ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hN0 w)]; exact hpt w
  · have hI : Integrable (fun w => (N w) ^ p) (Muon.Foundations.stdGaussianPi n) :=
      hint.mono' (hNc.pow p).aestronglyMeasurable
        (Filter.Eventually.of_forall fun w => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hN0 w)]; exact hpt w)
    refine (integral_mono hI hint hpt).trans (le_of_eq ?_)
    rw [integral_finsetSum _ fun j _ => (cond_moment (u j) p).1.const_mul _]
    have : ∀ j, ∫ w, μ j * (dotProduct w (u j)) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi n)
        = μ j * ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) := by
      intro j
      rw [integral_const_mul, (cond_moment (u j) p).2, ho j, one_pow, mul_one]
    simp_rw [this]
    rw [← Finset.sum_mul, hμ1, one_mul]


private theorem opNorm_sq_bound {m n : ℕ} (A : Mat m n) (u : Vec n) (hu : dotProduct u u = 1) :
    dotProduct (A *ᵥ u) (A *ᵥ u) ≤ opNorm A ^ 2 := by
  have h := ContinuousLinearMap.le_opNorm
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)) (WithLp.toLp 2 u)
  have h1 : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))
      (WithLp.toLp 2 u)‖ ^ 2 = dotProduct (A *ᵥ u) (A *ᵥ u) := by
    rw [LinearMap.coe_toContinuousLinearMap', EuclideanSpace.real_norm_sq_eq]
    simp only [res_toEuclideanLin_coe, dotProduct, sq]
  have h2 : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ = 1 := by
    have : ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ ^ 2 = 1 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      simpa [dotProduct, sq] using hu
    nlinarith [norm_nonneg (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))]
  rw [← h1]
  unfold opNorm
  rw [h2, mul_one] at h
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem N_facts {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    ∃ (μ : Fin n → ℝ) (u : Fin n → Vec n),
      (∀ j, μ j = svals A (j : ℕ) ^ 2) ∧
      (∀ j, dotProduct (u j) (u j) = 1) ∧
      ∑ j, μ j = 1 ∧
      (∀ j, μ j ≤ opNorm A ^ 2) ∧
      ((Aᵀ * A) * (Aᵀ * A)).trace = ∑ j, μ j ^ 2 ∧
      (∀ w, dotProduct (A *ᵥ w) (A *ᵥ w) = ∑ j, μ j * (dotProduct w (u j)) ^ 2) ∧
      (∀ w, dotProduct (A *ᵥ w) (A *ᵥ w) = ∑ i, ∑ k, w i * (Aᵀ * A) i k * w k) ∧
      (Aᵀ * A).trace = 1 := by
  obtain ⟨μ, u, hμ, ho, hc, hM⟩ := spectral A
  have hE := spec_entry (Aᵀ * A) μ u hc hM
  have hsymm : (Aᵀ * A).transpose = Aᵀ * A := by simp
  have hN2 : ∀ w, dotProduct (A *ᵥ w) (A *ᵥ w) = ∑ i, ∑ k, w i * (Aᵀ * A) i k * w k := by
    intro w
    have := res_dot_K_K A w w
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [this]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have htr : (Aᵀ * A).trace = ∑ j, μ j := spec_trace _ μ u ho hE
  have hfro : (Aᵀ * A).trace = 1 := by
    have h1 : ∑ i, ∑ j, ‖A i j‖ ^ 2 = 1 := by
      have := hA
      unfold fro at this
      have h0 : 0 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
      rw [Real.sqrt_eq_one] at this
      exact this
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs,
      sq_abs] at h1 ⊢
    rw [Finset.sum_comm] at h1
    simpa [sq] using h1
  refine ⟨μ, u, hμ, ?_, ?_, ?_, ?_, ?_, ?_, hfro⟩
  · intro j; have := ho j j; simpa using this
  · rw [← htr, hfro]
  · intro j
    have h1 : μ j = dotProduct (A *ᵥ u j) (A *ᵥ u j) := by
      rw [res_dot_K_K, Matrix.conjTranspose_eq_transpose_of_trivial, hM j, dotProduct_smul,
        smul_eq_mul]
      have := ho j j; simp at this; rw [this, mul_one]
    rw [h1]
    exact opNorm_sq_bound A (u j) (by have := ho j j; simpa using this)
  · exact spec_trace_sq _ μ u ho hM hsymm hE
  · intro w
    rw [hN2 w]; exact spec_quad _ μ u hE w
  · exact hN2

private theorem fubini_resid {m n : ℕ} (A : Mat m n) (p : ℕ)
    (hI : Integrable (fun w : Vec n => (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ p)
      (Muon.Foundations.stdGaussianPi n)) :
    Integrable (fun x => resid A x ^ (2 * p)) (gaussPair m n) ∧
    ∫ x, resid A x ^ (2 * p) ∂(gaussPair m n)
      = ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) *
        ∫ w, (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ p ∂(Muon.Foundations.stdGaussianPi n) := by
  have hmeas : Measurable (fun x : Vec m × Vec n => resid A x ^ (2 * p)) := by
    unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
  have hnorm : ∀ w : Vec n, ∫ z, ‖resid A (z, w) ^ (2 * p)‖ ∂(Muon.Foundations.stdGaussianPi m)
      = ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) * (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ p := by
    intro w
    have := (cond_moment (A *ᵥ w) p).2
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, resid]
    rw [abs_of_nonneg (Even.pow_nonneg ⟨p, by ring⟩ _)]
  have hf : Integrable (fun x => resid A x ^ (2 * p)) (gaussPair m n) := by
    unfold gaussPair
    refine (integrable_prod_iff' hmeas.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · exact Filter.Eventually.of_forall fun w => (cond_moment (A *ᵥ w) p).1
    · simp_rw [hnorm]; exact hI.const_mul _
  refine ⟨hf, ?_⟩
  unfold gaussPair
  rw [integral_prod_symm _ hf]
  simp_rw [show ∀ w : Vec n, ∫ z, resid A (z, w) ^ (2 * p) ∂(Muon.Foundations.stdGaussianPi m)
      = ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) * (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ p from
    fun w => (cond_moment (A *ᵥ w) p).2]
  rw [integral_const_mul]

private theorem svals_sum {m n : ℕ} (A : Mat m n) (e : ℕ) (he : e ≠ 0) :
    ∑ j : Fin n, svals A (j : ℕ) ^ e = ∑ k ∈ Finset.range (min m n), svals A k ^ e := by
  rw [Fin.sum_univ_eq_sum_range (fun k => svals A k ^ e) n]
  symm
  refine Finset.sum_subset (Finset.range_subset_range.2 (min_le_right m n)) ?_
  intro k hk hk'
  rw [Finset.mem_range] at hk hk'
  have hkm : m ≤ k := by
    by_contra h
    exact hk' (lt_min (not_le.1 h) hk)
  have hr : Module.finrank ℝ (Matrix.toEuclideanLin A).range ≤ m := by
    have := Submodule.finrank_le (Matrix.toEuclideanLin A).range
    simpa using this
  have : svals A k = 0 := by
    unfold svals
    rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
    exact hr.trans hkm
  rw [this, zero_pow he]

/-- `lem:app-setup-residual`(i), snapshot `cr-2026-10-23`, verbatim from the frozen source:

\begin{lemma}[Residual law]\label{lem:app-setup-residual}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm{A}_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and put $d=z^\T Aw$. Let $\alpha_1\ge\alpha_2\ge\dots\ge0$ be the
singular values of $A$ and $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item $d$ is symmetric, $\EE d^2=1$, $\EE d^4=3+6\sum_k\alpha_k^4\le3+6\norm{A}^2$, and
$\EE\abs{d}^{2p}\le\big((2p-1)!!\big)^2$ for every integer $p\ge1$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_setup_residual_i {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    (gaussPair m n).map (resid A) = (gaussPair m n).map (fun x => -resid A x) ∧
    ∫ x, resid A x ^ 2 ∂(gaussPair m n) = 1 ∧
    ∫ x, resid A x ^ 4 ∂(gaussPair m n) = 3 + 6 * ∑ k ∈ Finset.range (min m n), svals A k ^ 4 ∧
    ∫ x, resid A x ^ 4 ∂(gaussPair m n) ≤ 3 + 6 * opNorm A ^ 2 ∧
    ∀ p : ℕ, 1 ≤ p →
      ∫ x, |resid A x| ^ (2 * p) ∂(gaussPair m n) ≤
        ((Nat.doubleFactorial (2 * p - 1) : ℕ) : ℝ) ^ 2 := by
  obtain ⟨μ, u, hμ, ho, h1, hle, htr2, hN, hN2, htr⟩ := N_facts A hA
  have hμ0 : ∀ j, 0 ≤ μ j := fun j => by rw [hμ j]; exact sq_nonneg _
  have Nc : Continuous (fun w : Vec n => dotProduct (A *ᵥ w) (A *ᵥ w)) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have J := fun p => jensen_N μ u _ hμ0 h1 ho hN Nc p
  have F := fun p => fubini_resid A p (J p).1
  have hsq : ∑ j, μ j ^ 2 = ∑ k ∈ Finset.range (min m n), svals A k ^ 4 := by
    rw [← svals_sum A 4 (by norm_num)]
    exact Finset.sum_congr rfl fun j _ => by rw [hμ j]; ring
  -- second and fourth moments of N
  have hQ : (fun w : Vec n => dotProduct (A *ᵥ w) (A *ᵥ w))
      = fun w => ∑ i, ∑ k, w i * (Aᵀ * A) i k * w k := funext hN2
  have hmean : ∫ w, dotProduct (A *ᵥ w) (A *ᵥ w) ∂(Muon.Foundations.stdGaussianPi n) = 1 := by
    rw [hQ, Muon.Foundations.stdGaussianPi_quadratic_mean, htr]
  have hvar := Muon.Foundations.stdGaussianPi_quadratic_variance n (Aᵀ * A) (by simp)
  have hI1 : Integrable (fun w : Vec n => dotProduct (A *ᵥ w) (A *ᵥ w))
      (Muon.Foundations.stdGaussianPi n) := by simpa using (J 1).1
  have hI2 : Integrable (fun w : Vec n => (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ 2)
      (Muon.Foundations.stdGaussianPi n) := (J 2).1
  have h4 : ∫ w, (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ 2 ∂(Muon.Foundations.stdGaussianPi n)
      = 1 + 2 * ∑ j, μ j ^ 2 := by
    have e : ∀ w : Vec n, (∑ i, ∑ k, w i * (Aᵀ * A) i k * w k - (Aᵀ * A).trace) ^ 2
        = (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ 2 - 2 * (dotProduct (A *ᵥ w) (A *ᵥ w)) + 1 := by
      intro w; rw [← hN2 w, htr]; ring
    simp_rw [e] at hvar
    have hA' : Integrable (fun w : Vec n => (dotProduct (A *ᵥ w) (A *ᵥ w)) ^ 2
        - 2 * dotProduct (A *ᵥ w) (A *ᵥ w)) (Muon.Foundations.stdGaussianPi n) :=
      hI2.sub (hI1.const_mul 2)
    rw [integral_add hA' (integrable_const _), integral_sub hI2
      (hI1.const_mul 2), integral_const_mul, hmean, htr2] at hvar
    simp at hvar
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have hneg : (gaussPair m n).map (fun x : Vec m × Vec n => (-x.1, x.2)) = gaussPair m n := by
      have e : (fun x : Vec m × Vec n => (-x.1, x.2)) = Prod.map (fun z : Vec m => -z) id := rfl
      rw [e]
      unfold gaussPair
      rw [← Measure.map_prod_map _ _ (by fun_prop) measurable_id, stdG_map_neg, Measure.map_id]
    have hr : (fun x : Vec m × Vec n => -resid A x)
        = resid A ∘ (fun x : Vec m × Vec n => (-x.1, x.2)) := by
      funext x
      simp [resid, dotProduct, neg_mul, Finset.sum_neg_distrib]
    have hm : Measurable (resid A) := by
      unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
    rw [hr, ← Measure.map_map hm (by fun_prop), hneg]
  · have := (F 1).2
    simpa [hmean] using this
  · have e4 : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
      norm_num [Nat.doubleFactorial]
    have := (F 2).2
    rw [e4, h4] at this
    show ∫ x, resid A x ^ (2 * 2) ∂(gaussPair m n) = _
    rw [this, ← hsq]; ring
  · have e4 : ((Nat.doubleFactorial (2 * 2 - 1) : ℕ) : ℝ) = 3 := by
      norm_num [Nat.doubleFactorial]
    have := (F 2).2
    rw [e4, h4] at this
    have h5 : ∑ j, μ j ^ 2 ≤ opNorm A ^ 2 := by
      calc ∑ j, μ j ^ 2 ≤ ∑ j, μ j * opNorm A ^ 2 :=
            Finset.sum_le_sum fun j _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (hle j) (hμ0 j)
        _ = opNorm A ^ 2 := by rw [← Finset.sum_mul, h1, one_mul]
    show ∫ x, resid A x ^ (2 * 2) ∂(gaussPair m n) ≤ _
    rw [this]; linarith
  · intro p hp
    have hab : ∀ x : Vec m × Vec n, |resid A x| ^ (2 * p) = resid A x ^ (2 * p) := fun x => by
      rw [pow_mul, pow_mul, sq_abs]
    simp_rw [hab]
    rw [(F p).2, sq]
    exact mul_le_mul_of_nonneg_left (J p).2 (Nat.cast_nonneg _)

/-! ### Private helpers for `lem_app_setup_residual_ii` (task P-A.9.P2) -/

/-- Private copy of the rotation `x ↦ O x` on `EuclideanSpace` (from `Muon.Foundations.GaussianExtra`,
not imported here). -/
private noncomputable def r2_rotE (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearEquiv.isometryOfInner
    { toFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)
      invFun := fun x => WithLp.toLp 2 ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)
      map_add' := by
        intro x y
        ext i
        simp [Matrix.mulVec_add]
      map_smul' := by
        intro c x
        ext i
        simp [Matrix.mulVec_smul]
      left_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
          (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
      right_inv := by
        intro x
        have h : (O : Matrix (Fin n) (Fin n) ℝ) * (O : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 :=
          (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).1 O.2
        ext i
        change ((O : Matrix (Fin n) (Fin n) ℝ) *ᵥ
          ((O : Matrix (Fin n) (Fin n) ℝ)ᵀ *ᵥ WithLp.ofLp x)) i
          = WithLp.ofLp x i
        rw [Matrix.mulVec_mulVec, h, Matrix.one_mulVec] }
    (by
      intro x y
      have h : (O : Matrix (Fin n) (Fin n) ℝ)ᵀ * (O : Matrix (Fin n) (Fin n) ℝ) = 1 :=
        (Matrix.mem_orthogonalGroup_iff' (Fin n) ℝ).1 O.2
      simp only [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
      simp only [EuclideanSpace.inner_eq_star_dotProduct, Matrix.star_mulVec,
        Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul, h, Matrix.vecMul_one,
        dotProduct_comm])

private theorem r2_map_toLp (n : ℕ) :
    (Muon.Foundations.stdGaussianPi n).map (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n))
      = stdGaussian (EuclideanSpace ℝ (Fin n)) := by
  unfold Muon.Foundations.stdGaussianPi
  exact map_pi_eq_stdGaussian

/-- Private copy of rotation invariance of the standard Gaussian vector. -/
private theorem r2_map_orth (n : ℕ) (O : Matrix.orthogonalGroup (Fin n) ℝ) :
    (Muon.Foundations.stdGaussianPi n).map (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = Muon.Foundations.stdGaussianPi n := by
  have hrot : Measurable (r2_rotE n O) := (r2_rotE n O).continuous.measurable
  have hf : Measurable (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z) := by
    fun_prop
  have he : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
  have hemb : MeasurableEmbedding (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding
  have hG := stdGaussian_map (r2_rotE n O)
  have hcomp : (WithLp.toLp 2 ∘ fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = (r2_rotE n O) ∘ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) := by
    funext z
    ext i
    simp [r2_rotE]
  have key : ((Muon.Foundations.stdGaussianPi n).map
      (fun z : Fin n → ℝ => (O : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)).map (WithLp.toLp 2)
      = (Muon.Foundations.stdGaussianPi n).map (WithLp.toLp 2) := by
    rw [Measure.map_map he hf, hcomp, ← Measure.map_map hrot he, r2_map_toLp, hG]
  exact hemb.map_injective key

/-- Private: `svals A k = 0` once `min m n ≤ k` (rank bound). -/
private theorem r2_svals_zero {m n : ℕ} (A : Mat m n) (k : ℕ) (hk : min m n ≤ k) :
    svals A k = 0 := by
  have hr : Module.finrank ℝ (Matrix.toEuclideanLin A).range ≤ k := by
    rcases min_le_iff.1 hk with h | h
    · have := Submodule.finrank_le (Matrix.toEuclideanLin A).range
      simp at this
      omega
    · have := LinearMap.finrank_range_le (Matrix.toEuclideanLin A)
      simp at this
      omega
  unfold svals
  rw [LinearMap.singularValues_eq_zero_iff_le_finrank_range]
  exact hr

/-- Private: characteristic function of `z ↦ z·v` under the standard Gaussian. -/
private theorem r2_inner {m : ℕ} (v : Vec m) (θ : ℝ) :
    ∫ z, Complex.exp (((θ * dotProduct z v : ℝ) : ℂ) * Complex.I) ∂(Muon.Foundations.stdGaussianPi m)
      = ((Real.exp (-(θ ^ 2 * dotProduct v v) / 2) : ℝ) : ℂ) := by
  have hm : Measurable (fun z : Vec m => dotProduct z v) := by
    unfold dotProduct; fun_prop
  have hg : Measurable (fun x : ℝ => Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  have e1 : ∫ z, Complex.exp (((θ * dotProduct z v : ℝ) : ℂ) * Complex.I)
        ∂(Muon.Foundations.stdGaussianPi m)
      = ∫ x, Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I)
        ∂((Muon.Foundations.stdGaussianPi m).map (fun z => dotProduct z v)) :=
    (integral_map hm.aemeasurable hg.aestronglyMeasurable).symm
  have e2 : ∀ ν : Measure ℝ, ∫ x, Complex.exp (((θ * x : ℝ) : ℂ) * Complex.I) ∂ν
      = charFun ν θ := by
    intro ν
    unfold charFun
    congr 1
  have hc2 : Real.sqrt (dotProduct v v) ^ 2 = dotProduct v v := by
    apply Real.sq_sqrt
    have : dotProduct v v = ∑ i, v i ^ 2 := by simp [dotProduct, sq]
    rw [this]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [e1, lin_law v, gaussianReal_map_const_mul, e2, charFun_gaussianReal, Complex.ofReal_exp]
  congr 1
  simp [hc2]
  ring

/-- Private: the outer Gaussian integral after SVD coordinates. -/
private theorem r2_outer {n : ℕ} (μ : Fin n → ℝ) (u : Fin n → Vec n) (hμ0 : ∀ j, 0 ≤ μ j)
    (horth : ∀ j l, dotProduct (u j) (u l) = if j = l then 1 else 0) (θ : ℝ) :
    ∫ w, Real.exp (-(θ ^ 2 * ∑ j, μ j * dotProduct w (u j) ^ 2) / 2)
        ∂(Muon.Foundations.stdGaussianPi n)
      = ∏ j, (1 + θ ^ 2 * μ j) ^ (-(1 / 2 : ℝ)) := by
  have hMM : (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ)
      * (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
    ext j l
    rw [Matrix.one_apply, ← horth j l]
    simp [Matrix.mul_apply, dotProduct]
  have hO : (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ)
      ∈ Matrix.orthogonalGroup (Fin n) ℝ := (Matrix.mem_orthogonalGroup_iff (Fin n) ℝ).2 hMM
  have hmap : (Muon.Foundations.stdGaussianPi n).map
      (fun z : Vec n => (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ z)
      = Muon.Foundations.stdGaussianPi n := r2_map_orth n ⟨_, hO⟩
  have hcoord : ∀ (y : Vec n) (j : Fin n),
      ((Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ y) j = dotProduct y (u j) := by
    intro y j
    simp [Matrix.mulVec, dotProduct, mul_comm]
  have hFc : Measurable (fun y : Vec n => ∏ j, Real.exp (-(θ ^ 2 * μ j / 2) * y j ^ 2)) := by
    fun_prop
  have hφ : Measurable (fun w : Vec n =>
      (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ w) := by
    fun_prop
  have hpt : ∀ w : Vec n, Real.exp (-(θ ^ 2 * ∑ j, μ j * dotProduct w (u j) ^ 2) / 2)
      = (fun y : Vec n => ∏ j, Real.exp (-(θ ^ 2 * μ j / 2) * y j ^ 2))
          ((Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ w) := by
    intro w
    simp only [hcoord]
    rw [← Real.exp_sum]
    congr 1
    simp [Finset.mul_sum, Finset.sum_div, neg_div]
    refine Finset.sum_congr rfl fun j _ => by ring
  simp only [hpt]
  have e1 : ∫ w, (fun y : Vec n => ∏ j, Real.exp (-(θ ^ 2 * μ j / 2) * y j ^ 2))
        ((Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ w)
        ∂(Muon.Foundations.stdGaussianPi n)
      = ∫ y, (fun y : Vec n => ∏ j, Real.exp (-(θ ^ 2 * μ j / 2) * y j ^ 2)) y
        ∂((Muon.Foundations.stdGaussianPi n).map
          (fun w : Vec n => (Matrix.of fun j i => u j i : Matrix (Fin n) (Fin n) ℝ) *ᵥ w)) :=
    (integral_map hφ.aemeasurable hFc.aestronglyMeasurable).symm
  rw [e1, hmap]
  have hp := integral_fintype_prod_eq_prod (μ := fun _ : Fin n => gaussianReal 0 1)
    (f := fun (j : Fin n) (x : ℝ) => Real.exp (-(θ ^ 2 * μ j / 2) * x ^ 2))
  unfold Muon.Foundations.stdGaussianPi
  rw [hp]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Muon.Foundations.gaussian_laplace _ (by have := hμ0 j; positivity)]
  rw [show 1 + 2 * (θ ^ 2 * μ j / 2) = 1 + θ ^ 2 * μ j by ring]

/-- `lem:app-setup-residual`(ii), snapshot `cr-2026-10-23`, verbatim from the frozen source:

\begin{lemma}[Residual law]\label{lem:app-setup-residual}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm{A}_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and put $d=z^\T Aw$. Let $\alpha_1\ge\alpha_2\ge\dots\ge0$ be the
singular values of $A$ and $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item $\EE e^{i\theta d}=\prod_k(1+\theta^2\alpha_k^2)^{-1/2}$ for real $\theta$, and
$0\le\log\EE e^{i\theta d}+\theta^2/2\le\theta^4\norm{A}^2/4$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_setup_residual_ii {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    (∀ θ : ℝ, ∫ x, Complex.exp (((θ * resid A x : ℝ) : ℂ) * Complex.I) ∂(gaussPair m n)
        = ((residCharProd A θ : ℝ) : ℂ)) ∧
    ∀ θ : ℝ, 0 ≤ Real.log (residCharProd A θ) + θ ^ 2 / 2 ∧
      Real.log (residCharProd A θ) + θ ^ 2 / 2 ≤ θ ^ 4 * opNorm A ^ 2 / 4 := by
  obtain ⟨μ, u, hsq, horth, hcomp, hM⟩ := spectral A
  obtain ⟨μ₀, -, hμ₀, -, h1₀, hle₀, -⟩ := N_facts A hA
  have hμ0 : ∀ j : Fin n, 0 ≤ μ j := fun j => by rw [hsq j]; exact sq_nonneg _
  have e : ∀ j : Fin n, μ j = μ₀ j := fun j => (hsq j).trans (hμ₀ j).symm
  have hS1 : ∑ j : Fin n, μ j = 1 := by
    rw [Finset.sum_congr rfl (fun j _ => e j)]; exact h1₀
  have hle : ∀ j : Fin n, μ j ≤ opNorm A ^ 2 := fun j => by rw [e j]; exact hle₀ j
  have hsum2 : ∑ j : Fin n, μ j ^ 2 ≤ opNorm A ^ 2 := by
    calc ∑ j, μ j ^ 2 ≤ ∑ j, μ j * opNorm A ^ 2 :=
          Finset.sum_le_sum fun j _ => by rw [sq]; exact mul_le_mul_of_nonneg_left (hle j) (hμ0 j)
      _ = opNorm A ^ 2 := by rw [← Finset.sum_mul, hS1, one_mul]
  have hN2 : ∀ w : Vec n, dotProduct (A *ᵥ w) (A *ᵥ w) = ∑ i, ∑ k, w i * (Aᵀ * A) i k * w k := by
    intro w
    have := res_dot_K_K A w w
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    rw [this]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hE := spec_entry (Aᵀ * A) μ u hcomp hM
  have hN : ∀ w : Vec n, dotProduct (A *ᵥ w) (A *ᵥ w) = ∑ j, μ j * dotProduct w (u j) ^ 2 := by
    intro w
    rw [hN2 w]
    exact spec_quad _ μ u hE w
  have hprod : ∀ θ : ℝ, residCharProd A θ = ∏ j : Fin n, (1 + θ ^ 2 * μ j) ^ (-(1 / 2 : ℝ)) := by
    intro θ
    have e' : ∏ j : Fin n, (1 + θ ^ 2 * μ j) ^ (-(1 / 2 : ℝ))
        = ∏ k ∈ Finset.range n, (1 + θ ^ 2 * svals A k ^ 2) ^ (-(1 / 2 : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range (fun k => (1 + θ ^ 2 * svals A k ^ 2) ^ (-(1 / 2 : ℝ))) n]
      exact Finset.prod_congr rfl fun j _ => by simp only [hsq]
    rw [e']
    unfold residCharProd
    refine Finset.prod_subset (Finset.range_subset_range.2 (min_le_right m n)) fun k _ hk' => ?_
    have hk'' : min m n ≤ k := by rw [Finset.mem_range, not_lt] at hk'; exact hk'
    rw [r2_svals_zero A k hk'']
    simp
  refine ⟨fun θ => ?_, fun θ => ?_⟩
  · have hmeas : Measurable (fun x : Vec m × Vec n =>
        Complex.exp (((θ * resid A x : ℝ) : ℂ) * Complex.I)) := by
      unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
    have hint : Integrable (fun x : Vec m × Vec n =>
        Complex.exp (((θ * resid A x : ℝ) : ℂ) * Complex.I)) (gaussPair m n) :=
      (integrable_const (1 : ℝ)).mono' hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => (Complex.norm_exp_ofReal_mul_I _).le)
    have hin : ∀ w : Vec n, ∫ z, Complex.exp (((θ * resid A (z, w) : ℝ) : ℂ) * Complex.I)
        ∂(Muon.Foundations.stdGaussianPi m)
        = ((Real.exp (-(θ ^ 2 * dotProduct (A *ᵥ w) (A *ᵥ w)) / 2) : ℝ) : ℂ) :=
      fun w => r2_inner (A *ᵥ w) θ
    unfold gaussPair at hint ⊢
    rw [integral_prod_symm _ hint]
    simp_rw [hin]
    rw [integral_complex_ofReal, hprod θ]
    congr 1
    simp_rw [hN]
    exact r2_outer μ u hμ0 horth θ
  · have hlog : Real.log (residCharProd A θ) = -(1 / 2 : ℝ) * ∑ j, Real.log (1 + θ ^ 2 * μ j) := by
      have hpos : ∀ j, 0 < 1 + θ ^ 2 * μ j := fun j => by have := hμ0 j; positivity
      rw [hprod θ, Real.log_prod (fun j _ => (Real.rpow_pos_of_pos (hpos j) _).ne'), Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => Real.log_rpow (hpos j) _
    have hbnd : ∀ j, θ ^ 2 * μ j - (θ ^ 2 * μ j) ^ 2 / 2 ≤ Real.log (1 + θ ^ 2 * μ j) ∧
        Real.log (1 + θ ^ 2 * μ j) ≤ θ ^ 2 * μ j := by
      intro j
      have hx : 0 ≤ θ ^ 2 * μ j := mul_nonneg (sq_nonneg _) (hμ0 j)
      refine ⟨le_trans ?_ (Real.le_log_one_add_of_nonneg hx), ?_⟩
      · rw [le_div_iff₀ (by linarith)]
        nlinarith [pow_nonneg hx 3]
      · have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + θ ^ 2 * μ j)
        linarith
    have hSx : ∑ j, θ ^ 2 * μ j = θ ^ 2 := by rw [← Finset.mul_sum, hS1, mul_one]
    have hSq : ∑ j, (θ ^ 2 * μ j) ^ 2 / 2 = θ ^ 4 / 2 * ∑ j, μ j ^ 2 := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    have hlo : θ ^ 2 - θ ^ 4 / 2 * ∑ j, μ j ^ 2 ≤ ∑ j, Real.log (1 + θ ^ 2 * μ j) := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hbnd j).1)
      rw [Finset.sum_sub_distrib, hSx, hSq] at this
      exact this
    have hhi : ∑ j, Real.log (1 + θ ^ 2 * μ j) ≤ θ ^ 2 := by
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hbnd j).2)
      rw [hSx] at this
      exact this
    have h4 : 0 ≤ θ ^ 4 := by positivity
    have hS := mul_le_mul_of_nonneg_left hsum2 h4
    rw [hlog]
    constructor
    · nlinarith
    · nlinarith

/-- Operator norm bounded by the Frobenius norm (private helper, `lem_app_setup_residual_iii`). -/
private lemma r3_opNorm_le_fro {p q : ℕ} (K : Mat p q) : opNorm K ≤ fro K := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, fro, ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
          exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2
      = ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 := Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := (Finset.sum_mul _ _ _).symm

/-- Fourth moment of the residual is integrable (private helper, `lem_app_setup_residual_iii`). -/
private theorem r3_int4 {m n : ℕ} (A : Mat m n) (hA : fro A = 1) :
    Integrable (fun x => resid A x ^ 4) (gaussPair m n) := by
  obtain ⟨μ, u, hμ, ho, h1, -, -, hN, -, -⟩ := N_facts A hA
  have hμ0 : ∀ j, 0 ≤ μ j := fun j => by rw [hμ j]; exact sq_nonneg _
  have Nc : Continuous (fun w : Vec n => dotProduct (A *ᵥ w) (A *ᵥ w)) := by
    unfold dotProduct Matrix.mulVec dotProduct; fun_prop
  have J := (jensen_N μ u (fun w : Vec n => dotProduct (A *ᵥ w) (A *ᵥ w)) hμ0 h1 ho hN Nc 2).1
  have F := (fubini_resid A 2 J).1
  exact F

/-- `lem:app-setup-residual`(iii), snapshot `cr-2026-10-23`, verbatim from the frozen source:

\begin{lemma}[Residual law]\label{lem:app-setup-residual}
Let $A\in\R^{\Nout\times\Nin}$ be deterministic with $\norm{A}_\F=1$, let
$z\sim\mathcal N(0,\Id_{\Nout})$ and $w\sim\mathcal N(0,\Id_{\Nin})$ be
independent, and put $d=z^\T Aw$. Let $\alpha_1\ge\alpha_2\ge\dots\ge0$ be the
singular values of $A$ and $g\sim\mathcal N(0,1)$.
\begin{enumerate}[label=(\roman*)]
\item Along any sequence of such $A=A_B$ with $\norm{A_B}\to0$, $d\Rightarrow g$ in distribution,
and $\EE\,\psi(d)\to\EE\,\psi(g)$ for every continuous $\psi$ with $\abs{\psi(x)}\le1+x^2$.
\end{enumerate}
\end{lemma}
-/
theorem lem_app_setup_residual_iii {m n : ℕ → ℕ} {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : ∀ k, Mat (m k) (n k)) (z : ∀ k, Ω k → Vec (m k)) (w : ∀ k, Ω k → Vec (n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0)) :
    TendstoInDistribution (fun k ω => resid (A k) (z k ω, w k ω)) atTop id P
        (gaussianReal 0 1) ∧
    ∀ ψ : ℝ → ℝ, Continuous ψ → (∀ x, |ψ x| ≤ 1 + x ^ 2) →
      Tendsto (fun k => ∫ ω, ψ (resid (A k) (z k ω, w k ω)) ∂(P k)) atTop
        (𝓝 (∫ x, ψ x ∂(gaussianReal 0 1))) := by
  have hm : ∀ k, Measurable (fun x : Vec (m k) × Vec (n k) => resid (A k) x) := fun k => by
    unfold resid dotProduct Matrix.mulVec dotProduct; fun_prop
  have hpair : ∀ k, AEMeasurable (fun ω => (z k ω, w k ω)) (P k) := by
    intro k
    by_contra h
    have hne : Nonempty (Fin (m k)) := by
      by_contra hc
      rw [not_nonempty_iff] at hc
      have hA1 := hA k
      unfold fro at hA1
      simp at hA1
    obtain ⟨i0⟩ := hne
    have e := hlaw k
    rw [Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero (P k))] at e
    have e2 := congrArg (Measure.map Prod.fst) e
    rw [Measure.map_dirac' measurable_fst _] at e2
    unfold gaussPair at e2
    rw [Measure.map_fst_prod] at e2
    simp only [measure_univ, one_smul] at e2
    have e3 := congrArg (Measure.map (Function.eval i0)) e2
    rw [Measure.map_dirac' (measurable_pi_apply i0) _] at e3
    unfold Muon.Foundations.stdGaussianPi at e3
    rw [Measure.pi_map_eval] at e3
    simp only [measure_univ, Finset.prod_const_one, one_smul] at e3
    have hsing : ∀ a : ℝ, gaussianReal 0 1 {a} = 0 := fun a =>
      gaussianReal_absolutelyContinuous 0 one_ne_zero Real.volume_singleton
    obtain ⟨a, ha⟩ : ∃ a : ℝ, Measure.dirac a = gaussianReal 0 1 := ⟨_, e3⟩
    have h7 := hsing a
    rw [← ha, Measure.dirac_apply_of_mem (Set.mem_singleton a)] at h7
    norm_num at h7
  have hD : ∀ k, AEMeasurable (fun ω => resid (A k) (z k ω, w k ω)) (P k) :=
    fun k => (hm k).comp_aemeasurable (hpair k)
  have hmap : ∀ k, (P k).map (fun ω => resid (A k) (z k ω, w k ω))
      = (gaussPair (m k) (n k)).map (resid (A k)) := by
    intro k
    rw [← hlaw k]
    exact (AEMeasurable.map_map_of_aemeasurable (hm k).aemeasurable (hpair k)).symm
  have hcont : ∀ t : ℝ, Continuous (fun x : ℝ => Complex.exp ((t : ℂ) * (x : ℂ) * Complex.I)) :=
    fun t => by fun_prop
  have hchar : ∀ k t, charFun ((P k).map (fun ω => resid (A k) (z k ω, w k ω))) t
      = ((residCharProd (A k) t : ℝ) : ℂ) := by
    intro k t
    rw [hmap k, charFun_apply_real, integral_map (hm k).aemeasurable (hcont t).aestronglyMeasurable]
    have h2 := (lem_app_setup_residual_ii (A k) (hA k)).1 t
    simpa only [Complex.ofReal_mul] using h2
  have hpos : ∀ k t, 0 < residCharProd (A k) t := fun k t =>
    Finset.prod_pos fun j _ => Real.rpow_pos_of_pos (by positivity) _
  have hlog : ∀ t : ℝ, Tendsto (fun k => Real.log (residCharProd (A k) t)) atTop
      (𝓝 (-(t ^ 2 / 2))) := by
    intro t
    have hsq : Tendsto (fun k => opNorm (A k) ^ 2) atTop (𝓝 0) := by
      simpa using hAn.pow 2
    have hup : Tendsto (fun k => -(t ^ 2 / 2) + t ^ 4 * opNorm (A k) ^ 2 / 4) atTop
        (𝓝 (-(t ^ 2 / 2))) := by
      have := ((hsq.const_mul (t ^ 4)).div_const 4).const_add (-(t ^ 2 / 2))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun k => ?_) (fun k => ?_)
    · dsimp only
      have := (lem_app_setup_residual_ii (A k) (hA k)).2 t
      linarith [this.1]
    · dsimp only
      have := (lem_app_setup_residual_ii (A k) (hA k)).2 t
      linarith [this.2]
  have hR : ∀ t : ℝ, Tendsto (fun k => residCharProd (A k) t) atTop
      (𝓝 (Real.exp (-(t ^ 2 / 2)))) := by
    intro t
    have := (Real.continuous_exp.tendsto _).comp (hlog t)
    exact this.congr fun k => Real.exp_log (hpos k t)
  have hdist : TendstoInDistribution (fun k ω => resid (A k) (z k ω, w k ω)) atTop id P
      (gaussianReal 0 1) := by
    refine TendstoInDistribution.of_tendsto_charFun (fun k => hD k) aemeasurable_id ?_
    intro t
    have hc : ∀ k, charFun ((P k).map (fun ω => resid (A k) (z k ω, w k ω))) t
        = ((residCharProd (A k) t : ℝ) : ℂ) := fun k => hchar k t
    have hlim' : Tendsto (fun k => ((residCharProd (A k) t : ℝ) : ℂ)) atTop
        (𝓝 ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (hR t)
    have hgt : charFun ((gaussianReal 0 1).map id) t = ((Real.exp (-(t ^ 2 / 2)) : ℝ) : ℂ) := by
      rw [Measure.map_id, charFun_gaussianReal, Complex.ofReal_exp]
      congr 1
      push_cast
      ring
    rw [hgt]
    exact hlim'.congr fun k => (hc k).symm
  refine ⟨hdist, fun ψ hψc hψb => ?_⟩
  have hfour : ∀ k, Integrable (fun ω => resid (A k) (z k ω, w k ω) ^ 4) (P k) := by
    intro k
    have h1 : Integrable (fun x : ℝ => x ^ 4)
        ((P k).map (fun ω => resid (A k) (z k ω, w k ω))) := by
      rw [hmap k, integrable_map_measure (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable
        (hm k).aemeasurable]
      exact r3_int4 (A k) (hA k)
    rw [integrable_map_measure (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable
      (hD k)] at h1
    exact h1
  have hbd : ∀ k, ∫ ω, resid (A k) (z k ω, w k ω) ^ 4 ∂(P k) ≤ 9 := by
    intro k
    have e1 : ∫ ω, resid (A k) (z k ω, w k ω) ^ 4 ∂(P k)
        = ∫ x, x ^ 4 ∂((P k).map (fun ω => resid (A k) (z k ω, w k ω))) :=
      (integral_map (hD k) (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable).symm
    rw [e1, hmap k, integral_map (hm k).aemeasurable
      (by fun_prop : Measurable fun x : ℝ => x ^ 4).aestronglyMeasurable]
    show ∫ x, resid (A k) x ^ 4 ∂(gaussPair (m k) (n k)) ≤ 9
    have h4 := (lem_app_setup_residual_i (A k) (hA k)).2.2.2.1
    have hop : opNorm (A k) ≤ 1 := by
      have := r3_opNorm_le_fro (A k)
      rw [hA k] at this
      exact this
    have hop0 : 0 ≤ opNorm (A k) := by unfold opNorm; exact norm_nonneg _
    nlinarith [h4, hop, hop0]
  exact Muon.Foundations.tendsto_integral_of_tendstoInDistribution_of_uniform_fourth_moment
    P (gaussianReal 0 1) (fun k ω => resid (A k) (z k ω, w k ω)) id hdist hfour ⟨9, hbd⟩ ψ hψc hψb

end Muon.Setup
