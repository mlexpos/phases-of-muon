import Mathlib

/-!
# Shared conventions for the Muon appendix formalization

Snapshot `cr-2026-10-22`. Source: `sections/01-setup/section.tex` (Appendix A, subsection
"Conventions" at l.27–40 and the display equations cited per declaration), with the Lean
representation fixed in `sections/01-setup/CARD.md` §2.

This file holds only the objects every appendix section imports: matrix and vector types,
the named norms, the entrywise mean and matrix covariance tensor, the outer product, the
PSD square root and the regularized map `Q`, the EMA power sums, the covariance and spectral
measure objects, the proportional regime, and the deterministic-equivalent relation.
Section-specific model, algorithm and frozen-state objects live in `Muon.Setup`.

The declarations live in namespace `Muon` (user ruling for L-0.3; CAMPAIGN §3 names the
shared namespace `Muon.Foundations` — see the interface report).
-/
open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology

noncomputable section

namespace Muon

/-! ## Matrices and vectors -/

/-- Real `m × n` matrices, `m = N_out`, `n = N_in` (paper `W ∈ ℝ^{N_out × N_in}`,
`section.tex` l.33–34 and `def:app-setup-model` l.47–56). -/
abbrev Mat (m n : ℕ) := Matrix (Fin m) (Fin n) ℝ

/-- Real vectors of dimension `m` (`section.tex` l.39–40, samples `X_out`, `X_in`). -/
abbrev Vec (m : ℕ) := Fin m → ℝ

/-! ## Named norms

No norm instance on `Matrix` is used in any statement. The three norms are plain functions;
the bridge lemmas identify them with Mathlib's scoped instances, which are opened only inside
the bridge section. -/

/-- Frobenius norm `‖K‖_F` (`section.tex` conventions l.30–31, `\norm{X}_\F`). Generic over
`RCLike 𝕜` so that the complex test matrices of `def:deterministic-equivalent` are covered. -/
def fro {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) : ℝ :=
  Real.sqrt (∑ i, ∑ j, ‖K i j‖ ^ 2)

/-- Operator (spectral) norm `‖K‖` (`section.tex` conventions l.30–31, `\norm{X}`): the norm
of `K` as a continuous linear map between Euclidean spaces. Generic over `RCLike 𝕜`
(complex test matrices of `def:deterministic-equivalent`). -/
def opNorm {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) : ℝ :=
  ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)‖

/-- Nuclear norm `‖K‖_*` (`section.tex` conventions l.30–31, `\norm{X}_*`): the sum of the
singular values of `K`, via Mathlib's `LinearMap.singularValues` (0-indexed, finitely
supported, so `Finsupp.sum` is the full sum). Real matrices only. -/
def nuc {m n : ℕ} (K : Mat m n) : ℝ :=
  (Matrix.toEuclideanLin K).singularValues.sum fun _ s => s

section NormBridges

open scoped Matrix.Norms.Frobenius in
/-- Bridge: `fro` is the norm of Mathlib's Frobenius normed group structure on matrices.
Source: `section.tex` conventions l.30–31. -/
theorem fro_eq_norm {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) :
    fro K = ‖K‖ := by
  rw [Matrix.frobenius_norm_def, fro, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Real.rpow_two]

open scoped Matrix.Norms.L2Operator in
/-- Bridge: `opNorm` is the norm of Mathlib's `L2` operator normed group structure on
matrices (`Matrix.Norms.L2Operator`). Source: `section.tex` conventions l.30–31. -/
theorem opNorm_eq_norm {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) :
    opNorm K = ‖K‖ := by
  rw [Matrix.l2_opNorm_def]
  rfl

private lemma eig_congr_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S S' : E →ₗ[ℝ] E) (h : S = S') (hS : S.IsSymmetric)
    (hS' : S'.IsSymmetric) (n : ℕ) (hn : Module.finrank ℝ E = n) (i : Fin n) :
    hS.eigenvalues hn i = hS'.eigenvalues hn i := by
  subst h; rfl

private lemma sum_eig_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (S : E →ₗ[ℝ] E) (hS : S.IsSymmetric) (n1 n2 : ℕ)
    (h1 : Module.finrank ℝ E = n1) (h2 : Module.finrank ℝ E = n2) (f : ℝ → ℝ) :
    ∑ i : Fin n1, f (hS.eigenvalues h1 i) = ∑ j : Fin n2, f (hS.eigenvalues h2 j) := by
  have : n1 = n2 := h1.symm.trans h2
  subst this
  rfl

private lemma trace_cfc_sqrt_herm {n : ℕ} (A : Mat n n) (hA : A.IsHermitian) (hA0 : 0 ≤ A) :
    (CFC.sqrt A).trace = ∑ i : Fin n,
      √((Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin i) := by
  have hcfc : CFC.sqrt A = hA.cfc Real.sqrt := by
    rw [CFC.sqrt_eq_real_sqrt A hA0, cfcₙ_eq_cfc, hA.cfc_eq]
  rw [hcfc, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm, ← mul_assoc,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]
  calc ∑ i, √(hA.eigenvalues i)
      = ∑ j : Fin (Fintype.card (Fin n)), √(hA.eigenvalues₀ j) :=
        Equiv.sum_comp _ (fun j => √(hA.eigenvalues₀ j))
    _ = _ := sum_eig_eq _ _ _ _ finrank_euclideanSpace finrank_euclideanSpace_fin Real.sqrt

/-- Bridge: the nuclear norm is the trace of the PSD square root of `KᵀK`, i.e. the sum of
singular values. There is no Mathlib nuclear norm; this identity is the stated bridge.
Source: `section.tex` conventions l.30–31. -/
theorem nuc_eq_trace_cfc_sqrt {m n : ℕ} (K : Mat m n) :
    nuc K = (CFC.sqrt (Kᵀ * K)).trace := by
  classical
  have hA : (Kᵀ * K).IsHermitian := by simpa using Matrix.isHermitian_conjTranspose_mul_self K
  have hA0 : 0 ≤ Kᵀ * K := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self K
  have hop : (Matrix.toEuclideanLin K).adjoint ∘ₗ Matrix.toEuclideanLin K
      = Matrix.toEuclideanLin (Kᵀ * K) := by
    rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (Matrix.toLpLin_mul (p := 2) (q := 2) (r := 2) Kᵀ K).symm
  have hsupp : (Matrix.toEuclideanLin K).singularValues.support ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_range]
    by_contra h
    push Not at h
    exact (Finsupp.mem_support_iff.mp hi)
      ((Matrix.toEuclideanLin K).singularValues_of_finrank_le (by rw [finrank_euclideanSpace_fin]; exact h))
  unfold nuc
  rw [Finsupp.sum_of_support_subset _ hsupp _ (fun i _ => rfl),
    ← Fin.sum_univ_eq_sum_range (fun i => (Matrix.toEuclideanLin K).singularValues i) n,
    trace_cfc_sqrt_herm _ hA hA0]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.singularValues_fin _ finrank_euclideanSpace_fin i]
  congr 1
  exact eig_congr_aux _ _ hop _ _ n _ i

end NormBridges

/-! ## Entrywise mean and covariance tensor -/

/-- Entrywise matrix expectation `E[X]` (`section.tex` conventions l.39: "Expectations of
matrices are entrywise"). Bochner integrals on `Matrix` would need a norm instance, so the
mean is defined entrywise. -/
def mean {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω) (X : Ω → Mat m n) :
    Mat m n :=
  Matrix.of fun i j => ∫ ω, X ω i j ∂P

/-- Four-index covariance tensor `Cov[X_{ij}, X_{kl}]` of a random matrix (used for the batch
covariance `V_B` and `Σ_G` in `eqn:app-setup-tensor`, `eqn:app-setup-batch-cov`,
`eqn:app-setup-VB`, `section.tex` l.657–675). Built from `ProbabilityTheory.covariance`;
`Matrix.vec` is deliberately not used (column-major, indexed by `n × m`). -/
def covT {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω) (X : Ω → Mat m n) :
    Fin m → Fin n → Fin m → Fin n → ℝ :=
  fun i j k l => covariance (fun ω => X ω i j) (fun ω => X ω k l) P

/-! ## Outer product -/

/-- Outer product `x ⊗ y` (`section.tex` notation `\tensor`, D10 convention). -/
abbrev outer {m n : ℕ} (x : Vec m) (y : Vec n) : Mat m n := Matrix.vecMulVec x y

/-! ## PSD square root and the regularized map `Q_ϱ` -/

/-- Regularized spectral map `Q_ϱ(K) = K φ_ϱ(KᵀK)`, `φ_ϱ(x) = (x+ϱ)^{-1/2}`
(`eqn:app-setup-Q`, `section.tex` l.262–273). The value at `ϱ = 0` on the zero eigenspace is
forced to `0` by `Real.zero_rpow`, matching `φ_ϱ(0) := 0`. Every lemma about `Q` carries
`0 ≤ ϱ` (or `0 < ϱ`); negative `ϱ` is outside the paper's domain. -/
def Q (ϱ : ℝ) {m n : ℕ} (K : Mat m n) : Mat m n :=
  K * cfc (fun x : ℝ => (x + ϱ) ^ (-(1 / 2 : ℝ))) (Kᵀ * K)

private lemma intertwine_pow_aux {m n : ℕ} (K : Mat m n) (k : ℕ) :
    K * (Kᵀ * K) ^ k = (K * Kᵀ) ^ k * K := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, ← Matrix.mul_assoc K, ih]
    simp only [Matrix.mul_assoc]

private lemma intertwine_aeval_aux {m n : ℕ} (K : Mat m n) (q : Polynomial ℝ) :
    K * Polynomial.aeval (Kᵀ * K) q = Polynomial.aeval (K * Kᵀ) q * K := by
  induction q using Polynomial.induction_on with
  | C a =>
    rw [Polynomial.aeval_C, Polynomial.aeval_C]
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]
  | add p q hp hq => rw [map_add, map_add, Matrix.mul_add, Matrix.add_mul, hp, hq]
  | monomial k a ih =>
    simp only [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X]
    have hc : K * algebraMap ℝ (Mat n n) a = algebraMap ℝ (Mat m m) a * K := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul]
    rw [← Matrix.mul_assoc, hc, Matrix.mul_assoc, intertwine_pow_aux K (k + 1)]
    simp only [Matrix.mul_assoc]

/-- Intertwining `K f(KᵀK) = f(KKᵀ) K` for every real function `f` (the identity that makes
`Q_ϱ(K) = K φ_ϱ(KᵀK)` equal `(KKᵀ+ϱ)^{-1/2} K`; `section.tex` l.273–275, "the sum does not
depend on the choice of decomposition"). Holds for all `f` because both spectra are finite
(`Matrix.finite_real_spectrum`), so the functional calculus reduces to a polynomial
interpolant on the union of the two spectra. -/
theorem cfc_mul_transpose_mul_intertwine {m n : ℕ} (f : ℝ → ℝ) (K : Mat m n) :
    K * cfc f (Kᵀ * K) = cfc f (K * Kᵀ) * K := by
  classical
  have hA : (spectrum ℝ (Kᵀ * K)).Finite := Matrix.finite_real_spectrum
  have hB : (spectrum ℝ (K * Kᵀ)).Finite := Matrix.finite_real_spectrum
  have hsaA : IsSelfAdjoint (Kᵀ * K) := by
    have h := Matrix.isHermitian_conjTranspose_mul_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hsaB : IsSelfAdjoint (K * Kᵀ) := by
    have h := Matrix.isHermitian_mul_conjTranspose_self K
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  set s : Finset ℝ := (hA.union hB).toFinset with hs
  have hinj : Set.InjOn (id : ℝ → ℝ) (s : Set ℝ) := Set.injOn_id _
  set p : Polynomial ℝ := Lagrange.interpolate s id f with hp
  have hAp : ∀ x ∈ spectrum ℝ (Kᵀ * K), f x = p.eval x := by
    intro x hx
    have hxs : x ∈ s := by simp [hs, hx]
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (r := f) hinj hxs
    simpa [hp] using this.symm
  have hBp : ∀ x ∈ spectrum ℝ (K * Kᵀ), f x = p.eval x := by
    intro x hx
    have hxs : x ∈ s := by simp [hs, hx]
    have := Lagrange.eval_interpolate_at_node (s := s) (v := id) (r := f) hinj hxs
    simpa [hp] using this.symm
  rw [cfc_congr' hAp, cfc_congr' hBp, cfc_polynomial p (Kᵀ * K) hsaA,
    cfc_polynomial p (K * Kᵀ) hsaB]
  exact intertwine_aeval_aux K p

/-- For `ϱ > 0`, `Q_ϱ(K) = (KKᵀ + ϱ I)^{-1/2} K` (`eqn:app-setup-Q`, right-hand form, l.262–273).
Source: `section.tex` l.262–273, the displayed identity "`=(KKᵀ+ϱ Id)^{-1/2}K` (ϱ>0)". -/
theorem Q_eq_inv_sqrt_mul {m n : ℕ} {ϱ : ℝ} (hϱ : 0 < ϱ) (K : Mat m n) :
    Q ϱ K = (CFC.sqrt (K * Kᵀ + ϱ • (1 : Mat m m)))⁻¹ * K := by
  have hB0 : 0 ≤ K * Kᵀ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self Kᵀ
  have hC0 : 0 ≤ K * Kᵀ + ϱ • (1 : Mat m m) :=
    add_nonneg hB0 (smul_nonneg hϱ.le zero_le_one)
  have hsq : CFC.sqrt (K * Kᵀ + ϱ • (1 : Mat m m))
      = cfc (fun x : ℝ => Real.sqrt (x + ϱ)) (K * Kᵀ) := by
    rw [CFC.sqrt_eq_real_sqrt _ hC0, cfcₙ_eq_cfc]
    rw [show (fun x : ℝ => Real.sqrt (x + ϱ)) = Real.sqrt ∘ (fun x : ℝ => x + ϱ) from rfl,
      cfc_comp Real.sqrt (fun x : ℝ => x + ϱ) (K * Kᵀ)]
    congr 1
    rw [cfc_add_const ϱ (fun x : ℝ => x) (K * Kᵀ), cfc_id' ℝ (K * Kᵀ),
      Algebra.algebraMap_eq_smul_one]
  have hinv : ∀ x ∈ spectrum ℝ (K * Kᵀ), 0 ≤ x := fun x hx =>
    spectrum_nonneg_of_nonneg hB0 hx
  unfold Q
  rw [cfc_mul_transpose_mul_intertwine, hsq]
  congr 1
  have hpos_sqrt : ∀ x ∈ spectrum ℝ (K * Kᵀ), Real.sqrt (x + ϱ) ≠ 0 := fun x hx =>
    (Real.sqrt_pos.mpr (by linarith [hinv x hx])).ne'
  rw [Matrix.nonsing_inv_eq_ringInverse,
    ← cfc_inv (fun x : ℝ => Real.sqrt (x + ϱ)) (K * Kᵀ) hpos_sqrt (by cfc_cont_tac) (by cfc_tac)]
  refine cfc_congr fun x hx => ?_
  have hx0 := hinv x hx
  have hpos : 0 < x + ϱ := by linarith
  rw [Real.rpow_neg hpos.le, Real.sqrt_eq_rpow]

/-! ## EMA weights and power sums -/

/-- EMA weights `w_j = (1-β) β^j` (`eqn:app-setup-unrolled` and `eqn:app-setup-weights`,
`section.tex` l.444–455). Convention `β^0 = 1` at `β = 0` is `pow_zero`. -/
def emaW (β : ℝ) (j : ℕ) : ℝ := (1 - β) * β ^ j

/-- Power sums `S_p(β) = ∑_{j ≥ 0} w_j^p` (`eqn:app-setup-weights`, `section.tex` l.451–455).
Written `\sw{p}` in the paper; the paper's `\sw{1}` is not exported. -/
def sPow (β : ℝ) (p : ℕ) : ℝ := ∑' j : ℕ, emaW β j ^ p

/-- `∑_{j ≥ 0} (1-β) β^j = 1` for `0 ≤ β < 1` (`eqn:app-setup-weights`, first identity,
`section.tex` l.451–455). -/
theorem tsum_emaW {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) : ∑' j : ℕ, emaW β j = 1 := by
  have hpos : (0 : ℝ) < 1 - β := by linarith
  unfold emaW
  rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]
  exact mul_inv_cancel₀ hpos.ne'

/-- Closed form `S_p(β) = (1-β)^p / (1-β^p)` for `p ≥ 2` and `0 ≤ β < 1`
(`eqn:app-setup-weights`, second identity, `section.tex` l.451–455; the paper states it for
`p ≥ 2`). -/
theorem sPow_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {p : ℕ} (hp : 2 ≤ p) :
    sPow β p = (1 - β) ^ p / (1 - β ^ p) := by
  have hpow : β ^ p < 1 := pow_lt_one₀ hβ0 hβ1 (by omega)
  have key : ∀ j : ℕ, emaW β j ^ p = (1 - β) ^ p * (β ^ p) ^ j := by
    intro j
    unfold emaW
    rw [mul_pow, pow_right_comm β j p]
  unfold sPow
  simp only [key]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (pow_nonneg hβ0 p) hpow, div_eq_mul_inv]

/-- `S_2(β) = (1-β)/(1+β)` for `0 ≤ β < 1` (`eqn:app-setup-weights`, third identity,
`section.tex` l.451–455). -/
theorem sPow_two {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    sPow β 2 = (1 - β) / (1 + β) := by
  have hq : (0 : ℝ) < 1 - β := by linarith
  have hr : (0 : ℝ) < 1 + β := by linarith
  have hden : (1 : ℝ) - β ^ 2 = (1 - β) * (1 + β) := by ring
  rw [sPow_eq hβ0 hβ1 (p := 2) le_rfl, hden, div_eq_div_iff (mul_pos hq hr).ne' hr.ne']
  ring

/-! ## Covariances and spectral measures -/

/-- The pair of input and output covariances, with their PSD proofs
(`def:app-setup-model`, `section.tex` l.47–56: `Σ_out = E[X_out ⊗ X_out]`,
`Σ_in = E[X_in ⊗ X_in]`). `Sout` is `m × m` (output), `Sin` is `n × n` (input). -/
structure Covariances (m n : ℕ) where
  /-- Output covariance `Σ_out` (`def:app-setup-model`, l.47–56). -/
  Sout : Matrix (Fin m) (Fin m) ℝ
  /-- Input covariance `Σ_in` (`def:app-setup-model`, l.47–56). -/
  Sin : Matrix (Fin n) (Fin n) ℝ
  psdOut : Sout.PosSemidef
  psdIn : Sin.PosSemidef

/-- Output spectral measure `ν_out = (1/B) ∑_{i=1}^{N_out} δ_{μ_i}`
(`eqn:app-setup-spectral-measures`, `section.tex` l.1062–1067). Basis-free: the eigenvalues
are those of `Sout` as a multiset.
`B` is required to be positive where the mass normalization matters (`B = 0` gives `⊤`). -/
def nuOut {m n : ℕ} (C : Covariances m n) (B : ℕ) : Measure ℝ :=
  (B : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (C.psdOut.isHermitian.eigenvalues i)

/-- Input spectral measure `ν_in = (1/B) ∑_{k=1}^{N_in} δ_{λ_k}` (`eqn:app-setup-spectral-measures`,
`section.tex` l.1062–1067). Basis-free, as `nuOut`. -/
def nuIn {m n : ℕ} (C : Covariances m n) (B : ℕ) : Measure ℝ :=
  (B : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (C.psdIn.isHermitian.eigenvalues k)

private lemma trace_cfc_herm_eig_aux {n : ℕ} (A : Mat n n) (hA : A.IsHermitian) (φ : ℝ → ℝ) :
    (cfc φ A).trace = ∑ i : Fin n, φ (hA.eigenvalues i) := by
  rw [hA.cfc_eq φ, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply, Matrix.trace_mul_comm,
    ← mul_assoc, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id]

/-- Trace-integral identity `(1/B) Tr φ(Σ_out) = ∫ φ dν_out` for every `φ`
(`eqn:app-setup-spectral-measures`, the sentence "so that `(1/B) Tr φ(Σ) = ∫ φ dν`",
`section.tex` l.1062–1067). Stated for every real `φ`: the spectrum of `Σ_out` is finite, so
`cfc φ Σ_out` only sees `φ` on the eigenvalues. -/
theorem trace_cfc_eq_integral_nuOut {m n : ℕ} (C : Covariances m n) {B : ℕ} (hB : 0 < B)
    (φ : ℝ → ℝ) :
    (B : ℝ)⁻¹ * (cfc φ C.Sout).trace =
      ∫ x, φ x ∂(nuOut C B) := by
  rw [trace_cfc_herm_eig_aux _ C.psdOut.isHermitian φ]
  unfold nuOut
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac (by simp)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [integral_dirac, smul_eq_mul]

/-- Input-side trace-integral identity `(1/B) Tr φ(Σ_in) = ∫ φ dν_in`
(`eqn:app-setup-spectral-measures`, "likewise for `Σ_in`", `section.tex` l.1062–1067). -/
theorem trace_cfc_eq_integral_nuIn {m n : ℕ} (C : Covariances m n) {B : ℕ} (hB : 0 < B)
    (φ : ℝ → ℝ) :
    (B : ℝ)⁻¹ * (cfc φ C.Sin).trace = ∫ x, φ x ∂(nuIn C B) := by
  rw [trace_cfc_herm_eig_aux _ C.psdIn.isHermitian φ]
  unfold nuIn
  rw [integral_smul_measure, integral_finsetSum_measure (fun i _ => integrable_dirac (by simp)),
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  simp only [integral_dirac, smul_eq_mul]

/-! ## Proportional regime -/

/-- Proportional regime (`assum:proportional-regime`, `section.tex` l.1073–1087). The sequence
of dimensions `(m k, n k, B k)` is indexed by `k : ℕ`; `B k → ∞`, the aspect ratios
`n k / B k → γ_in ∈ (0,∞)` and `m k / B k → γ_out ∈ (0,∞)`, and the covariance operator norms
are bounded by one constant `c > 0` uniformly in `k`. The limits `γ_in`, `γ_out` are data
fields because downstream statements name them. -/
structure ProportionalRegime (m n B : ℕ → ℕ) (C : ∀ k : ℕ, Covariances (m k) (n k)) where
  /-- Input limiting aspect ratio `γ_in = lim N_in / B`. -/
  γin : ℝ
  /-- Output limiting aspect ratio `γ_out = lim N_out / B`. -/
  γout : ℝ
  γin_pos : 0 < γin
  γout_pos : 0 < γout
  B_top : Tendsto B atTop atTop
  ratio_in : Tendsto (fun k : ℕ => (n k : ℝ) / (B k : ℝ)) atTop (𝓝 γin)
  ratio_out : Tendsto (fun k : ℕ => (m k : ℝ) / (B k : ℝ)) atTop (𝓝 γout)
  bdd : ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, opNorm (C k).Sin ≤ c ∧ opNorm (C k).Sout ≤ c

/-! ## Deterministic equivalents -/

/-- `M(z)` has deterministic equivalent `Mbar(z)` in the proportional regime
(`def:deterministic-equivalent`, `section.tex` l.1115–1125): for every `z ∈ Z`, every family of
deterministic test matrices `T` with `‖T k‖` bounded uniformly in `k`, and every `ε > 0`,
the probability that `|N_k⁻¹ Tr[(M_k(z) − Mbar_k(z)) T_k]| ≥ ε` tends to `0`.
`Ω k` carries the probability measure `P k`; the normalizer `N k` is the dimension named by
context; `T k` is rectangular and complex as in the paper's `ℂ`-valued spectral parameter. -/
def IsDetEquiv {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k : ℕ, Measure (Ω k))
    (N : ℕ → ℕ) {d₁ d₂ : ℕ → ℕ} (Z : Set ℂ)
    (M : ∀ k : ℕ, ℂ → Ω k → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ)
    (Mbar : ∀ k : ℕ, ℂ → Matrix (Fin (d₁ k)) (Fin (d₂ k)) ℂ) : Prop :=
  ∀ z ∈ Z, ∀ T : ∀ k : ℕ, Matrix (Fin (d₂ k)) (Fin (d₁ k)) ℂ,
    (∃ c : ℝ, ∀ k : ℕ, opNorm (T k) ≤ c) →
    ∀ ε > 0, Tendsto
      (fun k : ℕ => P k {ω | ε ≤ ‖(N k : ℂ)⁻¹ * ((M k z ω - Mbar k z) * T k).trace‖})
      atTop (𝓝 0)

/-- `a ≃ b` in the sense of `def:deterministic-equivalent` and `section.tex` l.1135–1140:
`a = b + o_P(1)`, i.e. for every `ε > 0`, `P(|a_k − b_k| ≥ ε) → 0`. Scalars may be real or
complex (`E` any normed group). -/
def PEq {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)] {E : Type*} [NormedAddCommGroup E]
    (P : ∀ k : ℕ, Measure (Ω k)) (a : ∀ k : ℕ, Ω k → E) (b : ℕ → E) : Prop :=
  ∀ ε > 0, Tendsto (fun k : ℕ => P k {ω | ε ≤ ‖a k ω - b k‖}) atTop (𝓝 0)

end Muon

end
