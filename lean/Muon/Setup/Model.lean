import Muon.Foundations.Conventions
import Muon.Foundations.Gaussian
import Muon.Setup.Basic

/-!
# Appendix A: regression model, data-target normalization, moments and normalization

Work package L-A.4 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/01-setup/section.tex`: `def:app-setup-model` l.47–91, `assum:data-target` l.99–107,
`prop:app-setup-moments` l.109–131, `eqn:app-setup-whitened` l.201–205,
`eqn:app-setup-normalized` l.209–215, `prop:app-setup-normalization` l.217–233.

Shared objects are reused, not redefined: `Muon.Mat`, `Muon.Vec`, `Muon.Covariances`,
`Muon.outer`, `Muon.mean`, `Muon.fro` (`Muon.Foundations.Conventions`) and
`Muon.Foundations.stdGaussianPi` (`Muon.Foundations.Gaussian`). Every theorem below has proof
`sorry`; proof routes are in `results/L-A.4-interface.json`.
-/

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory

noncomputable section

namespace Muon.Setup

open Muon

/-! ## Batches, residuals and risks -/

/-- Minibatch of `B` feature pairs `(x_out, x_in)`. The paper writes `(x_in, x_out)`;
Lean uses `(out, in)` throughout this file. -/
abbrev Batch (m n B : ℕ) := Fin B → Vec m × Vec n

/-- Bilinear residual `d = X_outᵀ Δ X_in` of one sample (`eqn:app-setup-gradient`). -/
def resid {m n : ℕ} (Δ : Mat m n) (x : Vec m × Vec n) : ℝ :=
  dotProduct x.1 (Matrix.mulVec Δ x.2)

/-- Single-sample loss `L(W; X) = ½ ⟨X_out ⊗ X_in, W − W⋆⟩²` (`eqn:app-setup-risk`). -/
def lossSingle {m n : ℕ} (Wstar W : Mat m n) (x : Vec m × Vec n) : ℝ :=
  (1 / 2 : ℝ) * (resid (W - Wstar) x) ^ 2

/-- Population risk `𝓡(W) = E L(W; X)` (`eqn:app-setup-risk`, expectation form). -/
def popRisk {m n : ℕ} (ν : Measure (Vec m × Vec n)) (Wstar W : Mat m n) : ℝ :=
  ∫ x, lossSingle Wstar W x ∂ν

/-- Minibatch gradient `G° = (1/B) ∑_a d_a° X_out^{(a)} ⊗ X_in^{(a)}` (`eqn:app-setup-gradient`). -/
def grad {m n B : ℕ} (Δ : Mat m n) (b : Batch m n B) : Mat m n :=
  ((B : ℝ))⁻¹ • ∑ a, resid Δ (b a) • outer (b a).1 (b a).2

/-! ## Feature laws and the sampling model -/

/-- Feature law (`def:app-setup-model`): `ν` is a probability law on `(X_out, X_in)` with
independent components, square-integrable and centred coordinates, and second-moment matrices
`Σ_out`, `Σ_in` from `C`. Only second moments are assumed, as in the paper. -/
structure IsFeatureLaw {m n : ℕ} (C : Covariances m n) (ν : Measure (Vec m × Vec n)) : Prop where
  isProb : IsProbabilityMeasure ν
  indep : ν = ν.fst.prod ν.snd
  memLp_out : ∀ i : Fin m, MemLp (fun x : Vec m × Vec n => x.1 i) 2 ν
  memLp_in : ∀ j : Fin n, MemLp (fun x : Vec m × Vec n => x.2 j) 2 ν
  centered_out : ∀ i : Fin m, ∫ x, x.1 i ∂ν = 0
  centered_in : ∀ j : Fin n, ∫ x, x.2 j ∂ν = 0
  second_out : ∀ i k : Fin m, ∫ x, x.1 i * x.1 k ∂ν = C.Sout i k
  second_in : ∀ j l : Fin n, ∫ x, x.2 j * x.2 l ∂ν = C.Sin j l

/-- Filtered sampling model (`def:app-setup-model`, l.72–75, resolved as in §6.4 of the card).
`x t` is the minibatch of step `t`: it is `ℱ (t+1)`-measurable, has the law `ν^{⊗B}`, and is
independent of the past `ℱ t`. -/
structure ModelLaw {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {m n : ℕ} (ν : Measure (Vec m × Vec n)) [IsProbabilityMeasure ν] (B : ℕ) where
  x : ℕ → Ω → Batch m n B
  ℱ : Filtration ℕ mΩ
  x_meas : ∀ t, Measurable[ℱ (t + 1)] (x t)
  x_law : ∀ t, P.map (x t) = Measure.pi fun _ : Fin B => ν
  x_indep : ∀ t, Indep (MeasurableSpace.comap (x t) inferInstance) (ℱ t) P

/-- `B` independent copies of `ν` on one probability space (the fresh batch of a fixed step). -/
structure IIDBatch {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {m n B : ℕ}
    (ν : Measure (Vec m × Vec n)) (x : Fin B → Ω → Vec m × Vec n) : Prop where
  meas : ∀ a, AEMeasurable (x a) P
  law : ∀ a, P.map (x a) = ν
  indep : iIndepFun x P

/-- The model of `def:app-setup-model` (snapshot `cr-2026-10-23`) as a Prop: the eigenbases and eigenvalues of `Σ_out` and
`Σ_in` are the `SpectralData` argument (`Muon.Setup.SpectralData`, from `Basic`, which carries
the orthonormality and eigen-equations), and `ν` is the feature law `IsFeatureLaw`. The filtration
is `ModelLaw`. -/
def def_app_setup_model {m n : ℕ} {C : Covariances m n} (_S : SpectralData C)
    (ν : Measure (Vec m × Vec n)) : Prop :=
  IsFeatureLaw C ν

/-! ## Whitened representation and the normalized objects -/

/-- Whitened-to-physical map `(z, w) ↦ (Σ_out^{1/2} z, Σ_in^{1/2} w)` (`assum:data-target`). -/
def phys {m n : ℕ} (C : Covariances m n) (zw : Vec m × Vec n) : Vec m × Vec n :=
  (Matrix.mulVec (rOut C) zw.1, Matrix.mulVec (rIn C) zw.2)

/-- Law of the Gaussian data target: image of `N(0, I_m) ⊗ N(0, I_n)` under `phys C`. -/
def dataTarget {m n : ℕ} (C : Covariances m n) : Measure (Vec m × Vec n) :=
  ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)).map (phys C)

/-- `assum:data-target`: the features are the image of whitened Gaussian samples
`(z, w) ↦ (Σ_out^{1/2} z, Σ_in^{1/2} w)`. Encoded as a law identity (see `dataTarget`). -/
def assum_data_target {m n : ℕ} (C : Covariances m n) (ν : Measure (Vec m × Vec n)) : Prop :=
  ν = dataTarget C

/-- Normalized residual `d_a = d_a° / √(2𝓡(t))` (`eqn:app-setup-normalized`, snapshot `cr-2026-10-23`). -/
def dNorm {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) (z : Vec m × Vec n) : ℝ :=
  resid Δ z / Real.sqrt (2 * riskSigma C Δ)

/-- Normalized gradient `G_t = G_t° / √(2𝓡(t))` (`eqn:app-setup-normalized`, snapshot `cr-2026-10-23`). -/
def Gnorm {m n B : ℕ} (C : Covariances m n) (Δ : Mat m n) (b : Batch m n B) : Mat m n :=
  (Real.sqrt (2 * riskSigma C Δ))⁻¹ • grad Δ b

/-! ## Private helpers for the whitened identities -/

private lemma rOut_transpose {m n : ℕ} (C : Covariances m n) : (rOut C)ᵀ = rOut C := by
  have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma rIn_transpose {m n : ℕ} (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma dot_symm_mulVec {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : Sᵀ = S)
    (x y : Fin k → ℝ) :
    (S *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (S *ᵥ y) := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, hS]

private lemma outer_phys_eq {m n : ℕ} (C : Covariances m n) (zw : Vec m × Vec n) :
    outer (phys C zw).1 (phys C zw).2 = rOut C * outer zw.1 zw.2 * rIn C := by
  have hI := rIn_transpose C
  change Matrix.vecMulVec (rOut C *ᵥ zw.1) (rIn C *ᵥ zw.2)
    = rOut C * Matrix.vecMulVec zw.1 zw.2 * rIn C
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, ← Matrix.mulVec_transpose, hI]

/-! ## Proof helpers (private) for the moment and data-target statements -/

private lemma std_coord_memLp (k : ℕ) (i : Fin k) :
    MemLp (fun z : Fin k → ℝ => z i) 2 (Muon.Foundations.stdGaussianPi k) := by
  have h : MemLp (fun x : ℝ => x) 2
      ((Muon.Foundations.stdGaussianPi k).map (fun z : Fin k → ℝ => z i)) := by
    rw [Muon.Foundations.stdGaussianPi_map_coord]
    simpa using Muon.Foundations.gaussian_memLp_pow 1 2 (by norm_num)
  exact (memLp_map_measure_iff aestronglyMeasurable_id
    (measurable_pi_apply i).aemeasurable).mp h

private lemma integral_std_coord (k : ℕ) (i : Fin k) :
    ∫ z, z i ∂(Muon.Foundations.stdGaussianPi k) = 0 := by
  have h := integral_map (μ := Muon.Foundations.stdGaussianPi k)
    (φ := fun z : Fin k → ℝ => z i) (f := fun x : ℝ => x)
    (measurable_pi_apply i).aemeasurable aestronglyMeasurable_id
  simp only [Muon.Foundations.stdGaussianPi_map_coord, integral_id_gaussianReal] at h
  exact h.symm

private lemma memLp_mulVec_apply {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) :
    MemLp (fun z : Fin k → ℝ => (Matrix.mulVec A z) i) 2 (Muon.Foundations.stdGaussianPi k) := by
  have e : (fun z : Fin k → ℝ => (Matrix.mulVec A z) i)
      = ∑ j : Fin k, (fun z : Fin k → ℝ => A i j * z j) := by
    funext z
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [e]
  exact memLp_finsetSum' _ fun j _ => (std_coord_memLp k j).const_mul (A i j)

private lemma integral_mulVec_apply {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) :
    ∫ z, (Matrix.mulVec A z) i ∂(Muon.Foundations.stdGaussianPi k) = 0 := by
  have e : (fun z : Fin k → ℝ => (Matrix.mulVec A z) i)
      = fun z => ∑ j : Fin k, A i j * z j := by
    funext z
    simp [Matrix.mulVec, dotProduct]
  rw [e, integral_finset_sum _ (fun j _ => ((std_coord_memLp k j).integrable one_le_two).const_mul (A i j))]
  exact Finset.sum_eq_zero fun j _ => by rw [integral_const_mul, integral_std_coord, mul_zero]

private lemma gauss_mulVec_second {m k : ℕ} (R : Matrix (Fin m) (Fin k) ℝ) (i j : Fin m) :
    ∫ z, (Matrix.mulVec R z) i * (Matrix.mulVec R z) j ∂(Muon.Foundations.stdGaussianPi k)
      = (R * Rᵀ) i j := by
  have e : (fun z : Fin k → ℝ => (Matrix.mulVec R z) i * (Matrix.mulVec R z) j)
      = fun z => ∑ a : Fin k, ∑ b : Fin k,
          z a * (Matrix.of fun a b => R i a * R j b) a b * z b := by
    funext z
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e, Muon.Foundations.stdGaussianPi_quadratic_mean k (Matrix.of fun a b => R i a * R j b)]
  simp [Matrix.trace, Matrix.mul_apply]

private lemma memLp_map_coord {m k : ℕ} (A : Matrix (Fin m) (Fin k) ℝ) (i : Fin m) :
    MemLp (fun y : Vec m => y i) 2 ((Muon.Foundations.stdGaussianPi k).map (Matrix.mulVec A)) :=
  (memLp_map_measure_iff (measurable_pi_apply i).aestronglyMeasurable
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable.aemeasurable).mpr
    (memLp_mulVec_apply A i)

private lemma memLp_fst_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure ν] {h : α → ℝ} {p : ENNReal}
    (hh : MemLp h p μ) : MemLp (fun x : α × β => h x.1) p (μ.prod ν) := by
  have hmap : (μ.prod ν).map Prod.fst = μ := by simp
  have h2 : MemLp h p ((μ.prod ν).map Prod.fst) := by rw [hmap]; exact hh
  exact (memLp_map_measure_iff (by rw [hmap]; exact hh.aestronglyMeasurable)
    measurable_fst.aemeasurable).mp h2

private lemma memLp_snd_prod {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) [IsProbabilityMeasure μ] (ν : Measure β) [IsFiniteMeasure ν]
    {h : β → ℝ} {p : ENNReal}
    (hh : MemLp h p ν) : MemLp (fun x : α × β => h x.2) p (μ.prod ν) := by
  have hmap : (μ.prod ν).map Prod.snd = ν := by
    rw [Measure.map_snd_prod, measure_univ, one_smul]
  have h2 : MemLp h p ((μ.prod ν).map Prod.snd) := by rw [hmap]; exact hh
  exact (memLp_map_measure_iff (by rw [hmap]; exact hh.aestronglyMeasurable)
    measurable_snd.aemeasurable).mp h2

private lemma sep_integral {m n : ℕ} {ν : Measure (Vec m × Vec n)} [IsFiniteMeasure ν]
    (hν : ν = ν.fst.prod ν.snd) (F : Vec m → ℝ) (G : Vec n → ℝ)
    (hF : Measurable F) (hG : Measurable G) :
    ∫ x, F x.1 * G x.2 ∂ν = (∫ x, F x.1 ∂ν) * ∫ x, G x.2 ∂ν := by
  have h := integral_prod_mul (μ := ν.fst) (ν := ν.snd) F G
  rw [← hν] at h
  rw [h]
  congr 1
  · exact integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable
  · exact integral_map measurable_snd.aemeasurable hG.aestronglyMeasurable

private lemma integrable_sep {m n : ℕ} {ν : Measure (Vec m × Vec n)} [IsFiniteMeasure ν]
    (hν : ν = ν.fst.prod ν.snd) (F : Vec m → ℝ) (G : Vec n → ℝ)
    (hF : Measurable F) (hG : Measurable G)
    (hFi : Integrable (fun x : Vec m × Vec n => F x.1) ν)
    (hGi : Integrable (fun x : Vec m × Vec n => G x.2) ν) :
    Integrable (fun x : Vec m × Vec n => F x.1 * G x.2) ν := by
  have hF' : Integrable F ν.fst :=
    (integrable_map_measure hF.aestronglyMeasurable measurable_fst.aemeasurable).mpr hFi
  have hG' : Integrable G ν.snd :=
    (integrable_map_measure hG.aestronglyMeasurable measurable_snd.aemeasurable).mpr hGi
  have h := Integrable.mul_prod (μ := ν.fst) (ν := ν.snd) hF' hG'
  rw [← hν] at h
  exact h

private lemma resid_eq_sum {m n : ℕ} (Δ : Mat m n) (x : Vec m × Vec n) :
    resid Δ x = ∑ i, ∑ j, x.1 i * (Δ i j * x.2 j) := by
  simp only [resid, dotProduct, Matrix.mulVec, Finset.mul_sum]

private lemma resid_measurable {m n : ℕ} (Δ : Mat m n) :
    Measurable (fun x : Vec m × Vec n => resid Δ x) := by
  simp only [resid_eq_sum]
  fun_prop

private lemma resid_integral_zero {m n : ℕ} {C : Covariances m n}
    {ν : Measure (Vec m × Vec n)} (hν : IsFeatureLaw C ν) (Δ : Mat m n) :
    ∫ x, resid Δ x ∂ν = 0 := by
  haveI := hν.isProb
  have hI : ∀ (i : Fin m) (j : Fin n),
      Integrable (fun x : Vec m × Vec n => x.1 i * (Δ i j * x.2 j)) ν :=
    fun i j => integrable_sep hν.indep (fun y => y i) (fun y => Δ i j * y j)
      (measurable_pi_apply i) ((measurable_pi_apply j).const_mul _)
      ((hν.memLp_out i).integrable one_le_two)
      (((hν.memLp_in j).integrable one_le_two).const_mul _)
  have hc : ∀ (i : Fin m) (j : Fin n), ∫ x : Vec m × Vec n, x.1 i * (Δ i j * x.2 j) ∂ν = 0 := by
    intro i j
    have h := sep_integral hν.indep (fun y => y i) (fun y => Δ i j * y j)
      (measurable_pi_apply i) ((measurable_pi_apply j).const_mul _)
    try dsimp only at h
    rw [h, hν.centered_out i, zero_mul]
  simp only [resid_eq_sum]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun j _ => hI i j))]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => hI i j)]
  exact Finset.sum_eq_zero fun j _ => hc i j

private lemma trace_mul_sym_eq {m : ℕ} (S N : Matrix (Fin m) (Fin m) ℝ) (hN : Nᵀ = N) :
    (S * N).trace = ∑ i, ∑ k, S i k * N i k := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have h := congrFun (congrFun hN k) i
  simp only [Matrix.transpose_apply] at h
  rw [h]

private lemma resid_sq_integral {m n : ℕ} {C : Covariances m n}
    {ν : Measure (Vec m × Vec n)} (hν : IsFeatureLaw C ν) (Δ : Mat m n) :
    Integrable (fun x : Vec m × Vec n => resid Δ x ^ 2) ν ∧
      ∫ x, resid Δ x ^ 2 ∂ν = pairSigma C Δ Δ := by
  haveI := hν.isProb
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hMo : ∀ i k : Fin m, Integrable (fun x : Vec m × Vec n => x.1 i * x.1 k) ν :=
    fun i k => (hν.memLp_out i).integrable_mul (hν.memLp_out k)
  have hMi : ∀ j l : Fin n, Integrable (fun x : Vec m × Vec n => x.2 j * x.2 l) ν :=
    fun j l => (hν.memLp_in j).integrable_mul (hν.memLp_in l)
  have hT : ∀ (i k : Fin m) (j l : Fin n),
      Integrable (fun x : Vec m × Vec n =>
        (x.1 i * x.1 k) * ((Δ i j * Δ k l) * (x.2 j * x.2 l))) ν :=
    fun i k j l => integrable_sep hν.indep (fun y => y i * y k)
      (fun y => (Δ i j * Δ k l) * (y j * y l))
      ((measurable_pi_apply i).mul (measurable_pi_apply k))
      (((measurable_pi_apply j).mul (measurable_pi_apply l)).const_mul _)
      (hMo i k) ((hMi j l).const_mul _)
  have hterm : ∀ (i k : Fin m) (j l : Fin n),
      ∫ x : Vec m × Vec n, (x.1 i * x.1 k) * ((Δ i j * Δ k l) * (x.2 j * x.2 l)) ∂ν
        = C.Sout i k * ((Δ i j * Δ k l) * C.Sin j l) := by
    intro i k j l
    have h := sep_integral hν.indep (fun y => y i * y k)
      (fun y => (Δ i j * Δ k l) * (y j * y l))
      ((measurable_pi_apply i).mul (measurable_pi_apply k))
      (((measurable_pi_apply j).mul (measurable_pi_apply l)).const_mul _)
    try dsimp only at h
    rw [h, hν.second_out i k, integral_const_mul, hν.second_in j l]
  have hexp : ∀ x : Vec m × Vec n, resid Δ x ^ 2 = ∑ i, ∑ k, ∑ j, ∑ l,
      (x.1 i * x.1 k) * ((Δ i j * Δ k l) * (x.2 j * x.2 l)) := by
    intro x
    rw [sq, resid_eq_sum Δ x]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
      Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have hint : Integrable (fun x : Vec m × Vec n => resid Δ x ^ 2) ν := by
    simp only [hexp]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => hT i k j l
  have hquad : ∫ x, resid Δ x ^ 2 ∂ν = ∑ i, ∑ k, ∑ j, ∑ l,
      C.Sout i k * ((Δ i j * Δ k l) * C.Sin j l) := by
    simp only [hexp]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ =>
      integrable_finset_sum _ fun j _ => integrable_finset_sum _ fun l _ => hT i k j l)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun k _ => integrable_finset_sum _ fun j _ =>
      integrable_finset_sum _ fun l _ => hT i k j l)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ fun l _ => hT i k j l)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finset_sum _ (fun l _ => hT i k j l)]
    exact Finset.sum_congr rfl fun l _ => hterm i k j l
  have hSinT : C.Sinᵀ = C.Sin := by
    have h := C.psdIn.isHermitian
    unfold Matrix.IsHermitian at h
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hN : (Δ * C.Sin * Δᵀ)ᵀ = Δ * C.Sin * Δᵀ := by
    simp [Matrix.transpose_mul, hSinT, Matrix.mul_assoc]
  have hpair : pairSigma C Δ Δ = ∑ i, ∑ k, C.Sout i k * (Δ * C.Sin * Δᵀ) i k := by
    unfold pairSigma
    rw [show C.Sout * Δ * C.Sin * Δᵀ = C.Sout * (Δ * C.Sin * Δᵀ) by simp only [Matrix.mul_assoc]]
    exact trace_mul_sym_eq _ _ hN
  have hNent : ∀ i k : Fin m, (Δ * C.Sin * Δᵀ) i k = ∑ j, ∑ l, Δ i j * Δ k l * C.Sin j l := by
    intro i k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨hint, hquad.trans ?_⟩
  rw [hpair]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [hNent, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]


private lemma iid_transfer {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    {ν : Measure (Vec m × Vec n)} [IsProbabilityMeasure ν] {x : Fin B → Ω → Vec m × Vec n}
    (hx : IIDBatch P ν x) (a : Fin B) (hae : AEMeasurable (x a) P) (g : Vec m × Vec n → ℝ)
    (hg : Measurable g) :
    (Integrable (fun ω => g (x a ω)) P ↔ Integrable g ν) ∧
      ∫ ω, g (x a ω) ∂P = ∫ z, g z ∂ν := by
  have hmap := hx.law a
  refine ⟨?_, ?_⟩
  · have h1 := integrable_map_measure hg.aestronglyMeasurable hae
    rw [hmap] at h1
    exact h1.symm
  · have h2 := integral_map hae hg.aestronglyMeasurable
    rw [hmap] at h2
    exact h2.symm

private lemma resid_moment {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (Δ : Mat m n) (i : Fin m) (k : Fin n) :
    Integrable (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k)) ν ∧
      ∫ z, resid Δ z * (z.1 i * z.2 k) ∂ν = (C.Sout * Δ * C.Sin) i k := by
  haveI := hν.isProb
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hexp : ∀ z : Vec m × Vec n, resid Δ z * (z.1 i * z.2 k) = ∑ p : Fin m, ∑ q : Fin n,
      (z.1 i * z.1 p) * (Δ p q * (z.2 q * z.2 k)) := by
    intro z
    rw [resid_eq_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have hfun : (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k))
      = fun z => ∑ p : Fin m, ∑ q : Fin n, (z.1 i * z.1 p) * (Δ p q * (z.2 q * z.2 k)) :=
    funext hexp
  have hI : ∀ (p : Fin m) (q : Fin n),
      Integrable (fun z : Vec m × Vec n => (z.1 i * z.1 p) * (Δ p q * (z.2 q * z.2 k))) ν :=
    fun p q => integrable_sep hν.indep (fun y => y i * y p) (fun y => Δ p q * (y q * y k))
      ((measurable_pi_apply i).mul (measurable_pi_apply p))
      (((measurable_pi_apply q).mul (measurable_pi_apply k)).const_mul _)
      ((hν.memLp_out i).integrable_mul (hν.memLp_out p))
      (((hν.memLp_in q).integrable_mul (hν.memLp_in k)).const_mul _)
  have hsep : ∀ (p : Fin m) (q : Fin n),
      ∫ z, (z.1 i * z.1 p) * (Δ p q * (z.2 q * z.2 k)) ∂ν = C.Sout i p * (Δ p q * C.Sin q k) := by
    intro p q
    have h := sep_integral hν.indep (fun y => y i * y p) (fun y => Δ p q * (y q * y k))
      ((measurable_pi_apply i).mul (measurable_pi_apply p))
      (((measurable_pi_apply q).mul (measurable_pi_apply k)).const_mul _)
    try dsimp only at h
    rw [h, hν.second_out i p, integral_const_mul, hν.second_in q k]
  have hint : Integrable (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k)) ν := by
    rw [hfun]
    exact integrable_finset_sum _ fun p _ => integrable_finset_sum _ fun q _ => hI p q
  refine ⟨hint, ?_⟩
  have hsum : ∑ p : Fin m, ∫ z, ∑ q : Fin n, (z.1 i * z.1 p) * (Δ p q * (z.2 q * z.2 k)) ∂ν
      = ∑ p : Fin m, ∑ q : Fin n, C.Sout i p * (Δ p q * C.Sin q k) :=
    Finset.sum_congr rfl fun p _ => by
      rw [integral_finset_sum _ (fun q _ => hI p q)]
      exact Finset.sum_congr rfl fun q _ => hsep p q
  rw [hfun, integral_finset_sum _ (fun p _ => integrable_finset_sum _ fun q _ => hI p q), hsum]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun q _ =>
    Finset.sum_congr rfl fun p _ => by ring)

/-! ## Statements -/

/-- `prop:app-setup-moments`(i), snapshot `cr-2026-10-23`, verbatim from `section.tex`
l.109–131 (the proposition; part (i) is the first item):

\begin{proposition}[Residual and gradient moments]\label{prop:app-setup-moments}
In \cref{def:app-setup-model}, $\Sigmain$ and $\Sigmaout$ are symmetric
and positive semidefinite, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item For deterministic $\Delta\in\R^{\Nout\times\Nin}$ the residual
$d\defeq\Xout^\T\Delta\Xin$ is centered, and
\begin{equation}\label{eqn:app-setup-risk-trace}
\EE d^2=\Var(d)=\Tr\big(\Sigmaout\Delta\Sigmain\Delta^\T\big)=\norm{\Delta}_\Sigma^2,
\qquad \cR(W)=\tfrac12\norm{W-\Wstar}_\Sigma^2 .
\end{equation}
\item For deterministic $\Delta$ and a batch of $B$ independent copies, the
gradient $G^\circ\defeq\frac1B\sum_ad_a^\circ\,\Xout^{(a)}\tensor\Xin^{(a)}$ satisfies
\begin{equation}\label{eqn:app-setup-gradient-matrix}
G^\circ=\frac1B\,Y\vec D^\circ X^\T,\qquad \EE G^\circ=\Sigmaout\Delta\Sigmain .
\end{equation}
\item For the state $\Dt$ at step $t$ with $\EE\norm{\Dt}_\F^2<\infty$ and
the fresh batch of step $t$, the residuals and the gradient of
\cref{eqn:app-setup-gradient} satisfy
\begin{equation}\label{eqn:app-setup-conditional-moments}
\EE_t\,d_a^\circ=0,\qquad \EE_t\,(d_a^\circ)^2=2\cR(t),\qquad \EE_t\,\Gt^\circ=\Sigmaout\Dt\Sigmain .
\end{equation}
\end{enumerate}
\end{proposition}
-/
theorem prop_app_setup_moments_i {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (Δ : Mat m n) :
    C.Sout.PosSemidef ∧ C.Sin.PosSemidef ∧
    (∫ x, resid Δ x ∂ν = 0) ∧ (∫ x, (resid Δ x) ^ 2 ∂ν = pairSigma C Δ Δ) ∧
    variance (fun x => resid Δ x) ν = pairSigma C Δ Δ ∧
    (∀ Wstar W : Mat m n, popRisk ν Wstar W = riskSigma C (W - Wstar)) := by
  haveI := hν.isProb
  have hL2 : MemLp (fun x => resid Δ x) 2 ν :=
    (memLp_two_iff_integrable_sq (resid_measurable Δ).aestronglyMeasurable).mpr
      (resid_sq_integral hν Δ).1
  refine ⟨C.psdOut, C.psdIn, resid_integral_zero hν Δ, (resid_sq_integral hν Δ).2, ?_, ?_⟩
  · rw [variance_eq_sub hL2]
    simp only [Pi.pow_apply]
    rw [resid_integral_zero hν Δ, (resid_sq_integral hν Δ).2]
    ring
  · intro Wstar W
    unfold popRisk lossSingle
    rw [integral_const_mul, (resid_sq_integral hν (W - Wstar)).2]
    unfold riskSigma
    ring

/-- `prop:app-setup-moments`(ii), snapshot `cr-2026-10-23`, verbatim from `section.tex`
l.109–131 (part (ii) is the second item):

\begin{proposition}[Residual and gradient moments]\label{prop:app-setup-moments}
In \cref{def:app-setup-model}, $\Sigmain$ and $\Sigmaout$ are symmetric
and positive semidefinite, and the following hold.
\begin{enumerate}[label=(\roman*)]
\item For deterministic $\Delta\in\R^{\Nout\times\Nin}$ the residual
$d\defeq\Xout^\T\Delta\Xin$ is centered, and
\begin{equation}\label{eqn:app-setup-risk-trace}
\EE d^2=\Var(d)=\Tr\big(\Sigmaout\Delta\Sigmain\Delta^\T\big)=\norm{\Delta}_\Sigma^2,
\qquad \cR(W)=\tfrac12\norm{W-\Wstar}_\Sigma^2 .
\end{equation}
\item For deterministic $\Delta$ and a batch of $B$ independent copies, the
gradient $G^\circ\defeq\frac1B\sum_ad_a^\circ\,\Xout^{(a)}\tensor\Xin^{(a)}$ satisfies
\begin{equation}\label{eqn:app-setup-gradient-matrix}
G^\circ=\frac1B\,Y\vec D^\circ X^\T,\qquad \EE G^\circ=\Sigmaout\Delta\Sigmain .
\end{equation}
\item For the state $\Dt$ at step $t$ with $\EE\norm{\Dt}_\F^2<\infty$ and
the fresh batch of step $t$, the residuals and the gradient of
\cref{eqn:app-setup-gradient} satisfy
\begin{equation}\label{eqn:app-setup-conditional-moments}
\EE_t\,d_a^\circ=0,\qquad \EE_t\,(d_a^\circ)^2=2\cR(t),\qquad \EE_t\,\Gt^\circ=\Sigmaout\Dt\Sigmain .
\end{equation}
\end{enumerate}
\end{proposition}
-/
theorem prop_app_setup_moments_ii {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) {B : ℕ} (hB : 0 < B) (Δ : Mat m n) (x : Fin B → Ω → Vec m × Vec n)
    (hx : IIDBatch P ν x) :
    (∀ b : Batch m n B, grad Δ b = ((B : ℝ))⁻¹ •
      ((Matrix.of fun (i : Fin m) (a : Fin B) => (b a).1 i) *
        Matrix.diagonal (fun a => resid Δ (b a)) *
        (Matrix.of fun (j : Fin n) (a : Fin B) => (b a).2 j)ᵀ)) ∧
    mean P (fun ω => grad Δ (fun a => x a ω)) = C.Sout * Δ * C.Sin := by
  refine ⟨fun b => ?_, ?_⟩
  · ext i j
    simp only [grad, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, outer,
      smul_eq_mul]
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  · haveI := hν.isProb
    have hae : ∀ a, AEMeasurable (x a) P := hx.meas
    ext i k
    have hg : Measurable (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k)) :=
      (resid_measurable Δ).mul
        (((measurable_pi_apply i).comp measurable_fst).mul
          ((measurable_pi_apply k).comp measurable_snd))
    have hgrad : ∀ ω, grad Δ (fun a => x a ω) i k
        = (B : ℝ)⁻¹ * ∑ a, resid Δ (x a ω) * ((x a ω).1 i * (x a ω).2 k) := by
      intro ω
      simp only [grad, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, outer,
        smul_eq_mul]
    have hint : ∀ a, Integrable (fun ω => resid Δ (x a ω) * ((x a ω).1 i * (x a ω).2 k)) P :=
      fun a => ((iid_transfer hx a (hae a) (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k)) hg).1).mpr
        (resid_moment hν Δ i k).1
    have hval : ∀ a, ∫ ω, resid Δ (x a ω) * ((x a ω).1 i * (x a ω).2 k) ∂P
        = (C.Sout * Δ * C.Sin) i k := fun a =>
      ((iid_transfer hx a (hae a) (fun z : Vec m × Vec n => resid Δ z * (z.1 i * z.2 k)) hg).2).trans
        (resid_moment hν Δ i k).2
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    simp only [mean, Matrix.of_apply]
    simp only [hgrad]
    rw [integral_const_mul, integral_finset_sum _ (fun a _ => hint a)]
    simp only [hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [inv_mul_cancel_left₀ hB0]

private lemma phi_meas {m n : ℕ} (p : Fin m) (q : Fin n) :
    Measurable (fun z : Vec m × Vec n => z.1 p * z.2 q) :=
  ((measurable_pi_apply p).comp measurable_fst).mul ((measurable_pi_apply q).comp measurable_snd)

private lemma phi_integrable {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (p : Fin m) (q : Fin n) :
    Integrable (fun z : Vec m × Vec n => z.1 p * z.2 q) ν := by
  haveI := hν.isProb
  exact integrable_sep hν.indep (fun y => y p) (fun y => y q) (measurable_pi_apply p)
    (measurable_pi_apply q) ((hν.memLp_out p).integrable one_le_two)
    ((hν.memLp_in q).integrable one_le_two)

private lemma phi_integral_zero {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (p : Fin m) (q : Fin n) :
    ∫ z, z.1 p * z.2 q ∂ν = 0 := by
  haveI := hν.isProb
  have h := sep_integral hν.indep (fun y => y p) (fun y => y q) (measurable_pi_apply p)
    (measurable_pi_apply q)
  try dsimp only at h
  rw [h, hν.centered_out p, zero_mul]

private lemma phi_phi_integral {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (p r : Fin m) (q s : Fin n) :
    Integrable (fun z : Vec m × Vec n => z.1 p * z.2 q * (z.1 r * z.2 s)) ν ∧
      ∫ z, z.1 p * z.2 q * (z.1 r * z.2 s) ∂ν = C.Sout p r * C.Sin q s := by
  haveI := hν.isProb
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hF : Integrable (fun z : Vec m × Vec n => z.1 p * z.1 r) ν :=
    (hν.memLp_out p).integrable_mul (hν.memLp_out r)
  have hG : Integrable (fun z : Vec m × Vec n => z.2 q * z.2 s) ν :=
    (hν.memLp_in q).integrable_mul (hν.memLp_in s)
  have hint := integrable_sep hν.indep (fun y => y p * y r) (fun y => y q * y s)
    ((measurable_pi_apply p).mul (measurable_pi_apply r))
    ((measurable_pi_apply q).mul (measurable_pi_apply s)) hF hG
  have hsep := sep_integral hν.indep (fun y => y p * y r) (fun y => y q * y s)
    ((measurable_pi_apply p).mul (measurable_pi_apply r))
    ((measurable_pi_apply q).mul (measurable_pi_apply s))
  have heq : (fun z : Vec m × Vec n => z.1 p * z.2 q * (z.1 r * z.2 s))
      = fun z => (z.1 p * z.1 r) * (z.2 q * z.2 s) := funext fun z => by ring
  rw [heq]
  refine ⟨hint, ?_⟩
  try dsimp only at hsep
  rw [hsep, hν.second_out p r, hν.second_in q s]

private lemma resid_expand {m n : ℕ} (D : Mat m n) (z : Vec m × Vec n) :
    resid D z = ∑ k : Fin m × Fin n, D k.1 k.2 * (z.1 k.1 * z.2 k.2) := by
  rw [Fintype.sum_prod_type, resid_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma resid_sq_expand {m n : ℕ} (D : Mat m n) (z : Vec m × Vec n) :
    resid D z ^ 2 = ∑ x : (Fin m × Fin n) × (Fin m × Fin n),
      (D x.1.1 x.1.2 * D x.2.1 x.2.2) * (z.1 x.1.1 * z.2 x.1.2 * (z.1 x.2.1 * z.2 x.2.2)) := by
  have hsplit : ∀ f : (Fin m × Fin n) × (Fin m × Fin n) → ℝ,
      ∑ x, f x = ∑ i : Fin m × Fin n, ∑ j : Fin m × Fin n, f (i, j) :=
    fun f => Fintype.sum_prod_type f
  rw [sq, resid_expand, Fintype.sum_mul_sum, hsplit]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma fixed_sq_integral {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (D : Mat m n) :
    ∫ z, resid D z ^ 2 ∂ν = ∑ x : (Fin m × Fin n) × (Fin m × Fin n),
      (D x.1.1 x.1.2 * D x.2.1 x.2.2) * (C.Sout x.1.1 x.2.1 * C.Sin x.1.2 x.2.2) := by
  haveI := hν.isProb
  simp only [resid_sq_expand]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun x _ => by
      rw [integral_const_mul, (phi_phi_integral hν _ _ _ _).2]
  · intro x _
    exact (phi_phi_integral hν _ _ _ _).1.const_mul _

private lemma fixed_lin_integral {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (D : Mat m n) (i : Fin m) (k : Fin n) :
    ∫ z, resid D z * (z.1 i * z.2 k) ∂ν = ∑ kk : Fin m × Fin n,
      D kk.1 kk.2 * (C.Sout kk.1 i * C.Sin kk.2 k) := by
  haveI := hν.isProb
  have hpt : ∀ z : Vec m × Vec n, resid D z * (z.1 i * z.2 k)
      = ∑ kk : Fin m × Fin n, D kk.1 kk.2 * (z.1 kk.1 * z.2 kk.2 * (z.1 i * z.2 k)) := by
    intro z
    rw [resid_expand, Finset.sum_mul]
    exact Finset.sum_congr rfl fun kk _ => by ring
  simp only [hpt]
  rw [integral_finset_sum]
  · exact Finset.sum_congr rfl fun kk _ => by
      rw [integral_const_mul, (phi_phi_integral hν _ _ _ _).2]
  · intro kk _
    exact (phi_phi_integral hν _ _ _ _).1.const_mul _

private lemma grad_entry {m n B : ℕ} (Δ : Mat m n) (b : Batch m n B) (i : Fin m) (k : Fin n) :
    grad Δ b i k = (B : ℝ)⁻¹ * ∑ a, resid Δ (b a) * ((b a).1 i * (b a).2 k) := by
  simp only [grad, Matrix.smul_apply, Matrix.sum_apply, Matrix.vecMulVec_apply, outer,
    smul_eq_mul]

/-- Conditional expectation of a finite sum of products `X k * Ψ k`, where `X k` is
`H`-measurable and `Ψ k` is `G`-measurable with `G` independent of `H`: pull out `X k`
and replace `Ψ k` by its mean. -/
private lemma condExp_sum_indep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {H G : MeasurableSpace Ω} (hH : H ≤ mΩ) (hG : G ≤ mΩ)
    (hind : Indep G H P) {ι : Type*} [Fintype ι] (X Ψ : ι → Ω → ℝ)
    (hX : ∀ k, Measurable[H] (X k)) (hXi : ∀ k, Integrable (X k) P)
    (hΨ : ∀ k, Measurable[G] (Ψ k)) (hΨi : ∀ k, Integrable (Ψ k) P) :
    P[fun ω => ∑ k, X k ω * Ψ k ω | H] =ᵐ[P]
      fun ω => ∑ k, X k ω * ∫ ω', Ψ k ω' ∂P := by
  have hprod : ∀ k, Integrable (fun ω => X k ω * Ψ k ω) P := by
    intro k
    have hInd : IndepFun (X k) (Ψ k) P := by
      rw [IndepFun_iff_Indep]
      exact (indep_of_indep_of_le_right (indep_of_indep_of_le_left hind (hΨ k).comap_le)
        (hX k).comap_le).symm
    exact hInd.integrable_mul (hXi k) (hΨi k)
  have hcond : ∀ k, P[fun ω => X k ω * Ψ k ω | H] =ᵐ[P]
      fun ω => X k ω * ∫ ω', Ψ k ω' ∂P := by
    intro k
    have h1 : P[fun ω => X k ω * Ψ k ω | H] =ᵐ[P] fun ω => X k ω * P[Ψ k | H] ω :=
      condExp_mul_of_stronglyMeasurable_left (hX k).stronglyMeasurable (hprod k) (hΨi k)
    have h2 := condExp_indep_eq hG hH (hΨ k).stronglyMeasurable hind
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, e2]
  have hs := condExp_finsetSum (μ := P) (s := Finset.univ)
    (f := fun k ω => X k ω * Ψ k ω) (fun k _ => hprod k) H
  have hfun : (fun ω => ∑ k, X k ω * Ψ k ω) = ∑ k, (fun ω => X k ω * Ψ k ω) := by
    funext ω
    simp [Finset.sum_apply]
  rw [hfun]
  filter_upwards [hs, ae_all_iff.mpr hcond] with ω e1 e2
  rw [e1]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl fun k _ => e2 k

/-- `prop:app-setup-moments`(iii), snapshot `cr-2026-10-23`, verbatim from `section.tex`
l.109–131 (part (iii) is the third item). Hypotheses: `W t` is `ℱ t`-measurable with square
integrable entries, and the batch of step `t` is independent of `ℱ t` (in `ModelLaw`). -/
theorem prop_app_setup_moments_iii {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] (hν : IsFeatureLaw C ν) {B : ℕ} (hB : 0 < B) (M : ModelLaw P ν B)
    (Wstar : Mat m n) (W : ℕ → Ω → Mat m n)
    (hW : ∀ t, Measurable[M.ℱ t] (W t))
    (t : ℕ) (hWL2 : ∀ i j, MemLp (fun ω => W t ω i j) 2 P) (a : Fin B) :
    (condExp (M.ℱ t) P (fun ω => resid (W t ω - Wstar) (M.x t ω a)) =ᵐ[P] 0) ∧
    (condExp (M.ℱ t) P (fun ω => (resid (W t ω - Wstar) (M.x t ω a)) ^ 2) =ᵐ[P]
      fun ω => 2 * popRisk ν Wstar (W t ω)) ∧
    ∀ (i : Fin m) (k : Fin n),
      (condExp (M.ℱ t) P (fun ω => grad (W t ω - Wstar) (M.x t ω) i k) =ᵐ[P]
        fun ω => (C.Sout * (W t ω - Wstar) * C.Sin) i k) := by
  classical
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hxm : Measurable (M.x t) := (M.x_meas t).mono (M.ℱ.le (t + 1)) le_rfl
  have hGle := hxm.comap_le
  have hHle := M.ℱ.le t
  have hind : Indep (MeasurableSpace.comap (M.x t) inferInstance) (M.ℱ t) P := M.x_indep t
  have hWmeas : ∀ i j, Measurable[M.ℱ t] (fun ω => (W t ω - Wstar) i j) := by
    intro i j
    have hE : Measurable[M.ℱ t] (fun ω => W t ω i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hW t))
    exact hE.sub measurable_const
  have hDL2 : ∀ i j, MemLp (fun ω => (W t ω - Wstar) i j) 2 P := fun i j =>
    (hWL2 i j).sub (memLp_const _)
  have hDint : ∀ i j, Integrable (fun ω => (W t ω - Wstar) i j) P := fun i j =>
    (hDL2 i j).integrable one_le_two
  have hDprod : ∀ i j k l,
      Integrable (fun ω => (W t ω - Wstar) i j * (W t ω - Wstar) k l) P := fun i j k l =>
    (hDL2 i j).integrable_mul (hDL2 k l)
  have hmarg : ∀ a, P.map (fun ω => M.x t ω a) = ν := by
    intro a
    have hf : (fun ω => M.x t ω a) = (fun b : Batch m n B => b a) ∘ M.x t := rfl
    rw [hf, ← Measure.map_map (measurable_pi_apply a) hxm, M.x_law t, Measure.pi_map_eval]
    simp [measure_univ]
  have hcoord : ∀ a (g : Vec m × Vec n → ℝ), Measurable g → Integrable g ν →
      Integrable (fun ω => g (M.x t ω a)) P ∧ ∫ ω, g (M.x t ω a) ∂P = ∫ z, g z ∂ν := by
    intro a g hg hgi
    have hf : AEMeasurable (fun ω => M.x t ω a) P := ((measurable_pi_apply a).comp hxm).aemeasurable
    refine ⟨?_, ?_⟩
    · have h1 := integrable_map_measure hg.aestronglyMeasurable hf
      rw [hmarg a] at h1
      exact h1.mp hgi
    · have h2 := integral_map hf hg.aestronglyMeasurable
      rw [hmarg a] at h2
      exact h2.symm
  have hcm : ∀ a (g : Vec m × Vec n → ℝ), Measurable g →
      Measurable[MeasurableSpace.comap (M.x t) inferInstance] (fun ω => g (M.x t ω a)) :=
    fun a g hg => (hg.comp (measurable_pi_apply a : Measurable (fun b : Batch m n B => b a))).comp
      (comap_measurable (M.x t))
  refine ⟨?_, ?_, ?_⟩
  · -- (i) conditional mean zero
    have hres : (fun ω => resid (W t ω - Wstar) (M.x t ω a))
        = fun ω => ∑ k : Fin m × Fin n, (W t ω - Wstar) k.1 k.2 *
            ((M.x t ω a).1 k.1 * (M.x t ω a).2 k.2) := by
      funext ω
      rw [resid_expand]
    rw [hres]
    have hgen := condExp_sum_indep hHle hGle hind
      (fun (k : Fin m × Fin n) ω => (W t ω - Wstar) k.1 k.2)
      (fun (k : Fin m × Fin n) ω => (M.x t ω a).1 k.1 * (M.x t ω a).2 k.2)
      (fun k => hWmeas k.1 k.2) (fun k => hDint k.1 k.2)
      (fun k => hcm a _ (phi_meas k.1 k.2))
      (fun k => (hcoord a _ (phi_meas k.1 k.2) (phi_integrable hν k.1 k.2)).1)
    refine hgen.trans (ae_of_all P fun ω => ?_)
    simp only [Pi.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [(hcoord a _ (phi_meas k.1 k.2) (phi_integrable hν k.1 k.2)).2,
      phi_integral_zero hν, mul_zero]
  · -- (ii) conditional second moment
    have hpt : (fun ω => resid (W t ω - Wstar) (M.x t ω a) ^ 2)
        = fun ω => ∑ x : (Fin m × Fin n) × (Fin m × Fin n),
            ((W t ω - Wstar) x.1.1 x.1.2 * (W t ω - Wstar) x.2.1 x.2.2) *
              ((M.x t ω a).1 x.1.1 * (M.x t ω a).2 x.1.2 *
                ((M.x t ω a).1 x.2.1 * (M.x t ω a).2 x.2.2)) := by
      funext ω
      exact resid_sq_expand _ _
    rw [hpt]
    have hgen := condExp_sum_indep hHle hGle hind
      (fun (x : (Fin m × Fin n) × (Fin m × Fin n)) ω => (W t ω - Wstar) x.1.1 x.1.2 * (W t ω - Wstar) x.2.1 x.2.2)
      (fun (x : (Fin m × Fin n) × (Fin m × Fin n)) ω => (M.x t ω a).1 x.1.1 * (M.x t ω a).2 x.1.2 *
                ((M.x t ω a).1 x.2.1 * (M.x t ω a).2 x.2.2))
      (fun x => (hWmeas _ _).mul (hWmeas _ _))
      (fun x => hDprod _ _ _ _)
      (fun x => hcm a _ ((phi_meas x.1.1 x.1.2).mul (phi_meas x.2.1 x.2.2)))
      (fun x => (hcoord a _ ((phi_meas x.1.1 x.1.2).mul (phi_meas x.2.1 x.2.2))
        (phi_phi_integral hν x.1.1 x.2.1 x.1.2 x.2.2).1).1)
    refine hgen.trans (ae_of_all P fun ω => ?_)
    have hint : ∀ x : (Fin m × Fin n) × (Fin m × Fin n),
        ∫ ω', (M.x t ω' a).1 x.1.1 * (M.x t ω' a).2 x.1.2 *
            ((M.x t ω' a).1 x.2.1 * (M.x t ω' a).2 x.2.2) ∂P
          = C.Sout x.1.1 x.2.1 * C.Sin x.1.2 x.2.2 := fun x => by
      exact (hcoord a _ ((phi_meas x.1.1 x.1.2).mul (phi_meas x.2.1 x.2.2))
        (phi_phi_integral hν x.1.1 x.2.1 x.1.2 x.2.2).1).2.trans
        (phi_phi_integral hν x.1.1 x.2.1 x.1.2 x.2.2).2
    have hpop : popRisk ν Wstar (W t ω) = (1 / 2 : ℝ) * ∫ z, resid (W t ω - Wstar) z ^ 2 ∂ν := by
      simp only [popRisk, lossSingle, integral_const_mul]
    have key : ∀ c : ℝ, 2 * ((1 / 2 : ℝ) * c) = c := fun c => by ring
    dsimp only
    rw [hpop, fixed_sq_integral hν, key]
    simp only [hint]
  · -- (iii) conditional gradient mean
    intro i k
    have hgradeq : (fun ω => grad (W t ω - Wstar) (M.x t ω) i k)
        = fun ω => ∑ ak : Fin B × (Fin m × Fin n),
            ((B : ℝ)⁻¹ * (W t ω - Wstar) ak.2.1 ak.2.2) *
              ((M.x t ω ak.1).1 ak.2.1 * (M.x t ω ak.1).2 ak.2.2 *
                ((M.x t ω ak.1).1 i * (M.x t ω ak.1).2 k)) := by
      funext ω
      rw [grad_entry, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [resid_expand, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun kk _ => by ring
    rw [hgradeq]
    have hgen := condExp_sum_indep hHle hGle hind
      (fun (ak : Fin B × (Fin m × Fin n)) ω => (B : ℝ)⁻¹ * (W t ω - Wstar) ak.2.1 ak.2.2)
      (fun (ak : Fin B × (Fin m × Fin n)) ω => (M.x t ω ak.1).1 ak.2.1 * (M.x t ω ak.1).2 ak.2.2 *
                ((M.x t ω ak.1).1 i * (M.x t ω ak.1).2 k))
      (fun ak => measurable_const.mul (hWmeas _ _))
      (fun ak => (hDint _ _).const_mul _)
      (fun ak => hcm ak.1 _ ((phi_meas ak.2.1 ak.2.2).mul (phi_meas i k)))
      (fun ak => (hcoord ak.1 _ ((phi_meas ak.2.1 ak.2.2).mul (phi_meas i k))
        (phi_phi_integral hν ak.2.1 i ak.2.2 k).1).1)
    refine hgen.trans (ae_of_all P fun ω => ?_)
    have hint : ∀ ak : Fin B × (Fin m × Fin n),
        ∫ ω', (M.x t ω' ak.1).1 ak.2.1 * (M.x t ω' ak.1).2 ak.2.2 *
            ((M.x t ω' ak.1).1 i * (M.x t ω' ak.1).2 k) ∂P
          = C.Sout ak.2.1 i * C.Sin ak.2.2 k := fun ak => by
      exact (hcoord ak.1 _ ((phi_meas ak.2.1 ak.2.2).mul (phi_meas i k))
        (phi_phi_integral hν ak.2.1 i ak.2.2 k).1).2.trans
        (phi_phi_integral hν ak.2.1 i ak.2.2 k).2
    have hB0 : (B : ℝ) ≠ 0 := by exact_mod_cast hB.ne'
    have hS := (fixed_lin_integral hν (W t ω - Wstar) i k).symm.trans
      (resid_moment hν (W t ω - Wstar) i k).2
    have hrow : ∑ kk : Fin m × Fin n,
        (B : ℝ)⁻¹ * (W t ω - Wstar) kk.1 kk.2 * (C.Sout kk.1 i * C.Sin kk.2 k)
          = (B : ℝ)⁻¹ * (C.Sout * (W t ω - Wstar) * C.Sin) i k := by
      rw [← hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun kk _ => by ring
    simp only [hint]
    rw [Fintype.sum_prod_type]
    simp only [hrow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hB0, one_mul]

/-- `eqn:app-setup-whitened`, first display, snapshot `cr-2026-10-23`, verbatim from
`section.tex` l.201–205:

\begin{equation}\label{eqn:app-setup-whitened}
d_a^\circ=z_a^\T\At w_a,\qquad
\Gt^\circ=\frac1B\sum_{a=1}^Bd_a^\circ\,\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2},\qquad
\cR(t)=\tfrac12\norm{\At}_\F^2 ,
\end{equation}
-/
theorem eqn_app_setup_whitened_resid {m n : ℕ} (C : Covariances m n) (Δ : Mat m n)
    (zw : Vec m × Vec n) :
    resid Δ (phys C zw) = dotProduct zw.1 (Matrix.mulVec (Arot C Δ) zw.2) := by
  have hT := rOut_transpose C
  unfold resid phys Arot
  dsimp only
  rw [dot_symm_mulVec _ hT]
  simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- `eqn:app-setup-whitened`, gradient display, snapshot `cr-2026-10-23`, verbatim from
`section.tex` l.201–205:

\begin{equation}\label{eqn:app-setup-whitened}
d_a^\circ=z_a^\T\At w_a,\qquad
\Gt^\circ=\frac1B\sum_{a=1}^Bd_a^\circ\,\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2},\qquad
\cR(t)=\tfrac12\norm{\At}_\F^2 ,
\end{equation}
-/
theorem eqn_app_setup_whitened_grad {m n B : ℕ} (C : Covariances m n) (Δ : Mat m n)
    (zw : Fin B → Vec m × Vec n) :
    grad Δ (fun a => phys C (zw a)) = ((B : ℝ))⁻¹ •
      ∑ a, (dotProduct (zw a).1 (Matrix.mulVec (Arot C Δ) (zw a).2)) •
        (rOut C * outer (zw a).1 (zw a).2 * rIn C) := by
  unfold grad
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [eqn_app_setup_whitened_resid, outer_phys_eq]

/-- `eqn:app-setup-whitened`, risk display `𝓡(t) = ½ ‖A_t‖²_F`, snapshot `cr-2026-10-23`,
verbatim from `section.tex` l.201–205:

\begin{equation}\label{eqn:app-setup-whitened}
d_a^\circ=z_a^\T\At w_a,\qquad
\Gt^\circ=\frac1B\sum_{a=1}^Bd_a^\circ\,\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2},\qquad
\cR(t)=\tfrac12\norm{\At}_\F^2 ,
\end{equation}
-/
theorem eqn_app_setup_whitened_risk {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) :
    riskSigma C Δ = (fro (Arot C Δ)) ^ 2 / 2 := by
  have hS1 : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have hS2 : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have hTo := rOut_transpose C
  have hTi := rIn_transpose C
  have key : Arot C Δ * (Arot C Δ)ᵀ = rOut C * (Δ * C.Sin * Δᵀ) * rOut C := by
    unfold Arot
    rw [Matrix.transpose_mul, Matrix.transpose_mul, hTo, hTi, ← hS2]
    simp only [Matrix.mul_assoc]
  have h2 : (Arot C Δ * (Arot C Δ)ᵀ).trace = ∑ i, ∑ j, Arot C Δ i j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply, sq]
  have htr : pairSigma C Δ Δ = ∑ i, ∑ j, Arot C Δ i j ^ 2 := by
    unfold pairSigma
    rw [← h2, key, Matrix.trace_mul_cycle (rOut C) (Δ * C.Sin * Δᵀ) (rOut C), hS1]
    simp only [Matrix.mul_assoc]
  have hfro : fro (Arot C Δ) ^ 2 = ∑ i, ∑ j, Arot C Δ i j ^ 2 := by
    unfold fro
    rw [Real.sq_sqrt (by positivity)]
    simp only [Real.norm_eq_abs, sq_abs]
  unfold riskSigma
  rw [htr, hfro]

/-- `assum:data-target`, snapshot `cr-2026-10-23`, verbatim from `section.tex` l.99–107:

\begin{assumption}[Data-target normalization]\label{assum:data-target}
The input and output features are independent and Gaussian,
$\Xin\sim\mathcal N(0,\Sigmain)$ and $\Xout\sim\mathcal N(0,\Sigmaout)$, with
positive semidefinite covariances $\Sigmain\in\R^{\Nin\times\Nin}$ and
$\Sigmaout\in\R^{\Nout\times\Nout}$. They are represented in whitened form as
$\Xin=\Sigmain^{1/2}w$ and $\Xout=\Sigmaout^{1/2}z$ with
$w\sim\mathcal N(0,\Id_{\Nin})$ and $z\sim\mathcal N(0,\Id_{\Nout})$
independent; the whitened columns of a batch are written $(w_a,z_a)_{a\le B}$.
\end{assumption}
-/
theorem isFeatureLaw_dataTarget {m n : ℕ} (C : Covariances m n) :
    IsFeatureLaw C (dataTarget C) := by
  have hf : Measurable (Matrix.mulVec (rOut C)) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hg : Measurable (Matrix.mulVec (rIn C)) :=
    (Continuous.matrix_mulVec continuous_const continuous_id).measurable
  have hS1 : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have hS2 : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have hnu : dataTarget C = ((Muon.Foundations.stdGaussianPi m).map (Matrix.mulVec (rOut C))).prod
      ((Muon.Foundations.stdGaussianPi n).map (Matrix.mulVec (rIn C))) := by
    unfold dataTarget
    rw [Measure.map_prod_map _ _ hf hg]
    rfl
  have hfst : (dataTarget C).fst
      = (Muon.Foundations.stdGaussianPi m).map (Matrix.mulVec (rOut C)) := by
    rw [hnu]; exact Measure.fst_prod
  have hsnd : (dataTarget C).snd
      = (Muon.Foundations.stdGaussianPi n).map (Matrix.mulVec (rIn C)) := by
    rw [hnu]; exact Measure.snd_prod
  have hsplit : dataTarget C = (dataTarget C).fst.prod (dataTarget C).snd := by
    rw [hfst, hsnd]; exact hnu
  have hF_out : ∀ F : Vec m → ℝ, Measurable F →
      ∫ x, F x.1 ∂(dataTarget C)
        = ∫ z, F (Matrix.mulVec (rOut C) z) ∂(Muon.Foundations.stdGaussianPi m) := by
    intro F hF
    rw [hnu, integral_fun_fst, integral_map hf.aemeasurable hF.aestronglyMeasurable]
    simp
  have hF_in : ∀ F : Vec n → ℝ, Measurable F →
      ∫ x, F x.2 ∂(dataTarget C)
        = ∫ z, F (Matrix.mulVec (rIn C) z) ∂(Muon.Foundations.stdGaussianPi n) := by
    intro F hF
    rw [hnu, integral_fun_snd, integral_map hg.aemeasurable hF.aestronglyMeasurable]
    simp
  refine ⟨by rw [hnu]; infer_instance, hsplit, fun i => ?_, fun j => ?_, fun i => ?_,
    fun j => ?_, fun i k => ?_, fun j l => ?_⟩
  · rw [hnu]; exact memLp_fst_prod _ _ (memLp_map_coord (rOut C) i)
  · rw [hnu]; exact memLp_snd_prod _ _ (memLp_map_coord (rIn C) j)
  · exact (hF_out (fun y => y i) (measurable_pi_apply i)).trans (integral_mulVec_apply (rOut C) i)
  · exact (hF_in (fun y => y j) (measurable_pi_apply j)).trans (integral_mulVec_apply (rIn C) j)
  · refine (hF_out (fun y => y i * y k) ((measurable_pi_apply i).mul (measurable_pi_apply k))).trans ?_
    refine (gauss_mulVec_second (rOut C) i k).trans ?_
    rw [rOut_transpose C]
    exact congrFun (congrFun hS1 i) k
  · refine (hF_in (fun y => y j * y l) ((measurable_pi_apply j).mul (measurable_pi_apply l))).trans ?_
    refine (gauss_mulVec_second (rIn C) j l).trans ?_
    rw [rIn_transpose C]
    exact congrFun (congrFun hS2 j) l

/-- `eqn:app-setup-normalized`, residual display `d_a = z_aᵀ Â w_a` (the normalized residual
written in whitened form), snapshot `cr-2026-10-23`, verbatim from `section.tex` l.209–215:

\begin{equation}\label{eqn:app-setup-normalized}
\begin{gathered}
\Ahat\defeq\frac{\At}{\sqrt{2\cR(t)}},\qquad
d_a\defeq\frac{d_a^\circ}{\sqrt{2\cR(t)}}=z_a^\T\Ahat w_a,\\
\Gt\defeq\frac{\Gt^\circ}{\sqrt{2\cR(t)}}=\frac1B\sum_{a=1}^Bd_a\,\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}.
\end{gathered}
\end{equation}
-/
theorem eqn_app_setup_normalized_resid {m n : ℕ} (C : Covariances m n) (Δ : Mat m n)
    (zw : Vec m × Vec n) :
    dNorm C Δ (phys C zw) = dotProduct zw.1 (Matrix.mulVec (Ahat C Δ) zw.2) := by
  unfold dNorm Ahat
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, eqn_app_setup_whitened_resid,
    div_eq_inv_mul]

/-- `eqn:app-setup-normalized`, gradient display
`Ĝ = (1/B) ∑_a d_a Σ_out^{1/2}(z_a ⊗ w_a)Σ_in^{1/2}` (whitened form), snapshot `cr-2026-10-23`,
verbatim from `section.tex` l.209–215:

\begin{equation}\label{eqn:app-setup-normalized}
\begin{gathered}
\Ahat\defeq\frac{\At}{\sqrt{2\cR(t)}},\qquad
d_a\defeq\frac{d_a^\circ}{\sqrt{2\cR(t)}}=z_a^\T\Ahat w_a,\\
\Gt\defeq\frac{\Gt^\circ}{\sqrt{2\cR(t)}}=\frac1B\sum_{a=1}^Bd_a\,\Sigmaout^{1/2}(z_a\tensor w_a)\Sigmain^{1/2}.
\end{gathered}
\end{equation}
-/
theorem eqn_app_setup_normalized_grad {m n B : ℕ} (C : Covariances m n) (Δ : Mat m n)
    (zw : Fin B → Vec m × Vec n) :
    Gnorm C Δ (fun a => phys C (zw a)) = ((B : ℝ))⁻¹ •
      ∑ a, (dotProduct (zw a).1 (Matrix.mulVec (Ahat C Δ) (zw a).2)) •
        (rOut C * outer (zw a).1 (zw a).2 * rIn C) := by
  have hA : ∀ a, dotProduct (zw a).1 (Matrix.mulVec (Ahat C Δ) (zw a).2)
      = (Real.sqrt (2 * riskSigma C Δ))⁻¹ * dotProduct (zw a).1 (Matrix.mulVec (Arot C Δ) (zw a).2) := by
    intro a
    unfold Ahat
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  unfold Gnorm
  rw [eqn_app_setup_whitened_grad]
  simp only [hA, mul_smul, ← Finset.smul_sum]
  rw [smul_comm]

private lemma fro_sq_eq_sum {m n : ℕ} (K : Mat m n) :
    fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma mean_smul_const {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ} (P : Measure Ω)
    (c : ℝ) (X : Ω → Mat m n) :
    mean P (fun ω => c • X ω) = c • mean P X := by
  unfold mean
  ext i j
  simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  rw [integral_const_mul]

private lemma inv_scale_smul {m n : ℕ} (c s : ℝ) (hc : 0 < c) (M : Mat m n) :
    (c * s)⁻¹ • c • M = s⁻¹ • M := by
  rw [smul_smul, mul_inv, mul_comm c⁻¹ s⁻¹, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one]

/-- `prop:app-setup-normalization`(i), snapshot `cr-2026-10-23`, verbatim from `section.tex`
l.217–233 (part (i) is the first item, with its scaling clause):

\begin{proposition}[Normalization]\label{prop:app-setup-normalization}
Assume \cref{assum:data-target}.
\begin{enumerate}[label=(\roman*)]
\item If $\Dt=\Delta$ is deterministic with $\cR(t)>0$, then
$\norm{\Ahat}_\F=1$, the normalized residuals are centered with unit variance,
and
\begin{equation}\label{eqn:app-setup-normalized-moments}
\EE\,d_a=0,\qquad \EE\,d_a^2=1,\qquad
\EE\,\Gt=\Sigmaout^{1/2}\Ahat\Sigmain^{1/2}=\frac{\Sigmaout\Delta\Sigmain}{\sqrt{2\cR(t)}} .
\end{equation}
For every $c>0$, replacing $\Delta$ by $c\Delta$ with the same batch
multiplies $\cR(t)$ by $c^2$ and leaves $\Ahat$, $d_a$ and $\Gt$ unchanged.
\item For the state $\Dt$ at step $t$ and the fresh batch of step $t$, on
the event $\{\cR(t)>0\}$ the identities \cref{eqn:app-setup-normalized-moments}
hold with $\EE_t$ in place of $\EE$ and $\Dt$ in place of $\Delta$.
\end{enumerate}
\end{proposition}
-/
theorem prop_app_setup_normalization_i {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω)
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) {B : ℕ} (hB : 0 < B) (Δ : Mat m n) (hR : 0 < riskSigma C Δ)
    (x : Fin B → Ω → Vec m × Vec n) (hx : IIDBatch P ν x) :
    fro (Ahat C Δ) = 1 ∧
    (∀ a, ∫ ω, dNorm C Δ (x a ω) ∂P = 0) ∧
    (∀ a, ∫ ω, (dNorm C Δ (x a ω)) ^ 2 ∂P = 1) ∧
    mean P (fun ω => Gnorm C Δ (fun a => x a ω)) = rOut C * Ahat C Δ * rIn C ∧
    mean P (fun ω => Gnorm C Δ (fun a => x a ω)) =
      (Real.sqrt (2 * riskSigma C Δ))⁻¹ • (C.Sout * Δ * C.Sin) ∧
    (∀ c : ℝ, 0 < c →
      riskSigma C (c • Δ) = c ^ 2 * riskSigma C Δ ∧
      Ahat C (c • Δ) = Ahat C Δ ∧
      (∀ z : Vec m × Vec n, dNorm C (c • Δ) z = dNorm C Δ z) ∧
      (∀ b : Batch m n B, Gnorm C (c • Δ) b = Gnorm C Δ b)) := by
  haveI := hν.isProb
  have hR0 : (0:ℝ) ≤ 2 * riskSigma C Δ := by linarith
  have hR2 : (2 * riskSigma C Δ) ≠ 0 := by linarith
  have hsqR : Real.sqrt (2 * riskSigma C Δ) ^ 2 = 2 * riskSigma C Δ := Real.sq_sqrt hR0
  -- Ahat, fro: fro(Ahat)^2 = (2R)⁻¹ * fro(Arot)^2 = 1
  have hsumA : ∑ i, ∑ j, Arot C Δ i j ^ 2 = 2 * riskSigma C Δ := by
    have h := eqn_app_setup_whitened_risk C Δ
    have hf := fro_sq_eq_sum (Arot C Δ)
    linarith
  have hfro2 : fro (Ahat C Δ) ^ 2 = 1 := by
    rw [fro_sq_eq_sum]
    unfold Ahat
    simp only [Matrix.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [hsumA, inv_pow, hsqR, inv_mul_cancel₀ hR2]
  have hfro : fro (Ahat C Δ) = 1 := by
    have hnn : 0 ≤ fro (Ahat C Δ) := Real.sqrt_nonneg _
    have hfac : (fro (Ahat C Δ) - 1) * (fro (Ahat C Δ) + 1) = 0 := by
      ring_nf; linarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · linarith
  -- moments of the normalized residual
  have hd : ∀ z : Vec m × Vec n, dNorm C Δ z = (Real.sqrt (2 * riskSigma C Δ))⁻¹ * resid Δ z :=
    fun z => by unfold dNorm; rw [div_eq_inv_mul]
  have hd2 : ∀ z : Vec m × Vec n, dNorm C Δ z ^ 2 = (2 * riskSigma C Δ)⁻¹ * resid Δ z ^ 2 :=
    fun z => by
      unfold dNorm
      rw [div_pow, hsqR, div_eq_inv_mul]
  have hp : pairSigma C Δ Δ = 2 * riskSigma C Δ := by unfold riskSigma; ring
  have hgm : mean P (fun ω => grad Δ (fun a => x a ω)) = C.Sout * Δ * C.Sin :=
    (prop_app_setup_moments_ii P hν hB Δ x hx).2
  have hmean : mean P (fun ω => Gnorm C Δ (fun a => x a ω))
      = (Real.sqrt (2 * riskSigma C Δ))⁻¹ • mean P (fun ω => grad Δ (fun a => x a ω)) := by
    unfold Gnorm
    exact mean_smul_const P _ _
  have key : C.Sout * Δ * C.Sin = rOut C * (rOut C * Δ * rIn C) * rIn C := by
    have hS1 : rOut C * rOut C = C.Sout :=
      CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
    have hS2 : rIn C * rIn C = C.Sin :=
      CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
    conv_lhs => rw [← hS1, ← hS2]
    simp only [Matrix.mul_assoc]
  refine ⟨hfro, fun a => ?_, fun a => ?_, ?_, ?_, ?_⟩
  · -- E d_a = 0
    have h1 : ∀ ω, dNorm C Δ (x a ω) = (Real.sqrt (2 * riskSigma C Δ))⁻¹ * resid Δ (x a ω) :=
      fun ω => hd _
    simp only [h1]
    rw [integral_const_mul]
    have hT : ∫ ω, resid Δ (x a ω) ∂P = ∫ z, resid Δ z ∂ν :=
      (iid_transfer hx a (hx.meas a) (resid Δ) (resid_measurable Δ)).2
    rw [hT, resid_integral_zero hν Δ, mul_zero]
  · -- E d_a^2 = 1
    have h2 : ∀ ω, dNorm C Δ (x a ω) ^ 2 = (2 * riskSigma C Δ)⁻¹ * resid Δ (x a ω) ^ 2 :=
      fun ω => hd2 _
    simp only [h2]
    rw [integral_const_mul]
    have hT : ∫ ω, resid Δ (x a ω) ^ 2 ∂P = ∫ z, resid Δ z ^ 2 ∂ν :=
      (iid_transfer hx a (hx.meas a) (fun z => resid Δ z ^ 2)
        ((resid_measurable Δ).pow_const 2)).2
    rw [hT, (resid_sq_integral hν Δ).2, hp, inv_mul_cancel₀ hR2]
  · -- E G = rOut Ahat rIn
    rw [hmean, hgm]
    unfold Ahat Arot
    rw [Matrix.mul_smul, Matrix.smul_mul, key]
  · -- E G = (√(2R))⁻¹ Σ_out Δ Σ_in
    rw [hmean, hgm]
  · -- scaling
    intro c hc
    have hR_scale : riskSigma C (c • Δ) = c ^ 2 * riskSigma C Δ := by
      unfold riskSigma pairSigma
      simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_smul, Matrix.trace_smul,
        smul_eq_mul]
      ring
    have hsq : Real.sqrt (2 * riskSigma C (c • Δ))
        = c * Real.sqrt (2 * riskSigma C Δ) := by
      rw [hR_scale, show 2 * (c ^ 2 * riskSigma C Δ) = c ^ 2 * (2 * riskSigma C Δ) by ring,
        Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
    have hres : ∀ z : Vec m × Vec n, resid (c • Δ) z = c * resid Δ z := by
      intro z
      unfold resid
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hg : ∀ b : Batch m n B, grad (c • Δ) b = c • grad Δ b := by
      intro b
      unfold grad
      simp only [hres, mul_smul, ← Finset.smul_sum, smul_comm ((B : ℝ)⁻¹) c]
    refine ⟨hR_scale, ?_, fun z => ?_, fun b => ?_⟩
    · unfold Ahat Arot
      rw [hsq, Matrix.mul_smul, Matrix.smul_mul]
      exact inv_scale_smul c _ hc _
    · unfold dNorm
      rw [hres, hsq, mul_div_mul_left _ _ hc.ne']
    · unfold Gnorm
      rw [hsq, hg]
      exact inv_scale_smul c _ hc _

private lemma meas_resid_comp {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    {Δ : Ω → Mat m n} (hΔ : ∀ i j, Measurable fun ω => Δ ω i j)
    {x : Ω → Vec m × Vec n} (hx : Measurable x) :
    Measurable fun ω => resid (Δ ω) (x ω) := by
  simp only [resid_eq_sum]
  refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply i).comp (measurable_fst.comp hx)).mul
    ((hΔ i j).mul ((measurable_pi_apply j).comp (measurable_snd.comp hx)))

private lemma riskSigma_poly {m n : ℕ} {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    (hν : IsFeatureLaw C ν) (D : Mat m n) :
    riskSigma C D = (∑ x : (Fin m × Fin n) × (Fin m × Fin n),
      (D x.1.1 x.1.2 * D x.2.1 x.2.2) * (C.Sout x.1.1 x.2.1 * C.Sin x.1.2 x.2.2)) / 2 := by
  haveI := hν.isProb
  unfold riskSigma
  rw [← (resid_sq_integral hν D).2, fixed_sq_integral hν]

private lemma measurable_riskSigma {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    {C : Covariances m n} {ν : Measure (Vec m × Vec n)} (hν : IsFeatureLaw C ν)
    {D : Ω → Mat m n} (hD : ∀ i j, Measurable fun ω => D ω i j) :
    Measurable fun ω => riskSigma C (D ω) := by
  simp only [riskSigma_poly hν]
  exact (Finset.measurable_sum _ fun x _ => ((hD _ _).mul (hD _ _)).mul_const _).div_const _

private lemma measSet_A {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    {D : Ω → Mat m n} (hD : ∀ i j, Measurable fun ω => D ω i j) {R : Ω → ℝ}
    (hR : Measurable R) (N : ℕ) :
    MeasurableSet {ω | (∀ i j, |D ω i j| ≤ N) ∧ ((N : ℝ) + 1)⁻¹ ≤ R ω} := by
  have h1 : MeasurableSet {ω | ∀ i j, |D ω i j| ≤ N} := by
    have : {ω | ∀ i j, |D ω i j| ≤ N} = ⋂ i, ⋂ j, {ω | |D ω i j| ≤ N} := by
      ext ω; simp
    rw [this]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      measurableSet_le (hD i j).abs measurable_const
  exact h1.inter (measurableSet_le measurable_const hR)

private lemma exists_A {m n : ℕ} (D : Mat m n) (R : ℝ) (hR : 0 < R) :
    ∃ N : ℕ, (∀ i j, |D i j| ≤ N) ∧ ((N : ℝ) + 1)⁻¹ ≤ R := by
  obtain ⟨N1, hN1⟩ := exists_nat_ge (∑ i, ∑ j, |D i j|)
  obtain ⟨N2, hN2⟩ := exists_nat_ge R⁻¹
  refine ⟨max N1 N2, fun i j => ?_, ?_⟩
  · have h1 : |D i j| ≤ ∑ j', |D i j'| :=
      Finset.single_le_sum (f := fun j' => |D i j'|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ j)
    have h2 : ∑ j', |D i j'| ≤ ∑ i', ∑ j', |D i' j'| :=
      Finset.single_le_sum (f := fun i' => ∑ j', |D i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have h3 : (N1 : ℝ) ≤ ((max N1 N2 : ℕ) : ℝ) := by exact_mod_cast le_max_left _ _
    linarith
  · have h3 : (N2 : ℝ) ≤ ((max N1 N2 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have h4 : R⁻¹ ≤ ((max N1 N2 : ℕ) : ℝ) + 1 := by linarith
    calc (((max N1 N2 : ℕ) : ℝ) + 1)⁻¹ ≤ (R⁻¹)⁻¹ := inv_anti₀ (inv_pos.mpr hR) h4
      _ = R := inv_inv R

private lemma integrable_of_trunc {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) (hnn : ∀ ω, 0 ≤ f ω)
    (A : ℕ → Set Ω) (hmono : Monotone A) (hcover : ∀ ω, 0 < f ω → ∃ n, ω ∈ A n)
    (hAm : ∀ n, MeasurableSet (A n))
    (hint : ∀ n, Integrable ((A n).indicator f) P)
    (hbd : ∀ n, ∫ ω, (A n).indicator f ω ∂P ≤ 1) : Integrable f P := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have hmeas : ∀ n, Measurable fun ω => ENNReal.ofReal ((A n).indicator f ω) := fun n =>
    ENNReal.measurable_ofReal.comp (hf.indicator (hAm n))
  have hmo : ∀ ω, Monotone fun n => ENNReal.ofReal ((A n).indicator f ω) := by
    intro ω n m hnm
    apply ENNReal.ofReal_le_ofReal
    by_cases h : ω ∈ A n
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmono hnm h)]
    · rw [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun _ _ => hnn _) _
  have htend : ∀ ω, Filter.Tendsto (fun n => ENNReal.ofReal ((A n).indicator f ω))
      Filter.atTop (nhds (ENNReal.ofReal (f ω))) := by
    intro ω
    by_cases h : 0 < f ω
    · obtain ⟨n0, hn0⟩ := hcover ω h
      refine tendsto_atTop_of_eventually_const (i₀ := n0) fun n hn => ?_
      rw [Set.indicator_of_mem (hmono hn hn0)]
    · have h0 : f ω = 0 := le_antisymm (not_lt.mp h) (hnn ω)
      have hz : ∀ n, (A n).indicator f ω = 0 := fun n => by
        by_cases hh : ω ∈ A n
        · rw [Set.indicator_of_mem hh, h0]
        · rw [Set.indicator_of_notMem hh]
      simp [hz, h0]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone (μ := P)
    (fun n => (hmeas n).aemeasurable) (ae_of_all _ hmo) (ae_of_all _ htend)
  have hle : ∀ n, ∫⁻ ω, ENNReal.ofReal ((A n).indicator f ω) ∂P ≤ 1 := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hint n)
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => hnn _) _)]
    calc ENNReal.ofReal _ ≤ ENNReal.ofReal 1 := ENNReal.ofReal_le_ofReal (hbd n)
      _ = 1 := ENNReal.ofReal_one
  have hF : ∫⁻ ω, ENNReal.ofReal (f ω) ∂P ≤ 1 := le_of_tendsto' hlim hle
  refine lt_of_le_of_lt ?_ (show (1 : ENNReal) < ⊤ from ENNReal.one_lt_top)
  calc ∫⁻ ω, ‖f ω‖ₑ ∂P = ∫⁻ ω, ENNReal.ofReal (f ω) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [← ofReal_norm, Real.norm_of_nonneg (hnn ω)]
    _ ≤ 1 := hF

private lemma int_sum_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*}
    [Fintype ι] (X Ψ : ι → Ω → ℝ) (hXm : ∀ k, AEStronglyMeasurable (X k) P)
    (K : ℝ) (hXb : ∀ k ω, |X k ω| ≤ K) (hΨ : ∀ k, Integrable (Ψ k) P) :
    Integrable (fun ω => ∑ k, X k ω * Ψ k ω) P :=
  integrable_finsetSum _ fun k _ => (hΨ k).bdd_mul (hXm k)
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hXb k ω)

private lemma Gnorm_entry {m n B : ℕ} (C : Covariances m n) (Δ : Mat m n) (b : Batch m n B)
    (i : Fin m) (k : Fin n) :
    Gnorm C Δ b i k = (B : ℝ)⁻¹ * ∑ a, dNorm C Δ (b a) * ((b a).1 i * (b a).2 k) := by
  unfold Gnorm dNorm
  simp only [Matrix.smul_apply, grad_entry, smul_eq_mul, div_eq_inv_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

private lemma rotAhat_eq {m n : ℕ} (C : Covariances m n) (D : Mat m n) :
    rOut C * Ahat C D * rIn C
      = (Real.sqrt (2 * riskSigma C D))⁻¹ • (C.Sout * D * C.Sin) := by
  have key : C.Sout * D * C.Sin = rOut C * (rOut C * D * rIn C) * rIn C := by
    have hS1 : rOut C * rOut C = C.Sout :=
      CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
    have hS2 : rIn C * rIn C = C.Sin :=
      CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
    conv_lhs => rw [← hS1, ← hS2]
    simp only [Matrix.mul_assoc]
  unfold Ahat Arot
  rw [Matrix.mul_smul, Matrix.smul_mul, key]

/-- `prop:app-setup-normalization`(ii), snapshot `cr-2026-10-23`, verbatim from `section.tex`
l.217–233 (part (ii) is the second item). The identities hold on `{𝓡(t) > 0}` with `E_t`. -/
theorem prop_app_setup_normalization_ii {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω}
    [IsProbabilityMeasure P] {C : Covariances m n} {ν : Measure (Vec m × Vec n)}
    [IsProbabilityMeasure ν] (hν : IsFeatureLaw C ν) {B : ℕ} (hB : 0 < B) (M : ModelLaw P ν B)
    (Wstar : Mat m n) (W : ℕ → Ω → Mat m n)
    (hW : ∀ t, Measurable[M.ℱ t] (W t))
    (t : ℕ) (a : Fin B) :
    (∀ᵐ ω ∂P, 0 < riskSigma C (W t ω - Wstar) →
      condExp (M.ℱ t) P (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a)) ω = 0) ∧
    (∀ᵐ ω ∂P, 0 < riskSigma C (W t ω - Wstar) →
      condExp (M.ℱ t) P (fun ω => (dNorm C (W t ω - Wstar) (M.x t ω a)) ^ 2) ω = 1) ∧
    (∀ (i : Fin m) (k : Fin n), ∀ᵐ ω ∂P, 0 < riskSigma C (W t ω - Wstar) →
      condExp (M.ℱ t) P (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k) ω =
        (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹ *
          (C.Sout * (W t ω - Wstar) * C.Sin) i k) ∧
    (∀ (i : Fin m) (k : Fin n), ∀ᵐ ω ∂P, 0 < riskSigma C (W t ω - Wstar) →
      condExp (M.ℱ t) P (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k) ω =
        (rOut C * Ahat C (W t ω - Wstar) * rIn C) i k) := by
  classical
  haveI : ENNReal.HolderTriple 2 2 1 := ⟨by rw [inv_one]; exact ENNReal.inv_two_add_inv_two⟩
  have hxm : Measurable (M.x t) := (M.x_meas t).mono (M.ℱ.le (t + 1)) le_rfl
  have hHle := M.ℱ.le t
  have hxa : ∀ a' : Fin B, Measurable fun ω => M.x t ω a' := fun a' =>
    (measurable_pi_apply a').comp hxm
  have hDe : ∀ i j, Measurable[M.ℱ t] (fun ω => (W t ω - Wstar) i j) := by
    intro i j
    have hE : Measurable[M.ℱ t] (fun ω => W t ω i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hW t))
    exact hE.sub measurable_const
  have hDe0 : ∀ i j, Measurable (fun ω => (W t ω - Wstar) i j) := fun i j =>
    (hDe i j).mono hHle le_rfl
  have hRm : Measurable[M.ℱ t] (fun ω => riskSigma C (W t ω - Wstar)) :=
    @measurable_riskSigma Ω (M.ℱ t) m n C ν hν (fun ω => W t ω - Wstar) hDe
  have hRm0 : Measurable (fun ω => riskSigma C (W t ω - Wstar)) := hRm.mono hHle le_rfl
  have hdm : ∀ a' : Fin B, Measurable fun ω => dNorm C (W t ω - Wstar) (M.x t ω a') := fun a' =>
    (meas_resid_comp hDe0 (hxa a')).div ((hRm0.const_mul 2).sqrt)
  have hmarg : ∀ a, P.map (fun ω => M.x t ω a) = ν := by
    intro a
    have hf : (fun ω => M.x t ω a) = (fun b : Batch m n B => b a) ∘ M.x t := rfl
    rw [hf, ← Measure.map_map (measurable_pi_apply a) hxm, M.x_law t, Measure.pi_map_eval]
    simp [measure_univ]
  have hcoord : ∀ a (g : Vec m × Vec n → ℝ), Measurable g → Integrable g ν →
      Integrable (fun ω => g (M.x t ω a)) P := by
    intro a g hg hgi
    have hf : AEMeasurable (fun ω => M.x t ω a) P := (hxa a).aemeasurable
    have h1 := integrable_map_measure hg.aestronglyMeasurable hf
    rw [hmarg a] at h1
    exact h1.mp hgi
  have hpop : ∀ W' : Mat m n, popRisk ν Wstar W' = riskSigma C (W' - Wstar) :=
    fun W' => (prop_app_setup_moments_i hν 0).2.2.2.2.2 Wstar W'
  have hpop0 : ∀ W' : Mat m n, 0 ≤ popRisk ν Wstar W' := fun W' =>
    integral_nonneg fun x => by unfold lossSingle; positivity
  -- truncation events
  obtain ⟨A, hAmem, hAmeas⟩ : ∃ A : ℕ → Set Ω,
      (∀ N ω, ω ∈ A N ↔ ((∀ i j, |(W t ω - Wstar) i j| ≤ N) ∧
        ((N : ℝ) + 1)⁻¹ ≤ riskSigma C (W t ω - Wstar))) ∧
      ∀ N, MeasurableSet[M.ℱ t] (A N) :=
    ⟨fun N => {ω | (∀ i j, |(W t ω - Wstar) i j| ≤ N) ∧
        ((N : ℝ) + 1)⁻¹ ≤ riskSigma C (W t ω - Wstar)},
      fun _ _ => Iff.rfl,
      fun N => @measSet_A Ω (M.ℱ t) m n (fun ω => W t ω - Wstar) hDe _ hRm N⟩
  have hAmeas0 : ∀ N, MeasurableSet (A N) := fun N => hHle _ (hAmeas N)
  have hRpos : ∀ N ω, ω ∈ A N → 0 < riskSigma C (W t ω - Wstar) := by
    intro N ω hω
    exact lt_of_lt_of_le (by positivity) ((hAmem N ω).mp hω).2
  have hAmono : Monotone A := by
    intro N N' hN ω hω
    rw [hAmem] at hω ⊢
    have hc : (N : ℝ) ≤ N' := by exact_mod_cast hN
    refine ⟨fun i j => (hω.1 i j).trans hc, le_trans ?_ hω.2⟩
    exact inv_anti₀ (by positivity) (by linarith)
  have hcover : ∀ ω, 0 < riskSigma C (W t ω - Wstar) → ∃ N, ω ∈ A N := by
    intro ω hR
    obtain ⟨N, hN1, hN2⟩ := exists_A (W t ω - Wstar) _ hR
    exact ⟨N, (hAmem N ω).mpr ⟨hN1, hN2⟩⟩
  -- the F_t-measurable truncated scale factor
  obtain ⟨c, hc⟩ : ∃ c : ℕ → Ω → ℝ, ∀ N,
      c N = (A N).indicator (fun ω => (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹) :=
    ⟨fun N => (A N).indicator (fun ω => (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹),
      fun _ => rfl⟩
  have hcm : ∀ N, Measurable[M.ℱ t] (c N) := by
    intro N
    rw [hc N]
    exact ((hRm.const_mul 2).sqrt.inv).indicator (hAmeas N)
  have hc_in : ∀ N ω, ω ∈ A N →
      c N ω = (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹ := by
    intro N ω hω
    rw [hc N, Set.indicator_of_mem hω]
  have hc_out : ∀ N ω, ω ∉ A N → c N ω = 0 := by
    intro N ω hω
    rw [hc N, Set.indicator_of_notMem hω]
  have hcb : ∀ N ω, |c N ω| ≤ (N : ℝ) + 1 := by
    intro N ω
    by_cases hω : ω ∈ A N
    · rw [hc_in N ω hω]
      have hR := ((hAmem N ω).mp hω).2
      have hu : (0 : ℝ) < ((N : ℝ) + 1)⁻¹ := by positivity
      have hu1 : ((N : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) N])
      have hs : ((N : ℝ) + 1)⁻¹ ≤ Real.sqrt (2 * riskSigma C (W t ω - Wstar)) := by
        apply Real.le_sqrt_of_sq_le
        nlinarith
      rw [abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      calc (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹ ≤ (((N : ℝ) + 1)⁻¹)⁻¹ :=
            inv_anti₀ hu hs
        _ = (N : ℝ) + 1 := inv_inv _
    · rw [hc_out N ω hω]
      simp only [abs_zero]
      positivity
  -- truncated state
  obtain ⟨Wt, hWt⟩ : ∃ Wt : ℕ → Ω → Mat m n,
      ∀ N ω, Wt N ω = if ω ∈ A N then W t ω else Wstar :=
    ⟨fun N ω => if ω ∈ A N then W t ω else Wstar, fun _ _ => rfl⟩
  have hWtD : ∀ N ω, ω ∈ A N → Wt N ω - Wstar = W t ω - Wstar := by
    intro N ω hω; rw [hWt, if_pos hω]
  have hWt0 : ∀ N ω, ω ∉ A N → Wt N ω - Wstar = 0 := by
    intro N ω hω; rw [hWt, if_neg hω, sub_self]
  have hWtm : ∀ N, Measurable[M.ℱ t] (Wt N) := by
    intro N
    have : Wt N = fun ω => if ω ∈ A N then W t ω else Wstar := funext (hWt N)
    rw [this]
    exact Measurable.ite (hAmeas N) (hW t) measurable_const
  have hWte : ∀ N i j, Measurable[M.ℱ t] (fun ω => (Wt N ω - Wstar) i j) := by
    intro N i j
    have hE : Measurable[M.ℱ t] (fun ω => Wt N ω i j) :=
      (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (hWtm N))
    exact hE.sub measurable_const
  have hWtb : ∀ N ω i j, |(Wt N ω - Wstar) i j| ≤ N := by
    intro N ω i j
    by_cases hω : ω ∈ A N
    · rw [hWtD N ω hω]; exact ((hAmem N ω).mp hω).1 i j
    · rw [hWt0 N ω hω]; simp
  have hWtL2 : ∀ N i j, MemLp (fun ω => Wt N ω i j) 2 P := by
    intro N i j
    refine MemLp.of_bound (C := (N : ℝ) + |Wstar i j|) ?_ (ae_of_all _ fun ω => ?_)
    · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        ((hWtm N).mono hHle le_rfl))).aestronglyMeasurable
    · have h1 := hWtb N ω i j
      have h2 : Wt N ω i j = (Wt N ω - Wstar) i j + Wstar i j := by
        simp [Matrix.sub_apply]
      rw [Real.norm_eq_abs, h2]
      calc |(Wt N ω - Wstar) i j + Wstar i j| ≤ |(Wt N ω - Wstar) i j| + |Wstar i j| :=
            abs_add_le _ _
        _ ≤ _ := by linarith
  have hmom : ∀ (N : ℕ) (a' : Fin B),
      (condExp (M.ℱ t) P (fun ω => resid (Wt N ω - Wstar) (M.x t ω a')) =ᵐ[P] 0) ∧
      (condExp (M.ℱ t) P (fun ω => (resid (Wt N ω - Wstar) (M.x t ω a')) ^ 2) =ᵐ[P]
        fun ω => 2 * popRisk ν Wstar (Wt N ω)) ∧
      ∀ (i : Fin m) (k : Fin n),
        (condExp (M.ℱ t) P (fun ω => grad (Wt N ω - Wstar) (M.x t ω) i k) =ᵐ[P]
          fun ω => (C.Sout * (Wt N ω - Wstar) * C.Sin) i k) := by
    intro N a'
    have h := prop_app_setup_moments_iii hν hB M Wstar
      (fun s => if s = t then Wt N else fun _ => Wstar)
      (fun s => by
        by_cases hs : s = t
        · subst hs
          simpa using hWtm N
        · simp only [if_neg hs]
          exact measurable_const)
      t (by simpa using hWtL2 N) a'
    simpa using h
  -- integrability of the truncated quantities
  have hgint : ∀ N a', Integrable (fun ω => resid (Wt N ω - Wstar) (M.x t ω a')) P := by
    intro N a'
    have hres : (fun ω => resid (Wt N ω - Wstar) (M.x t ω a'))
        = fun ω => ∑ k : Fin m × Fin n, (Wt N ω - Wstar) k.1 k.2 *
            ((M.x t ω a').1 k.1 * (M.x t ω a').2 k.2) := by
      funext ω
      rw [resid_expand]
    rw [hres]
    exact int_sum_bdd _ _ (fun k => ((hWte N k.1 k.2).mono hHle le_rfl).aestronglyMeasurable)
      N (fun k ω => hWtb N ω k.1 k.2)
      (fun k => hcoord a' _ (phi_meas k.1 k.2) (phi_integrable hν k.1 k.2))
  have hg2int : ∀ N a', Integrable (fun ω => (resid (Wt N ω - Wstar) (M.x t ω a')) ^ 2) P := by
    intro N a'
    have hpt : (fun ω => resid (Wt N ω - Wstar) (M.x t ω a') ^ 2)
        = fun ω => ∑ x : (Fin m × Fin n) × (Fin m × Fin n),
            ((Wt N ω - Wstar) x.1.1 x.1.2 * (Wt N ω - Wstar) x.2.1 x.2.2) *
              ((M.x t ω a').1 x.1.1 * (M.x t ω a').2 x.1.2 *
                ((M.x t ω a').1 x.2.1 * (M.x t ω a').2 x.2.2)) := by
      funext ω
      exact resid_sq_expand _ _
    rw [hpt]
    refine int_sum_bdd _ _ (fun x => (((hWte N _ _).mul (hWte N _ _)).mono hHle le_rfl).aestronglyMeasurable)
      ((N : ℝ) * N) (fun x ω => ?_)
      (fun x => hcoord a' _ ((phi_meas x.1.1 x.1.2).mul (phi_meas x.2.1 x.2.2))
        (phi_phi_integral hν x.1.1 x.2.1 x.1.2 x.2.2).1)
    rw [abs_mul]
    exact mul_le_mul (hWtb N ω _ _) (hWtb N ω _ _) (abs_nonneg _) (Nat.cast_nonneg N)
  have hgrint : ∀ N (i : Fin m) (k : Fin n),
      Integrable (fun ω => grad (Wt N ω - Wstar) (M.x t ω) i k) P := by
    intro N i k
    have hgradeq : (fun ω => grad (Wt N ω - Wstar) (M.x t ω) i k)
        = fun ω => ∑ ak : Fin B × (Fin m × Fin n),
            ((B : ℝ)⁻¹ * (Wt N ω - Wstar) ak.2.1 ak.2.2) *
              ((M.x t ω ak.1).1 ak.2.1 * (M.x t ω ak.1).2 ak.2.2 *
                ((M.x t ω ak.1).1 i * (M.x t ω ak.1).2 k)) := by
      funext ω
      rw [grad_entry, Fintype.sum_prod_type, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [resid_expand, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun kk _ => by ring
    rw [hgradeq]
    refine int_sum_bdd _ _ (fun ak => ((measurable_const.mul (hWte N _ _)).mono hHle le_rfl).aestronglyMeasurable)
      ((B : ℝ)⁻¹ * N) (fun ak ω => ?_)
      (fun ak => hcoord ak.1 _ ((phi_meas ak.2.1 ak.2.2).mul (phi_meas i k))
        (phi_phi_integral hν ak.2.1 i ak.2.2 k).1)
    rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg B))]
    exact mul_le_mul_of_nonneg_left (hWtb N ω _ _) (inv_nonneg.mpr (Nat.cast_nonneg B))
  -- pointwise identities between truncated and untruncated quantities
  have hF1 : ∀ N a' ω, c N ω * resid (Wt N ω - Wstar) (M.x t ω a')
      = (A N).indicator (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a')) ω := by
    intro N a' ω
    by_cases hω : ω ∈ A N
    · rw [Set.indicator_of_mem hω, hc_in N ω hω, hWtD N ω hω]
      unfold dNorm
      rw [div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hω, hc_out N ω hω, zero_mul]
  have hF2 : ∀ N a' ω, c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2
      = (A N).indicator (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a') ^ 2) ω := by
    intro N a' ω
    by_cases hω : ω ∈ A N
    · rw [Set.indicator_of_mem hω, hc_in N ω hω, hWtD N ω hω]
      unfold dNorm
      rw [div_pow, inv_pow, div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hω, hc_out N ω hω]
      simp
  have hF3 : ∀ N (i : Fin m) (k : Fin n) ω, c N ω * grad (Wt N ω - Wstar) (M.x t ω) i k
      = (A N).indicator (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k) ω := by
    intro N i k ω
    by_cases hω : ω ∈ A N
    · rw [Set.indicator_of_mem hω, hc_in N ω hω, hWtD N ω hω]
      unfold Gnorm
      rw [Matrix.smul_apply, smul_eq_mul]
    · rw [Set.indicator_of_notMem hω, hc_out N ω hω, zero_mul]
  -- conditional second moment of the truncated, scaled residual
  have hce : ∀ N a', condExp (M.ℱ t) P (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2)
      =ᵐ[P] fun ω => c N ω ^ 2 * (2 * popRisk ν Wstar (Wt N ω)) := by
    intro N a'
    have hprod : Integrable (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) P :=
      (hg2int N a').bdd_mul (((hcm N).pow_const 2).mono hHle le_rfl).aestronglyMeasurable
        (c := ((N : ℝ) + 1) ^ 2) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs, abs_pow]
          exact pow_le_pow_left₀ (abs_nonneg _) (hcb N ω) 2)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := M.ℱ t) (μ := P)
      (f := fun ω => c N ω ^ 2) (g := fun ω => resid (Wt N ω - Wstar) (M.x t ω a') ^ 2)
      ((hcm N).pow_const 2).stronglyMeasurable hprod (hg2int N a')
    filter_upwards [h1, (hmom N a').2.1] with ω e1 e2
    have e1' : condExp (M.ℱ t) P (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) ω
        = c N ω ^ 2 * condExp (M.ℱ t) P
          (fun ω => resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) ω := e1
    rw [e1', e2]
  -- square integrability of the normalized residual
  have hdn2 : ∀ a', Integrable (fun ω => (dNorm C (W t ω - Wstar) (M.x t ω a')) ^ 2) P := by
    intro a'
    refine integrable_of_trunc ((hdm a').pow_const 2) (fun ω => sq_nonneg _) A hAmono ?_
      hAmeas0 (fun N => ?_) (fun N => ?_)
    · intro ω hpos
      apply hcover
      by_contra hR
      push_neg at hR
      have h0 : Real.sqrt (2 * riskSigma C (W t ω - Wstar)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (by linarith)
      have : dNorm C (W t ω - Wstar) (M.x t ω a') = 0 := by
        unfold dNorm; rw [h0, div_zero]
      rw [this] at hpos
      simp at hpos
    · have hprod : Integrable (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) P :=
        (hg2int N a').bdd_mul (((hcm N).pow_const 2).mono hHle le_rfl).aestronglyMeasurable
          (c := ((N : ℝ) + 1) ^ 2) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcb N ω) 2)
      exact hprod.congr (ae_of_all _ fun ω => hF2 N a' ω)
    · have hprod : Integrable (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) P :=
        (hg2int N a').bdd_mul (((hcm N).pow_const 2).mono hHle le_rfl).aestronglyMeasurable
          (c := ((N : ℝ) + 1) ^ 2) (ae_of_all _ fun ω => by
            rw [Real.norm_eq_abs, abs_pow]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcb N ω) 2)
      calc ∫ ω, (A N).indicator (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a') ^ 2) ω ∂P
          = ∫ ω, c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2 ∂P :=
            integral_congr_ae (ae_of_all _ fun ω => (hF2 N a' ω).symm)
        _ = ∫ ω, condExp (M.ℱ t) P
              (fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2) ω ∂P :=
            (integral_condExp hHle).symm
        _ = ∫ ω, c N ω ^ 2 * (2 * popRisk ν Wstar (Wt N ω)) ∂P :=
            integral_congr_ae (hce N a')
        _ ≤ ∫ ω, (1 : ℝ) ∂P := by
            refine integral_mono_of_nonneg
              (ae_of_all _ fun ω => mul_nonneg (sq_nonneg _) (by linarith [hpop0 (Wt N ω)]))
              (integrable_const 1) (ae_of_all _ fun ω => ?_)
            show c N ω ^ 2 * (2 * popRisk ν Wstar (Wt N ω)) ≤ 1
            by_cases hω : ω ∈ A N
            · rw [hpop, hWtD N ω hω, hc_in N ω hω]
              have hR := hRpos N ω hω
              rw [inv_pow, Real.sq_sqrt (by linarith)]
              rw [inv_mul_cancel₀ (by linarith)]
            · rw [hc_out N ω hω]
              simp
        _ = 1 := by simp
  have hdn1 : ∀ a', Integrable (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a')) P := fun a' =>
    ((memLp_two_iff_integrable_sq (hdm a').aestronglyMeasurable).mpr (hdn2 a')).integrable
      one_le_two
  have hGint : ∀ (i : Fin m) (k : Fin n),
      Integrable (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k) P := by
    intro i k
    have hφ2 : Integrable (fun ω => ((M.x t ω a).1 i * (M.x t ω a).2 k) ^ 2) P := by
      have := hcoord a _ ((phi_meas i k).mul (phi_meas i k)) (phi_phi_integral hν i i k k).1
      exact this.congr (ae_of_all _ fun ω => by simp only [sq]; rfl)
    have hterm : ∀ a' : Fin B, Integrable
        (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a') *
          ((M.x t ω a').1 i * (M.x t ω a').2 k)) P := by
      intro a'
      have hφ2' : Integrable (fun ω => ((M.x t ω a').1 i * (M.x t ω a').2 k) ^ 2) P := by
        have := hcoord a' _ ((phi_meas i k).mul (phi_meas i k)) (phi_phi_integral hν i i k k).1
        exact this.congr (ae_of_all _ fun ω => by simp only [sq]; rfl)
      refine Integrable.mono' (((hdn2 a').add hφ2').const_mul (1 / 2 : ℝ))
        (((hdm a').mul ((phi_meas i k).comp (hxa a'))).aestronglyMeasurable) ?_
      refine ae_of_all _ fun ω => ?_
      simp only [Pi.add_apply]
      rw [Real.norm_eq_abs, abs_mul]
      nlinarith [sq_abs (dNorm C (W t ω - Wstar) (M.x t ω a')),
        sq_abs ((M.x t ω a').1 i * (M.x t ω a').2 k),
        sq_nonneg (|dNorm C (W t ω - Wstar) (M.x t ω a')| - |(M.x t ω a').1 i * (M.x t ω a').2 k|)]
    have hfun : (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k)
        = fun ω => (B : ℝ)⁻¹ * ∑ a', dNorm C (W t ω - Wstar) (M.x t ω a') *
            ((M.x t ω a').1 i * (M.x t ω a').2 k) := funext fun ω => Gnorm_entry _ _ _ _ _
    rw [hfun]
    exact (integrable_finsetSum _ fun a' _ => hterm a').const_mul _
  have hcondQ : ∀ (N : ℕ) (a' : Fin B), ∀ᵐ ω ∂P, ω ∈ A N →
      condExp (M.ℱ t) P (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a')) ω = 0 := by
    intro N a'
    have hcg : Integrable (fun ω => c N ω * resid (Wt N ω - Wstar) (M.x t ω a')) P :=
      (hgint N a').bdd_mul ((hcm N).mono hHle le_rfl).aestronglyMeasurable
        (c := (N : ℝ) + 1) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hcb N ω)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := M.ℱ t) (μ := P)
      (f := fun ω => c N ω) (g := fun ω => resid (Wt N ω - Wstar) (M.x t ω a'))
      (hcm N).stronglyMeasurable hcg (hgint N a')
    have h2 := condExp_indicator (m := M.ℱ t) (μ := P) (hdn1 a') (hAmeas N)
    have hfun : (A N).indicator (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a'))
        = fun ω => c N ω * resid (Wt N ω - Wstar) (M.x t ω a') :=
      funext fun ω => (hF1 N a' ω).symm
    rw [hfun] at h2
    filter_upwards [h1, h2, (hmom N a').1] with ω e1 e2 e3 hω
    have e1' : condExp (M.ℱ t) P (fun ω => c N ω * resid (Wt N ω - Wstar) (M.x t ω a')) ω
        = c N ω * condExp (M.ℱ t) P (fun ω => resid (Wt N ω - Wstar) (M.x t ω a')) ω := e1
    rw [e1', e3, Set.indicator_of_mem hω] at e2
    simpa using e2.symm
  have hcondQ2 : ∀ (N : ℕ) (a' : Fin B), ∀ᵐ ω ∂P, ω ∈ A N →
      condExp (M.ℱ t) P (fun ω => (dNorm C (W t ω - Wstar) (M.x t ω a')) ^ 2) ω = 1 := by
    intro N a'
    have h2 := condExp_indicator (m := M.ℱ t) (μ := P) (hdn2 a') (hAmeas N)
    have hfun : (A N).indicator (fun ω => dNorm C (W t ω - Wstar) (M.x t ω a') ^ 2)
        = fun ω => c N ω ^ 2 * resid (Wt N ω - Wstar) (M.x t ω a') ^ 2 :=
      funext fun ω => (hF2 N a' ω).symm
    rw [hfun] at h2
    filter_upwards [h2, hce N a'] with ω e2 e3 hω
    rw [e3, Set.indicator_of_mem hω] at e2
    rw [← e2, hpop, hWtD N ω hω, hc_in N ω hω]
    have hR := hRpos N ω hω
    rw [inv_pow, Real.sq_sqrt (by linarith), inv_mul_cancel₀ (by linarith)]
  have hcondG : ∀ (N : ℕ) (i : Fin m) (k : Fin n), ∀ᵐ ω ∂P, ω ∈ A N →
      condExp (M.ℱ t) P (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k) ω =
        (Real.sqrt (2 * riskSigma C (W t ω - Wstar)))⁻¹ *
          (C.Sout * (W t ω - Wstar) * C.Sin) i k := by
    intro N i k
    have hcg : Integrable (fun ω => c N ω * grad (Wt N ω - Wstar) (M.x t ω) i k) P :=
      (hgrint N i k).bdd_mul ((hcm N).mono hHle le_rfl).aestronglyMeasurable
        (c := (N : ℝ) + 1) (ae_of_all _ fun ω => by
          rw [Real.norm_eq_abs]; exact hcb N ω)
    have h1 := condExp_mul_of_stronglyMeasurable_left (m := M.ℱ t) (μ := P)
      (f := fun ω => c N ω) (g := fun ω => grad (Wt N ω - Wstar) (M.x t ω) i k)
      (hcm N).stronglyMeasurable hcg (hgrint N i k)
    have h2 := condExp_indicator (m := M.ℱ t) (μ := P) (hGint i k) (hAmeas N)
    have hfun : (A N).indicator (fun ω => Gnorm C (W t ω - Wstar) (M.x t ω) i k)
        = fun ω => c N ω * grad (Wt N ω - Wstar) (M.x t ω) i k :=
      funext fun ω => (hF3 N i k ω).symm
    rw [hfun] at h2
    filter_upwards [h1, h2, (hmom N a).2.2 i k] with ω e1 e2 e3 hω
    have e1' : condExp (M.ℱ t) P (fun ω => c N ω * grad (Wt N ω - Wstar) (M.x t ω) i k) ω
        = c N ω * condExp (M.ℱ t) P (fun ω => grad (Wt N ω - Wstar) (M.x t ω) i k) ω := e1
    rw [e1', e3, Set.indicator_of_mem hω] at e2
    rw [← e2, hc_in N ω hω, hWtD N ω hω]
  have hpick : ∀ {Q : Ω → Prop} , (∀ N, ∀ᵐ ω ∂P, ω ∈ A N → Q ω) →
      ∀ᵐ ω ∂P, 0 < riskSigma C (W t ω - Wstar) → Q ω := by
    intro Q hQ
    filter_upwards [ae_all_iff.mpr hQ] with ω hω hR
    obtain ⟨N, hN⟩ := hcover ω hR
    exact hω N hN
  refine ⟨hpick (hcondQ · a), hpick (hcondQ2 · a), fun i k => hpick (hcondG · i k),
    fun i k => ?_⟩
  filter_upwards [hpick (hcondG · i k)] with ω hω hR
  rw [hω hR, rotAhat_eq, Matrix.smul_apply, smul_eq_mul]

end Muon.Setup
