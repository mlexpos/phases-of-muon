import Muon.Dynamics.Corollaries
import Muon.Dynamics.Concentration
import Muon.Dynamics.Diffuse
import Muon.Dynamics.Chains
import Muon.External.Certificates

/-!
# Appendix E, work package L-E.12: the block residual

Snapshot `cr-2026-10-23`. Source: `sections/05-dynamics/section.tex`, `lem:app-dyn-block` (ll. 2156–2165) and its
exact block identity `eqn:app-dyn-block-identity` (l. 2182). Card: `sections/05-dynamics/CARD.md` §2, §3 and the
L-E.12 row of §5. Interface only: every proof is `sorry`.

Representation choices:
* Framework. The law-level `DynHyp` of `Muon.Dynamics.Corollaries` (one probability space `P`, dimensions `k`) carries
  (H1)–(H4); the actual spectral measures are `actMeas`, the error path `errPath`, the coefficients `DynCoeff` with
  `IsActualCoeff`, exactly as in `cor:app-dyn-half`. The source's standing "along a sequence with `B → ∞`" is
  `ProportionalRegime.B_top` inside `DynHyp.regime`.
* Coefficients. `𝔡` and `ζ` are the drift kernel and forcing measure of C and D at `ϱ`, so the statement takes
  `hc : IsActualCoeff cert (F k) (S k) (c k)`. Without it the claim is false for arbitrary coefficients.
* Certificates. The proof uses the Gaussian operator-norm tail (through `IsActualCoeff` and the joint forcing of D),
  the `L⁶` operator-norm bound (batches), the Gaussian Poincaré inequality (prefix, response), the Gaussian
  quadratic-form moments (stationary tangent). Each is an explicit
  argument of `Muon.External`.
* Stopping. `t_{b_c} = L · b_c` with `b_c = inf {b : Δ_{t_b} ∉ 𝒜}` (`blockExitIdx`, valued in `ℕ∞`, `⊤` if none);
  the macro stop `τ ∧ τ_c` is `stopMacro`, with `τ_c = ⊤ ↦ +∞`.
* Probability. "In probability" is `∀ ε > 0, P {sup > ε} → 0` with the supremum taken in `ℝ≥0∞`
  (`⨆ τ ∈ [0,T], ENNReal.ofReal …`), so no `sSup` junk value appears. Integrability of the integrands is a
  conclusion conjunct.
* Identity. `eqn:app-dyn-block-identity` is stated in the sample-level `DynSetup` of `Muon.Dynamics.Transport`
  (its `dynUpd`, `dynStatSum`, `dynSumErr`, `dynVbar` are reused). The forcing measure `𝔉_L(D)` is the finite-time
  measure `Muon.Volatility.finiteTimeMeasure` at a frozen model whose state is `Â(D)`; the identity takes a function
  `FL` and the hypothesis `hFL` pinning `FL D` to that measure for every frozen model with the state `Â(D)`.
  Conditional expectations of matrices use `Muon.Foundations.condExpMat`; event indicators are inside `condExp`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set Matrix
open Muon Muon.Setup

noncomputable section

namespace Muon.Dynamics

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
  {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)}

/-! ## Helpers -/

/-- The tensor test function `f ⊗ g` on `ℝ × ℝ`, `(μ, λ) ↦ f(μ) g(λ)` (`section.tex`, `f⊗g` of ll. 2156–2165). -/
def tensorFG (f g : ℝ → ℝ) : ℝ × ℝ → ℝ := fun x => f x.1 * g x.2

/-- The block index `b_c = inf {b ≥ 0 : Δ_{t_b} ∉ 𝒜}` of `lem:app-dyn-diffuse`, with `t_b = bL` (`ℕ∞`-valued, `⊤` if
the process never leaves `𝒜` at block starts), for the error path `errPath` of `DynHyp`. Snapshot `cr-2026-10-23`. -/
def blockExitIdx (hyp : DynHyp p P m n B C) (k : ℕ) (ω : Ω) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : errPath hyp k (b * blockLen (B k)) ω ∉ admA p (C k)), (b : ℕ∞)

/-- The stopped macro time `τ ∧ τ_c` with `τ_c = t_{b_c}/B = L · b_c / B` (`section.tex` l. 2158); `τ_c = +∞` when
`b_c = ⊤`. -/
def stopMacro (L Bn : ℕ) (b : ℕ∞) (τ : ℝ) : ℝ :=
  if b = ⊤ then τ else min τ ((L : ℝ) * (b.toNat : ℝ) / (Bn : ℝ))

/-- The residual inside the supremum of `lem:app-dyn-block`:
`∫ f⊗g dχ^act(τ∧τ_c) − ∫ f⊗g dχ^act(0) − ∫_0^{τ∧τ_c} ∫ f⊗g dF_B(χ^act(σ)) dσ`, with `F_B` the weak field
`fieldOp` of `eqn:app-dyn-field` built from `c k` (`𝔡`, `ζ`). -/
def blockResidual (hyp : DynHyp p P m n B C) (S : ∀ k : ℕ, SpectralData (C k))
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k)) (f g : ℝ → ℝ) (k : ℕ) (ω : Ω) (τ : ℝ) : ℝ :=
  |(∫ x, tensorFG f g x ∂(actMeas hyp S k ω (stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ)))
    - (∫ x, tensorFG f g x ∂(actMeas hyp S k ω 0))
    - ∫ σ in (0 : ℝ)..(stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ),
        fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ) (tensorFG f g)|

/-! ## `lem:app-dyn-block` -/


/-! ## `eqn:app-dyn-block-identity` -/

private lemma block_delta_sum (p : DynParams) {m n B : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B) (t L : ℕ) (ω : Ω) :
    dynDelta S (t + L) ω = dynDelta S t ω -
      (p.h / (B : ℝ)) • ∑ r ∈ Finset.range L, dynUpd S (t + r) ω := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Nat.add_succ]
    change Muon.Setup.devRand S.C S.alg (dynStart S) (dynBatch S) (t + L + 1) ω = _
    rw [Muon.Setup.devRand_succ]
    change dynDelta S (t + L) ω - S.alg.η (t + L) • dynUpd S (t + L) ω = _
    rw [ih, S.alg_η]
    simp only [Finset.sum_range_succ, smul_add]
    module

private lemma block_upd_decomposition (p : DynParams) {m n B : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) :
    (∑ r ∈ Finset.range (blockLen B), dynUpd S (t + r) ω) =
      dynStatSum p S t ω + dynSumErr p S t ω := by
  simp only [dynStatSum, dynSumErr]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _
  module

private lemma block_frobIP_sum_right {m n : ℕ} {ι : Type*}
    (X : Mat m n) (s : Finset ι) (U : ι → Mat m n) :
    frobIP X (∑ r ∈ s, U r) = ∑ r ∈ s, frobIP X (U r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [frobIP]
  | @insert r s hr ih =>
    simp only [Finset.sum_insert hr]
    rw [show frobIP X (U r + ∑ x ∈ s, U x) =
        frobIP X (U r) + frobIP X (∑ x ∈ s, U x) by
      unfold frobIP
      simp only [Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]]
    rw [ih]

private lemma block_frobIP_comm {m n : ℕ} (X Y : Mat m n) : frobIP X Y = frobIP Y X := by
  unfold frobIP
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]

private lemma block_wfg_self_adjoint {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n)
    (X Y : Mat m n) : frobIP (wfg f g C X) Y = frobIP X (wfg f g C Y) := by
  unfold wfg frobIP
  have hf : (cfc f C.Sout)ᵀ = cfc f C.Sout := by
    have h : IsSelfAdjoint (cfc f C.Sout) := cfc_predicate f C.Sout
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hg : (cfc g C.Sin)ᵀ = cfc g C.Sin := by
    have h : IsSelfAdjoint (cfc g C.Sin) := cfc_predicate g C.Sin
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  simp only [Matrix.transpose_mul, hf, hg, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

private lemma block_Xfg_quadratic {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n)
    (D U : Mat m n) (a : ℝ) :
    Xfg f g C (D - a • U) - Xfg f g C D =
      -2 * a * frobIP (wfg f g C D) U + a ^ 2 * frobIP U (wfg f g C U) := by
  unfold Xfg wfg frobIP
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  have hf : (cfc f C.Sout)ᵀ = cfc f C.Sout := by
    have h : IsSelfAdjoint (cfc f C.Sout) := cfc_predicate f C.Sout
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hg : (cfc g C.Sin)ᵀ = cfc g C.Sin := by
    have h : IsSelfAdjoint (cfc g C.Sin) := cfc_predicate g C.Sin
    have h' := h.star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h'
  have hleft : ((cfc f C.Sout * D * cfc g C.Sin) * Uᵀ).trace =
      (D * (cfc f C.Sout * U * cfc g C.Sin)ᵀ).trace := by
    simp only [Matrix.transpose_mul, hf, hg, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have hcomm : (U * (cfc f C.Sout * D * cfc g C.Sin)ᵀ).trace =
      (D * (cfc f C.Sout * U * cfc g C.Sin)ᵀ).trace := by
    rw [← Matrix.trace_transpose]
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, hf, hg, Matrix.mul_assoc] using hleft
  rw [hleft, hcomm]
  ring

private lemma block_pointwise_identity (p : DynParams) {m n B : ℕ} {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} (S : DynSetup p P m n B)
    (f g : ℝ → ℝ) (t : ℕ) (ω : Ω) :
    Xfg f g S.C (dynDelta S (t + blockLen B) ω) - Xfg f g S.C (dynDelta S t ω) =
      -2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (blockLen B),
        frobIP (wfg f g S.C (dynDelta S t ω)) (dynUpd S (t + r) ω) +
      (p.h / (B : ℝ)) ^ 2 *
        (frobIP (dynStatSum p S t ω) (wfg f g S.C (dynStatSum p S t ω)) +
          2 * frobIP (dynStatSum p S t ω) (wfg f g S.C (dynSumErr p S t ω)) +
          frobIP (dynSumErr p S t ω) (wfg f g S.C (dynSumErr p S t ω))) := by
  rw [block_delta_sum, block_Xfg_quadratic, block_upd_decomposition]
  have hsum := block_frobIP_sum_right (wfg f g S.C (dynDelta S t ω))
    (Finset.range (blockLen B))
    (fun r => dynUpd S (t + r) ω)
  have hlin : frobIP (wfg f g S.C (dynDelta S t ω))
      (dynStatSum p S t ω + dynSumErr p S t ω) =
      ∑ r ∈ Finset.range (blockLen B),
        frobIP (wfg f g S.C (dynDelta S t ω)) (dynUpd S (t + r) ω) := by
    rw [← block_upd_decomposition p S t ω]
    exact hsum
  rw [hlin]
  have hcross : frobIP (dynSumErr p S t ω) (wfg f g S.C (dynStatSum p S t ω)) =
      frobIP (dynStatSum p S t ω) (wfg f g S.C (dynSumErr p S t ω)) := by
    rw [block_frobIP_comm]
    exact block_wfg_self_adjoint f g S.C _ _
  unfold wfg frobIP at hcross ⊢
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.transpose_add, Matrix.trace_add] at hcross ⊢
  rw [hcross]
  ring

/-! ### Helpers for `eqn_app_dyn_block_identity` -/

private lemma block_aeval_diag {k : ℕ} (d : Fin k → ℝ) (q : Polynomial ℝ) :
    Polynomial.aeval (Matrix.diagonal d) q = Matrix.diagonal (fun i => q.eval (d i)) := by
  have h := Polynomial.aeval_algHom_apply (Matrix.diagonalAlgHom ℝ (n := Fin k) (α := ℝ)) d q
  have h2 : Polynomial.aeval d q = fun i => q.eval (d i) := by
    funext i
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℝ (fun _ : Fin k => ℝ) i) d q
    simp [Polynomial.aeval_def] at this ⊢
  rw [h2] at h
  exact h

private lemma block_aeval_conj {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (A : Mat k k) (q : Polynomial ℝ) :
    Polynomial.aeval (U * A * Uᵀ) q = U * Polynomial.aeval A q * Uᵀ := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  let u : unitary (Mat k k) := ⟨U, by
    rw [Unitary.mem_iff]
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, hU, hUU]⟩
  let φ : Mat k k →ₐ[ℝ] Mat k k := (Unitary.conjStarAlgAut ℝ (Mat k k) u).toAlgEquiv.toAlgHom
  have h := Polynomial.aeval_algHom_apply φ A q
  simpa [φ, Unitary.conjStarAlgAut_apply, u, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] using h

private lemma block_selfadj_conj {k : ℕ} (U : Mat k k) (d : Fin k → ℝ) :
    IsSelfAdjoint (U * Matrix.diagonal d * Uᵀ) := by
  rw [IsSelfAdjoint, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [Matrix.transpose_mul, Matrix.mul_assoc]

private lemma block_spectrum_subset {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ) :
    spectrum ℝ (U * Matrix.diagonal d * Uᵀ) ⊆ Set.range d := by
  intro x hx
  by_contra hxr
  apply hx
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  have hne : ∀ i, x - d i ≠ 0 := fun i h => hxr ⟨i, by linarith⟩
  rw [spectrum.mem_resolventSet_iff]
  have hA : algebraMap ℝ (Mat k k) x - U * Matrix.diagonal d * Uᵀ =
      U * Matrix.diagonal (fun i => x - d i) * Uᵀ := by
    have h1 : algebraMap ℝ (Mat k k) x = U * (x • (1 : Mat k k)) * Uᵀ := by
      simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.smul_mul, hUU]
    rw [h1, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [Matrix.diagonal_apply_ne _ h, h]
  rw [hA]
  have hdd : ∀ (a b : Fin k → ℝ), (∀ i, a i * b i = 1) →
      U * Matrix.diagonal a * Uᵀ * (U * Matrix.diagonal b * Uᵀ) = 1 := by
    intro a b hab
    calc U * Matrix.diagonal a * Uᵀ * (U * Matrix.diagonal b * Uᵀ)
        = U * Matrix.diagonal a * (Uᵀ * U) * Matrix.diagonal b * Uᵀ := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hU, Matrix.mul_one, Matrix.mul_assoc U, Matrix.diagonal_mul_diagonal]
          have : (fun i => a i * b i) = fun _ => (1 : ℝ) := funext hab
          rw [this]
          simp [hUU]
  refine isUnit_iff_exists.mpr ⟨U * Matrix.diagonal (fun i => (x - d i)⁻¹) * Uᵀ,
    hdd _ _ (fun i => mul_inv_cancel₀ (hne i)), hdd _ _ (fun i => inv_mul_cancel₀ (hne i))⟩

private lemma block_cfc_spectral {k : ℕ} (U : Mat k k) (hU : Uᵀ * U = 1) (d : Fin k → ℝ) (f : ℝ → ℝ) :
    cfc f (U * Matrix.diagonal d * Uᵀ) = U * Matrix.diagonal (fun i => f (d i)) * Uᵀ := by
  classical
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℝ, ∀ i, q.eval (d i) = f (d i) := by
    refine ⟨Lagrange.interpolate (Finset.univ.image d) id f, fun i => ?_⟩
    exact Lagrange.eval_interpolate_at_node f Function.injective_id.injOn (Finset.mem_image_of_mem d (Finset.mem_univ i))
  have hcongr : cfc f (U * Matrix.diagonal d * Uᵀ) = cfc (fun x => q.eval x) (U * Matrix.diagonal d * Uᵀ) := by
    apply cfc_congr
    intro x hx
    obtain ⟨i, rfl⟩ := block_spectrum_subset U hU d hx
    exact (hq i).symm
  rw [hcongr, cfc_polynomial q _ (block_selfadj_conj U d), block_aeval_conj U hU, block_aeval_diag]
  simp only [hq]

private lemma block_G_spectral {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (Y : Mat m n) :
    frobIP Y (wfg f g C Y) =
      ∑ i, ∑ j, f (SP.μ i) * g (SP.lam j) * ((SP.uOutᵀ * Y * SP.vIn) i j) ^ 2 := by
  have hU := SP.huOut
  have hV := SP.hvIn
  have hUU : SP.uOut * SP.uOutᵀ = 1 := mul_eq_one_comm.mp hU
  have hVV : SP.vIn * SP.vInᵀ = 1 := mul_eq_one_comm.mp hV
  set Z := SP.uOutᵀ * Y * SP.vIn with hZ
  have hY : Y = SP.uOut * Z * SP.vInᵀ := by
    rw [hZ]
    calc Y = (SP.uOut * SP.uOutᵀ) * Y * (SP.vIn * SP.vInᵀ) := by rw [hUU, hVV]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hW : wfg f g C Y = SP.uOut * (Matrix.diagonal (fun i => f (SP.μ i)) * Z *
      Matrix.diagonal (fun j => g (SP.lam j))) * SP.vInᵀ := by
    unfold wfg
    rw [Sout_eq_spectral SP, Sin_eq_spectral SP, block_cfc_spectral _ hU, block_cfc_spectral _ hV]
    conv_lhs => rw [hY]
    calc _ = SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * (SP.uOutᵀ * SP.uOut) * Z *
          (SP.vInᵀ * SP.vIn) * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [hW]
  conv_lhs => rw [hY]
  unfold frobIP
  have hdf : (Matrix.diagonal (fun i => f (SP.μ i)))ᵀ = Matrix.diagonal (fun i => f (SP.μ i)) :=
    Matrix.diagonal_transpose _
  have hdg : (Matrix.diagonal (fun j => g (SP.lam j)))ᵀ = Matrix.diagonal (fun j => g (SP.lam j)) :=
    Matrix.diagonal_transpose _
  have h1 : (SP.uOut * Z * SP.vInᵀ * (SP.uOut * (Matrix.diagonal (fun i => f (SP.μ i)) * Z *
      Matrix.diagonal (fun j => g (SP.lam j))) * SP.vInᵀ)ᵀ).trace =
      (Matrix.diagonal (fun i => f (SP.μ i)) * Z * Matrix.diagonal (fun j => g (SP.lam j)) * Zᵀ).trace := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hdf, hdg]
    have hconj : ∀ X : Mat m m, (SP.uOut * X * SP.uOutᵀ).trace = X.trace := by
      intro X
      rw [Matrix.trace_mul_comm (SP.uOut * X) SP.uOutᵀ, ← Matrix.mul_assoc, hU, Matrix.one_mul]
    calc _ = (SP.uOut * (Z * (SP.vInᵀ * SP.vIn) * Matrix.diagonal (fun j => g (SP.lam j)) * Zᵀ *
          Matrix.diagonal (fun i => f (SP.μ i))) * SP.uOutᵀ).trace := by
            congr 1; simp only [Matrix.mul_assoc]
      _ = _ := by
            rw [hconj, hV, Matrix.mul_one, Matrix.trace_mul_comm]
            simp only [Matrix.mul_assoc]
  rw [h1, trace_diag_form]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma block_frobIP_eq_sum {m n : ℕ} (X Y : Mat m n) :
    frobIP X Y = ∑ i, ∑ j, X i j * Y i j := by
  unfold frobIP
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]

private lemma block_Xfg_cont {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) :
    Continuous (Xfg f g C) := by
  unfold Xfg wfg
  simp_rw [block_frobIP_eq_sum]
  fun_prop

private lemma block_frobIP_cont {m n : ℕ} :
    Continuous (fun x : Mat m n × Mat m n => frobIP x.1 x.2) := by
  simp_rw [block_frobIP_eq_sum]
  fun_prop

section frozen

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {m n B : ℕ}

private lemma block_Qmeas (ϱ : ℝ) (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp (measurable_const.prodMk measurable_id :
    Measurable (fun K : Mat m n => ((⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)), K)))

private lemma block_Qpath_meas (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    Measurable (fun (x : ℤ → Mat m n) (s : ℤ) => Q ϱ (x s)) :=
  Measurable.of_eval fun s => (block_Qmeas ϱ hϱ).comp (measurable_pi_apply s)

/-- path of frozen updates is a.e. measurable. -/
private lemma block_updpath_aem [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) :
    AEMeasurable (fun ω (s : ℤ) => frozenUpd F S' ϱ s ω) P' :=
  (block_Qpath_meas ϱ hϱ).comp_aemeasurable (lem_app_setup_ema_law_ii F S').2.1

private lemma block_updpath_stationary [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (k : ℤ) :
    P'.map (fun ω (s : ℤ) => frozenUpd F S' ϱ (s + k) ω) =
      P'.map (fun ω (s : ℤ) => frozenUpd F S' ϱ s ω) := by
  have h1 := (lem_app_setup_ema_law_ii F S').2
  have hA : AEMeasurable (fun ω (s : ℤ) => frozenBuf F S' s ω) P' := h1.1
  have hB : AEMeasurable (fun ω (s : ℤ) => frozenBuf F S' (s + k) ω) P' := by
    have : Measurable (fun (x : ℤ → Mat m n) (s : ℤ) => x (s + k)) :=
      Measurable.of_eval fun s => measurable_pi_apply (s + k)
    exact this.comp_aemeasurable hA
  have e1 := h1.2 k
  have hg := block_Qpath_meas (m := m) (n := n) ϱ hϱ
  have c1 : (fun ω (s : ℤ) => frozenUpd F S' ϱ (s + k) ω) =
      (fun (x : ℤ → Mat m n) (s : ℤ) => Q ϱ (x s)) ∘ (fun ω (s : ℤ) => frozenBuf F S' (s + k) ω) := rfl
  have c2 : (fun ω (s : ℤ) => frozenUpd F S' ϱ s ω) =
      (fun (x : ℤ → Mat m n) (s : ℤ) => Q ϱ (x s)) ∘ (fun ω (s : ℤ) => frozenBuf F S' s ω) := rfl
  rw [c1, c2, ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hB,
    ← AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hA, e1]

/-- integral invariance under time shift for measurable functionals of the update path. -/
private lemma block_updpath_integral_shift [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (k : ℤ) (Ψ : (ℤ → Mat m n) → ℝ)
    (hΨ : Measurable Ψ) :
    ∫ ω, Ψ (fun s => frozenUpd F S' ϱ (s + k) ω) ∂P' = ∫ ω, Ψ (fun s => frozenUpd F S' ϱ s ω) ∂P' := by
  have hA := block_updpath_aem F S' ϱ hϱ
  have hB : AEMeasurable (fun ω (s : ℤ) => frozenUpd F S' ϱ (s + k) ω) P' := by
    have : Measurable (fun (x : ℤ → Mat m n) (s : ℤ) => x (s + k)) :=
      Measurable.of_eval fun s => measurable_pi_apply (s + k)
    exact this.comp_aemeasurable hA
  have e := block_updpath_stationary F S' ϱ hϱ k
  calc ∫ ω, Ψ (fun s => frozenUpd F S' ϱ (s + k) ω) ∂P'
      = ∫ x, Ψ x ∂(P'.map (fun ω (s : ℤ) => frozenUpd F S' ϱ (s + k) ω)) :=
        (integral_map hB hΨ.aestronglyMeasurable).symm
    _ = ∫ x, Ψ x ∂(P'.map (fun ω (s : ℤ) => frozenUpd F S' ϱ s ω)) := by rw [e]
    _ = _ := integral_map hA hΨ.aestronglyMeasurable

end frozen

section bnd

private lemma block_bound_of_cont {m n : ℕ} (h : Mat m n → ℝ) (hc : Continuous h) (R : ℝ) :
    ∃ K : ℝ, ∀ Y : Mat m n, (∀ i j, |Y i j| ≤ R) → |h Y| ≤ K := by
  have hK : IsCompact (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn (f := h) hc.continuousOn
  refine ⟨K, fun Y hY => ?_⟩
  have hmem : Y ∈ (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) := by
    intro i _ j _
    exact abs_le.mp (hY i j)
  simpa using hK' Y hmem

private lemma block_integrable_cont {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {m n : ℕ} {X : Ω' → Mat m n} (hX : AEMeasurable X P') (R : ℝ)
    (hb : ∀ ω i j, |X ω i j| ≤ R) (h : Mat m n → ℝ) (hc : Continuous h) :
    Integrable (fun ω => h (X ω)) P' := by
  obtain ⟨K, hK⟩ := block_bound_of_cont h hc R
  refine Integrable.of_bound (C := K) (hc.measurable.comp_aemeasurable hX).aestronglyMeasurable ?_
  exact ae_of_all _ fun ω => by simpa using hK (X ω) (hb ω)

private lemma block_abs_entry_le_fro {m n : ℕ} (A : Mat m n) (i : Fin m) (j : Fin n) :
    |A i j| ≤ fro A := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖A i j‖ ^ 2 ≤ ∑ j', ‖A i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖A i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖A i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖A i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖A i' j'‖ ^ 2) (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)
  simpa [Real.norm_eq_abs, sq_abs] using h1.trans h2

private lemma block_Q_entry_bound {m n : ℕ} (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (K : Mat m n) (i : Fin m) (j : Fin n) :
    |Q ϱ K i j| ≤ (m : ℝ) + 1 := by
  obtain ⟨_, hf, hk, _⟩ := lem_app_setup_filter_i ϱ hϱ K
  have h1 := block_abs_entry_le_fro (Q ϱ K) i j
  have hr : (K.rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hk.trans (min_le_left m n)
  have h2 : fro (Q ϱ K) ^ 2 ≤ (m : ℝ) := hf.trans hr
  have h0 : 0 ≤ fro (Q ϱ K) := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (fro (Q ϱ K) - 1)]

end bnd

section frozen2

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {m n B : ℕ}

private lemma block_upd_entry_bound (F : FrozenParams m n B) (S' : FrozenSamples P' m n B) (ϱ : ℝ)
    (hϱ : 0 ≤ ϱ) (s : ℤ) (ω : Ω') (i : Fin m) (j : Fin n) :
    |frozenUpd F S' ϱ s ω i j| ≤ (m : ℝ) + 1 :=
  block_Q_entry_bound ϱ hϱ _ i j

private lemma block_upd_aem [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (s : ℤ) :
    AEMeasurable (fun ω => frozenUpd F S' ϱ s ω) P' :=
  (measurable_pi_apply s).comp_aemeasurable (block_updpath_aem F S' ϱ hϱ)

private lemma block_upd_mean_shift [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (k : ℤ) :
    Muon.mean P' (frozenUpd F S' ϱ k) = Muon.mean P' (frozenUpd F S' ϱ 0) := by
  ext i j
  have h := block_updpath_integral_shift F S' ϱ hϱ k (fun x => x 0 i j)
    (by fun_prop)
  simpa [Muon.mean] using h

private lemma block_Icc_sum {M : Type*} [AddCommMonoid M] (h : ℤ → M) (L : ℕ) :
    ∑ s ∈ Finset.Icc (1 : ℤ) (L : ℤ), h s = ∑ r ∈ Finset.range L, h (1 + (r : ℤ)) := by
  refine Finset.sum_nbij' (fun s => (s - 1).toNat) (fun r => 1 + (r : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    simp only [Finset.mem_range]
    omega
  · intro r hr
    simp only [Finset.mem_range] at hr
    simp only [Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    show 1 + (((s - 1).toNat : ℕ) : ℤ) = s
    omega
  · intro r hr
    show (((1 + (r : ℤ)) - 1).toNat) = r
    omega
  · intro s hs
    simp only [Finset.mem_Icc] at hs
    have : 1 + (((s - 1).toNat : ℕ) : ℤ) = s := by omega
    rw [this]

end frozen2

section frozen3

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} {m n B : ℕ}

private lemma block_frozen_second_moment [IsProbabilityMeasure P'] (F : FrozenParams m n B)
    (S' : FrozenSamples P' m n B) (SP : SpectralData F.C) (ϱ : ℝ) (hϱ : 0 < ϱ) (f g : ℝ → ℝ)
    (L : ℕ) (hL : 0 < L) (t : ℤ) :
    ∫ ω, Xfg f g F.C (∑ r ∈ Finset.range L, frozenUpd F S' ϱ (t + r) ω) ∂P' =
      (L : ℝ) ^ 2 * Xfg f g F.C (Muon.mean P' (frozenUpd F S' ϱ t)) +
      (L : ℝ) * (B : ℝ) *
        (Muon.Volatility.finiteTimeMeasure F S' SP L ϱ).sum (fun x r => f x.1 * g x.2 * r) := by
  have hϱ0 := hϱ.le
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  -- Step 1: shift to times `1, …, L`
  have hshift : ∫ ω, Xfg f g F.C (∑ r ∈ Finset.range L, frozenUpd F S' ϱ (t + r) ω) ∂P' =
      ∫ ω, Xfg f g F.C (∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω) ∂P' := by
    have hmeas : Measurable (fun x : ℤ → Mat m n => Xfg f g F.C (∑ r ∈ Finset.range L, x (1 + (r : ℤ)))) :=
      (block_Xfg_cont f g F.C).measurable.comp
        (Finset.measurable_sum _ fun r _ => measurable_pi_apply _)
    have := block_updpath_integral_shift F S' ϱ hϱ0 (t - 1) _ hmeas
    have e : ∀ r : ℕ, (1 + (r : ℤ)) + (t - 1) = t + r := fun r => by ring
    simpa only [e] using this
  rw [hshift]
  -- Step 2: the common mean
  set m0 : Mat m n := Muon.mean P' (frozenUpd F S' ϱ 0) with hm0
  have hmean : ∀ s : ℤ, Muon.mean P' (frozenUpd F S' ϱ s) = m0 := fun s => block_upd_mean_shift F S' ϱ hϱ0 s
  rw [hmean t]
  -- bounds and measurability of the pieces
  have hm0b : ∀ i j, |m0 i j| ≤ (m : ℝ) + 1 := by
    intro i j
    have := norm_integral_le_of_norm_le_const (μ := P') (f := fun ω => frozenUpd F S' ϱ 0 ω i j)
      (C := (m : ℝ) + 1) (ae_of_all _ fun ω => by
        simpa [Real.norm_eq_abs] using block_upd_entry_bound F S' ϱ hϱ0 0 ω i j)
    simpa [hm0, Muon.mean, Real.norm_eq_abs] using this
  have hUb : ∀ (r : ℕ) ω i j, |frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j| ≤ (m : ℝ) + 1 :=
    fun r ω i j => block_upd_entry_bound F S' ϱ hϱ0 _ ω i j
  set Y : Ω' → Mat m n := fun ω => ∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω - (L : ℝ) • m0 with hY
  have hYaem : AEMeasurable Y P' := by
    exact (Finset.aemeasurable_fun_sum _ fun r _ => block_upd_aem F S' ϱ hϱ0 _).sub_const _
  have hYb : ∀ ω i j, |Y ω i j| ≤ 2 * (L : ℝ) * ((m : ℝ) + 1) := by
    intro ω i j
    have h1 : |∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j| ≤ (L : ℝ) * ((m : ℝ) + 1) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ r ∈ Finset.range L, |frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j|
          ≤ ∑ r ∈ Finset.range L, ((m : ℝ) + 1) := Finset.sum_le_sum fun r _ => hUb r ω i j
        _ = (L : ℝ) * ((m : ℝ) + 1) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have h2 : |(L : ℝ) * m0 i j| ≤ (L : ℝ) * ((m : ℝ) + 1) := by
      rw [abs_mul, abs_of_pos hLpos]
      exact mul_le_mul_of_nonneg_left (hm0b i j) hLpos.le
    simp only [hY, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    calc _ ≤ |∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j| + |(L : ℝ) * m0 i j| := abs_sub _ _
      _ ≤ _ := by linarith
  -- Step 3: algebra
  have halg : ∀ ω, Xfg f g F.C (∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω) =
      Xfg f g F.C (Y ω) + 2 * (L : ℝ) * frobIP (Y ω) (wfg f g F.C m0) + (L : ℝ) ^ 2 * Xfg f g F.C m0 := by
    intro ω
    have hq := block_Xfg_quadratic f g F.C (Y ω) m0 (-(L : ℝ))
    have e : Y ω - (-(L : ℝ)) • m0 = ∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω := by
      simp only [hY, neg_smul, sub_neg_eq_add]; abel
    rw [e] at hq
    have hsa := block_wfg_self_adjoint f g F.C (Y ω) m0
    rw [hsa] at hq
    have hX : Xfg f g F.C m0 = frobIP m0 (wfg f g F.C m0) := rfl
    rw [hX]
    linear_combination hq
  -- integrability
  have hentint : ∀ (r : ℕ) (i : Fin m) (j : Fin n),
      Integrable (fun ω => frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j) P' := fun r i j =>
    block_integrable_cont (block_upd_aem F S' ϱ hϱ0 _) _ (hUb r) (fun A => A i j) (by fun_prop)
  have hYentint : ∀ i j, Integrable (fun ω => Y ω i j) P' := fun i j =>
    block_integrable_cont hYaem _ hYb (fun A => A i j) (by fun_prop)
  have hYent : ∀ i j, ∫ ω, Y ω i j ∂P' = 0 := by
    intro i j
    have e : ∀ ω, Y ω i j = ∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j - (L : ℝ) * m0 i j := by
      intro ω
      simp only [hY, Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    simp_rw [e]
    rw [integral_sub (integrable_finset_sum _ fun r _ => hentint r i j) (integrable_const _),
      integral_finset_sum _ fun r _ => hentint r i j]
    have : ∀ r ∈ Finset.range L, ∫ ω, frozenUpd F S' ϱ (1 + (r : ℤ)) ω i j ∂P' = m0 i j := by
      intro r _
      have := congrFun (congrFun (hmean (1 + (r : ℤ))) i) j
      simpa [Muon.mean] using this
    rw [Finset.sum_congr rfl this]
    simp
  set c := wfg f g F.C m0 with hc
  have hlin : ∫ ω, frobIP (Y ω) c ∂P' = 0 := by
    have h1 : ∀ i : Fin m, ∫ ω, ∑ j : Fin n, Y ω i j * c i j ∂P' = 0 := by
      intro i
      rw [integral_finset_sum Finset.univ (fun j _ => (hYentint i j).mul_const (c i j))]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [integral_mul_const, hYent]; simp
    simp_rw [block_frobIP_eq_sum]
    have hI : ∀ i : Fin m, Integrable (fun ω => ∑ j : Fin n, Y ω i j * c i j) P' := fun i =>
      integrable_finset_sum _ fun j _ => (hYentint i j).mul_const (c i j)
    rw [integral_finset_sum Finset.univ (fun i _ => hI i)]
    exact Finset.sum_eq_zero fun i _ => h1 i
  have hint1 : Integrable (fun ω => Xfg f g F.C (Y ω)) P' :=
    block_integrable_cont hYaem _ hYb _ (block_Xfg_cont f g F.C)
  have hint2 : Integrable (fun ω => frobIP (Y ω) c) P' :=
    block_integrable_cont hYaem _ hYb (fun Z => frobIP Z c) (by simp_rw [block_frobIP_eq_sum]; fun_prop)
  have hsplit : ∫ ω, Xfg f g F.C (∑ r ∈ Finset.range L, frozenUpd F S' ϱ (1 + (r : ℤ)) ω) ∂P' =
      ∫ ω, Xfg f g F.C (Y ω) ∂P' + (L : ℝ) ^ 2 * Xfg f g F.C m0 := by
    simp_rw [halg]
    have hi12 : Integrable (fun ω => Xfg f g F.C (Y ω) + 2 * (L : ℝ) * frobIP (Y ω) c) P' :=
      hint1.add (hint2.const_mul (2 * (L : ℝ)))
    rw [integral_add hi12 (integrable_const _), integral_add hint1 (hint2.const_mul (2 * (L : ℝ))),
      integral_const_mul, hlin]
    simp
  rw [hsplit]
  -- spectral evaluation of the centred part
  have hcent : ∀ ω, ∑ s ∈ Finset.Icc (1 : ℤ) (L : ℤ), Muon.Volatility.centredUpd F S' ϱ s ω = Y ω := by
    intro ω
    rw [block_Icc_sum]
    simp only [Muon.Volatility.centredUpd, hmean, hY]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, Nat.cast_smul_eq_nsmul ℝ]
  have hspec : ∫ ω, Xfg f g F.C (Y ω) ∂P' =
      (L : ℝ) * (B : ℝ) * (Muon.Volatility.finiteTimeMeasure F S' SP L ϱ).sum
        (fun x r => f x.1 * g x.2 * r) := by
    have hZint : ∀ i j, Integrable (fun ω => f (SP.μ i) * g (SP.lam j) * ((SP.uOutᵀ * Y ω * SP.vIn) i j) ^ 2) P' := by
      intro i j
      refine Integrable.const_mul ?_ _
      exact block_integrable_cont hYaem _ hYb (fun A => ((SP.uOutᵀ * A * SP.vIn) i j) ^ 2)
        (by simp_rw [Matrix.mul_apply]; fun_prop)
    have hftm : (Muon.Volatility.finiteTimeMeasure F S' SP L ϱ).sum (fun x r => f x.1 * g x.2 * r) =
        ∑ i : Fin m, ∑ j : Fin n, f (SP.μ i) * g (SP.lam j) *
          (((B : ℝ) * L)⁻¹ * ∫ ω, ((SP.uOutᵀ * Y ω * SP.vIn) i j) ^ 2 ∂P') := by
      unfold Muon.Volatility.finiteTimeMeasure
      simp_rw [hcent]
      rw [← Finsupp.sum_finset_sum_index (fun a => mul_zero _) (fun a b1 b2 => mul_add _ _ _)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finsupp.sum_finset_sum_index (fun a => mul_zero _) (fun a b1 b2 => mul_add _ _ _)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finsupp.sum_single_index (mul_zero _)]
    rw [hftm]
    have e1 : ∀ ω, Xfg f g F.C (Y ω) = ∑ i : Fin m, ∑ j : Fin n,
        f (SP.μ i) * g (SP.lam j) * ((SP.uOutᵀ * Y ω * SP.vIn) i j) ^ 2 :=
      fun ω => block_G_spectral f g SP (Y ω)
    simp_rw [e1]
    have hI : ∀ i : Fin m, Integrable (fun ω => ∑ j : Fin n,
        f (SP.μ i) * g (SP.lam j) * ((SP.uOutᵀ * Y ω * SP.vIn) i j) ^ 2) P' := fun i =>
      integrable_finset_sum _ fun j _ => hZint i j
    rw [integral_finset_sum Finset.univ (fun i _ => hI i), Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum Finset.univ (fun j _ => hZint i j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_const_mul]
    have hBL : (B : ℝ) * L ≠ 0 := by positivity
    field_simp
  rw [hspec]; ring

end frozen3

private lemma block_Ahat_norm {m n : ℕ} (C : Covariances m n) (D : Mat m n)
    (hD : 0 < riskSigma C D) : fro (Ahat C D) = 1 := by
  have hsq : ∀ (c : ℝ) (K : Mat m n), fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
    intro c K
    have hf : ∀ K : Mat m n, fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
      intro K
      unfold fro
      rw [Real.sq_sqrt (by positivity)]
      simp only [Real.norm_eq_abs, sq_abs]
    simp only [hf, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  have hr := eqn_app_setup_whitened_risk C D
  have hs : fro (Ahat C D) ^ 2 = 1 := by
    rw [Ahat, hsq, inv_pow, Real.sq_sqrt (by linarith)]
    rw [show fro (Arot C D) ^ 2 = 2 * riskSigma C D by linarith,
      inv_mul_cancel₀ (by linarith)]
  have hn : 0 ≤ fro (Ahat C D) := Real.sqrt_nonneg _
  nlinarith

private theorem block_physgrad_cont {m n B : ℕ} (C : Covariances m n) (D : Mat m n) :
    Continuous (fun b : Fin B → Vec m × Vec n =>
      batchGrad D (fun a => phys C (b a))) := by
  unfold batchGrad grad resid phys outer
  fun_prop

private theorem block_stat_aesm {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t D M ω).stat k) P := by
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))
      (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
      exact ((block_physgrad_cont C D).measurable.comp
        (Measurable.of_eval fun a => cs.meas_aux (t : ℤ) j a)).stronglyMeasurable.const_smul
          (emaW p.β j)
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add
      (((block_physgrad_cont C D).measurable.comp (Measurable.of_eval fun a =>
        cs.meas_act ((t : ℤ) + k + 1) a)).stronglyMeasurable.aestronglyMeasurable.const_smul
          (1 - p.β))

private theorem block_statV_path_aem {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D M : Mat m n) (hD : 0 < riskSigma C D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad D (physBatch C (cs.aux (t : ℤ) j) ω))) :
    AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p C cs t D M ω).statV k) P := by
  apply AEMeasurable.of_eval
  intro k
  have hρ : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (by linarith) p.hϱ.le
  exact (block_Qmeas (physRidge p C D) hρ).comp_aemeasurable (block_stat_aesm p C cs t D M hs k).aemeasurable

section statpart

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}
  {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}

private lemma block_stat_second_moment [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (S : DynSetup p P m n B) (f g : ℝ → ℝ) (S' : Muon.Setup.FrozenSamples P' m n B)
    (SP : SpectralData S.C) (FL : Mat m n → (ℝ × ℝ) →₀ ℝ)
    (hFL : ∀ (D : Mat m n) (Fz : Muon.Setup.FrozenParams m n B) (hC : Fz.C = S.C),
      Fz.A = Ahat S.C D → 0 < riskSigma S.C D → Fz.β = p.β →
        FL D = Muon.Volatility.finiteTimeMeasure Fz S' (hC ▸ SP) (blockLen B) p.ϱ)
    (hBpos : 0 < B) (t : ℕ) (D : Mat m n) (hD : 0 < riskSigma S.C D) :
    ∫ ω, Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω) ∂P =
      (blockLen B : ℝ) ^ 2 * Xfg f g S.C (dynVbar p S t D) +
      (blockLen B : ℝ) * (B : ℝ) * (FL D).sum (fun x r => f x.1 * g x.2 * r) := by
  have hLpos : 0 < blockLen B := by
    unfold blockLen
    apply Nat.floor_pos.mpr
    exact Real.one_le_rpow (by exact_mod_cast hBpos) (by norm_num)
  let F : Muon.Setup.FrozenParams m n B := ⟨S.C, Ahat S.C D, block_Ahat_norm S.C D hD, p.β, p.hβ, hBpos⟩
  have hlaw := lem_app_dyn_chains_i p S.C S.cs t D 0 hD F rfl rfl rfl S'
  have hFLD : FL D = Muon.Volatility.finiteTimeMeasure F S' SP (blockLen B) p.ϱ :=
    hFL D F rfl rfl hD rfl
  have hϱ0 : 0 ≤ p.ϱ := p.hϱ.le
  have hYp : AEMeasurable (fun ω' (k : ℕ) => frozenUpd F S' p.ϱ ((t : ℤ) + (k : ℤ) - 1) ω') P' := by
    have : Measurable (fun (x : ℤ → Mat m n) (k : ℕ) => x ((t : ℤ) + (k : ℤ) - 1)) :=
      Measurable.of_eval fun k => measurable_pi_apply _
    exact this.comp_aemeasurable (block_updpath_aem F S' p.ϱ hϱ0)
  have hXp : AEMeasurable (fun ω (k : ℕ) => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV k) P :=
    block_statV_path_aem p S.C S.cs t D 0 hD hlaw.1
  have hΨ : Measurable (fun y : ℕ → Mat m n => Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), y (r + 1))) :=
    (block_Xfg_cont f g S.C).measurable.comp (Finset.measurable_sum _ fun r _ => measurable_pi_apply _)
  have h1 : ∫ ω, Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω) ∂P =
      ∫ ω', Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), frozenUpd F S' p.ϱ ((t : ℤ) + r) ω') ∂P' := by
    have e1 := integral_map hXp hΨ.aestronglyMeasurable
    have e2 := integral_map hYp hΨ.aestronglyMeasurable
    rw [hlaw.2.2.1] at e1
    have e3 := e1.symm.trans e2
    have e4 : ∀ r : ℕ, (t : ℤ) + ((r + 1 : ℕ) : ℤ) - 1 = (t : ℤ) + r := fun r => by push_cast; ring
    simp only [stationaryV, e4] at e3 ⊢
    exact e3
  rw [h1, block_frozen_second_moment F S' SP p.ϱ p.hϱ f g (blockLen B) hLpos (t : ℤ), hFLD]
  have hmean : dynVbar p S t D = Muon.mean P' (frozenUpd F S' p.ϱ (t : ℤ)) := by
    have := hlaw.2.2.2.2
    exact this
  rw [hmean]

end statpart

section infra

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma block_isProb (S : DynSetup p P m n B) (hB : 0 < B) : IsProbabilityMeasure P := by
  have h := S.cs.law_act 0 ⟨0, hB⟩
  have hm := S.cs.meas_act 0 ⟨0, hB⟩
  refine ⟨?_⟩
  have := congrArg (fun μ => μ Set.univ) h
  simp only [Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ] at this
  rw [this]
  exact measure_univ

private lemma block_past_le (S : DynSetup p P m n B) (t : ℕ) : dynPast S t ≤ mΩ := by
  refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_) ?_
  · exact (S.cs.meas_act s a).comap_le
  · exact S.M0_meas.comap_le

private lemma block_past_mono (S : DynSetup p P m n B) {s t : ℕ} (h : s ≤ t) :
    dynPast S s ≤ dynPast S t := by
  refine sup_le_sup_right ?_ _
  refine iSup_le fun u => iSup_le fun hu => iSup_le fun a => ?_
  exact le_iSup₂_of_le u ⟨hu.1, hu.2.trans (by exact_mod_cast h)⟩ (le_iSup_of_le a le_rfl)

private lemma block_indep_sup {Ω : Type} (A M F G : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (hAG : A ≤ G) (hFG : F ≤ G) (hGle : G ≤ mΩ) (hMle : M ≤ mΩ) (hFle : F ≤ mΩ)
    (hAF : Indep A F P) (hMG : Indep M G P) : Indep (A ⊔ M) F P := by
  have hAle : A ≤ mΩ := hAG.trans hGle
  let p1 : Set (Set Ω) := {s | ∃ a, MeasurableSet[A] a ∧ ∃ b, MeasurableSet[M] b ∧ s = a ∩ b}
  have hp1 : IsPiSystem p1 := by
    rintro _ ⟨a, ha, b, hb, rfl⟩ _ ⟨a', ha', b', hb', rfl⟩ _
    refine ⟨a ∩ a', @MeasurableSet.inter Ω A _ _ ha ha', b ∩ b', @MeasurableSet.inter Ω M _ _ hb hb', ?_⟩
    ext x; simp only [Set.mem_inter_iff]; tauto
  have hgen : A ⊔ M = MeasurableSpace.generateFrom p1 := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        refine MeasurableSpace.measurableSet_generateFrom ⟨a, ha, Set.univ, @MeasurableSet.univ Ω M, by simp⟩
      · intro b hb
        refine MeasurableSpace.measurableSet_generateFrom ⟨Set.univ, @MeasurableSet.univ Ω A, b, hb, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro _ ⟨a, ha, b, hb, rfl⟩
      exact @MeasurableSet.inter Ω (A ⊔ M) _ _ ((le_sup_left : A ≤ A ⊔ M) _ ha) ((le_sup_right : M ≤ A ⊔ M) _ hb)
  have hp2 : IsPiSystem {s | MeasurableSet[F] s} := @MeasurableSpace.isPiSystem_measurableSet Ω F
  have hgen2 : F = MeasurableSpace.generateFrom {s | MeasurableSet[F] s} := (@MeasurableSpace.generateFrom_measurableSet Ω F).symm
  refine IndepSets.indep (sup_le hAle hMle) hFle hp1 hp2 hgen hgen2 ?_
  rw [IndepSets_iff]
  rintro _ f ⟨a, ha, b, hb, rfl⟩ hf
  have haG : MeasurableSet[G] a := hAG a ha
  have hfG : MeasurableSet[G] f := hFG f hf
  have h1 : P (a ∩ b ∩ f) = P b * P (a ∩ f) := by
    have := (Indep_iff _ _ _).mp hMG b (a ∩ f) hb (@MeasurableSet.inter Ω G _ _ haG hfG)
    rw [show a ∩ b ∩ f = b ∩ (a ∩ f) by ext x; simp only [Set.mem_inter_iff]; tauto]
    exact this
  have h2 : P (a ∩ f) = P a * P f := (Indep_iff _ _ _).mp hAF a f ha hf
  have h3 : P (a ∩ b) = P b * P a := by
    have := (Indep_iff _ _ _).mp hMG b a hb haG
    rw [Set.inter_comm]; exact this
  rw [h1, h2, h3]; ring


private lemma block_indep_past_future [IsProbabilityMeasure P] (S : DynSetup p P m n B) (t : ℕ) :
    Indep (dynPast S t) (chainFuture S.cs t) P := by
  refine block_indep_sup _ _ _
    ((⨆ (s : ℤ) (_ : 1 ≤ s) (a : Fin B), MeasurableSpace.comap (S.cs.act s a) inferInstance) ⊔
      (⨆ (s : ℤ) (j : ℕ) (a : Fin B), MeasurableSpace.comap (S.cs.aux s j a) inferInstance)) P
    ?_ ?_ ?_ ?_ ?_ ?_ S.M0_indep
  · refine le_sup_of_le_left (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
    exact le_iSup₂_of_le s hs.1 (le_iSup_of_le a le_rfl)
  · refine sup_le ?_ ?_
    · refine le_sup_of_le_left (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
      exact le_iSup₂_of_le s (by omega) (le_iSup_of_le a le_rfl)
    · refine le_sup_of_le_right (iSup_le fun j => iSup_le fun a => ?_)
      exact le_iSup_of_le (t : ℤ) (le_iSup_of_le j (le_iSup_of_le a le_rfl))
  · refine sup_le (iSup_le fun s => iSup_le fun _ => iSup_le fun a => ?_)
      (iSup_le fun s => iSup_le fun j => iSup_le fun a => ?_)
    · exact (S.cs.meas_act s a).comap_le
    · exact (S.cs.meas_aux s j a).comap_le
  · exact S.M0_meas.comap_le
  · refine sup_le ?_ ?_
    · exact iSup_le fun s => iSup_le fun _ => iSup_le fun a => (S.cs.meas_act s a).comap_le
    · exact iSup_le fun j => iSup_le fun a => (S.cs.meas_aux _ j a).comap_le
  · have hind := (iIndepFun_iff_iIndep _ _ _).mp S.cs.indep
    have hle : ∀ i, MeasurableSpace.comap
        (Sum.elim (fun q : ℤ × Fin B => S.cs.act q.1 q.2)
          (fun q : ℤ × ℕ × Fin B => S.cs.aux q.1 q.2.1 q.2.2) i : Ω → Vec m × Vec n) inferInstance ≤ mΩ := by
      intro i
      rcases i with q | q
      · exact (S.cs.meas_act q.1 q.2).comap_le
      · exact (S.cs.meas_aux q.1 q.2.1 q.2.2).comap_le
    have hdisj : Disjoint {i : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B) | ∃ q : ℤ × Fin B, i = Sum.inl q ∧ 1 ≤ q.1 ∧ q.1 ≤ (t : ℤ)}
        {i | (∃ q : ℤ × Fin B, i = Sum.inl q ∧ (t : ℤ) < q.1) ∨ (∃ q : ℤ × ℕ × Fin B, i = Sum.inr q ∧ q.1 = (t : ℤ))} := by
      rw [Set.disjoint_left]
      rintro i ⟨q, rfl, h1, h2⟩ (⟨q', hq', h3⟩ | ⟨q', hq', _⟩)
      · cases hq'; omega
      · cases hq'
    have := indep_iSup_of_disjoint hle hind hdisj
    refine indep_of_indep_of_le_right (indep_of_indep_of_le_left this ?_) ?_
    · refine iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_
      exact le_iSup₂_of_le (Sum.inl (s, a)) ⟨(s, a), rfl, hs.1, hs.2⟩ le_rfl
    · refine sup_le (iSup_le fun s => iSup_le fun hs => iSup_le fun a => ?_)
        (iSup_le fun j => iSup_le fun a => ?_)
      · exact le_iSup₂_of_le (Sum.inl (s, a)) (Or.inl ⟨(s, a), rfl, hs⟩) le_rfl
      · exact le_iSup₂_of_le (Sum.inr ((t : ℤ), j, a)) (Or.inr ⟨((t : ℤ), j, a), rfl, rfl⟩) le_rfl

end infra


private lemma block_risk_nonneg {m n : ℕ} (C : Covariances m n) (Δ : Mat m n) :
    0 ≤ riskSigma C Δ := by
  rw [eqn_app_setup_whitened_risk]
  positivity

private lemma block_risk_cont {m n : ℕ} (C : Covariances m n) :
    Continuous (fun Δ : Mat m n => riskSigma C Δ) := by
  unfold riskSigma pairSigma
  fun_prop

private lemma block_mat_meas {Ω : Type} {σ : MeasurableSpace Ω} {m n : ℕ} {F : Ω → Mat m n}
    (h : ∀ i j, Measurable[σ] fun ω => F ω i j) : Measurable[σ] F :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => h i j

private lemma block_entry_meas {Ω : Type} {σ : MeasurableSpace Ω} {m n : ℕ} {F : Ω → Mat m n}
    (hF : Measurable[σ] F) (i : Fin m) (j : Fin n) : Measurable[σ] fun ω => F ω i j :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hF)

private lemma block_grad_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    {Δ : Ω → Mat m n} {b : Ω → Batch m n B}
    (hΔ : Measurable[σ] Δ) (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => grad (Δ ω) (b ω)) := by
  have hGc : Continuous (fun pr : Mat m n × Batch m n B => grad pr.1 pr.2) := by
    unfold grad resid outer
    fun_prop
  exact Measurable.comp (g := fun pr : Mat m n × Batch m n B => grad pr.1 pr.2)
    (f := fun ω => (Δ ω, b ω)) hGc.measurable (hΔ.prodMk hb)

private lemma block_stepUpdate_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W)) (hMp : Measurable[σ] (fun ω => (s ω).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => stepUpdate C p (s ω) (b ω)) ∧
      Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
  have hWc : Continuous (fun A : Mat m n => A - p.Wstar) := continuous_id.sub continuous_const
  have hD : Measurable[σ] (fun ω => errorOf p (s ω)) := hWc.measurable.comp hW
  have hR : Measurable[σ] (fun ω => riskSigma C (errorOf p (s ω))) := (block_risk_cont C).measurable.comp hD
  have hset : MeasurableSet[σ] {ω | riskSigma C (errorOf p (s ω)) = 0} :=
    hR (measurableSet_singleton 0)
  have hF : Measurable[σ] (fun ω => grad (errorOf p (s ω)) (b ω)) := block_grad_meas hD hb
  have hbuf : Measurable[σ] (fun ω => stepBuffer p (s ω) (b ω)) := by
    apply block_mat_meas
    intro i j
    have hMij := block_entry_meas hMp i j
    have hFij := block_entry_meas hF i j
    simp only [stepBuffer, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    exact (hMij.const_mul _).add (hFij.const_mul _)
  refine ⟨?_, hbuf⟩
  refine Measurable.ite hset measurable_const ?_
  have hnn : ∀ ω, (0 : ℝ) ≤ 2 * riskSigma C (errorOf p (s ω)) * p.ϱ :=
    fun ω => mul_nonneg (mul_nonneg (by norm_num) (block_risk_nonneg C _)) p.hϱ.le
  have hφ : Measurable[σ]
      (fun ω => (⟨2 * riskSigma C (errorOf p (s ω)) * p.ϱ, hnn ω⟩ : Set.Ici (0 : ℝ))) :=
    ((hR.const_mul 2).mul_const p.ϱ).subtype_mk
  exact measurable_Q.comp (hφ.prodMk hbuf)

private lemma block_step_meas {Ω : Type} {σ : MeasurableSpace Ω} {B m n : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (k : ℕ) (s : Ω → AlgState m n) (b : Ω → Batch m n B)
    (hW : Measurable[σ] (fun ω => (s ω).W)) (hMp : Measurable[σ] (fun ω => (s ω).Mprev))
    (hb : Measurable[σ] b) :
    Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).W) ∧
      Measurable[σ] (fun ω => (step C p k (s ω) (b ω)).Mprev) := by
  obtain ⟨hU, hbuf⟩ := block_stepUpdate_meas (σ := σ) C p s b hW hMp hb
  refine ⟨?_, hbuf⟩
  apply block_mat_meas
  intro i j
  have hWij := block_entry_meas hW i j
  have hUij := block_entry_meas hU i j
  simp only [step, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  exact hWij.sub (hUij.const_mul _)

private lemma block_pi_meas {Ω : Type} {σ : MeasurableSpace Ω} {ι : Type*} {π : ι → Type*}
    [∀ i, MeasurableSpace (π i)] {g : Ω → ∀ i, π i} (h : ∀ i, Measurable[σ] fun ω => g ω i) :
    Measurable[σ] g := measurable_pi_iff.mpr h


section dyn

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma block_batch_meas (S : DynSetup p P m n B) (u : ℕ) :
    Measurable[dynPast S (u + 1)] (dynBatch S u) := by
  refine block_pi_meas (fun a => ?_)
  have h1 : Measurable[dynPast S (u + 1)] (S.cs.act ((u : ℤ) + 1) a) := by
    refine Measurable.of_comap_le ?_
    refine le_sup_of_le_left ?_
    exact le_iSup₂_of_le ((u : ℤ) + 1) ⟨by omega, by push_cast; omega⟩ (le_iSup_of_le a le_rfl)
  have hc : Continuous (fun z : Vec m × Vec n => phys S.C z) := by
    unfold phys; fun_prop
  exact hc.measurable.comp h1

private lemma block_state_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (fun ω => (dynState S t ω).W) ∧
      Measurable[dynPast S t] (fun ω => (dynState S t ω).Mprev) := by
  induction t with
  | zero =>
    refine ⟨measurable_const, ?_⟩
    have : Measurable[MeasurableSpace.comap S.M0 inferInstance] S.M0 := comap_measurable _
    exact this.mono (le_sup_right) le_rfl
  | succ k ih =>
    have hW : Measurable[dynPast S (k + 1)] (fun ω => (dynState S k ω).W) := ih.1.mono (block_past_mono S (Nat.le_succ k)) le_rfl
    have hM : Measurable[dynPast S (k + 1)] (fun ω => (dynState S k ω).Mprev) := ih.2.mono (block_past_mono S (Nat.le_succ k)) le_rfl
    exact block_step_meas (σ := dynPast S (k + 1)) S.C S.alg k (dynState S k) (dynBatch S k) hW hM (block_batch_meas S k)



private lemma block_delta_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynDelta S t) := by
  have hWc : Continuous (fun A : Mat m n => A - S.alg.Wstar) := continuous_id.sub continuous_const
  exact hWc.measurable.comp (block_state_meas S t).1

private lemma block_buf_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S t] (dynBuf S t) := (block_state_meas S t).2

private lemma block_upd_meas (S : DynSetup p P m n B) (t : ℕ) :
    Measurable[dynPast S (t + 1)] (dynUpd S t) := by
  have hW : Measurable[dynPast S (t + 1)] (fun ω => (dynState S t ω).W) :=
    (block_state_meas S t).1.mono (block_past_mono S (Nat.le_succ t)) le_rfl
  have hM : Measurable[dynPast S (t + 1)] (fun ω => (dynState S t ω).Mprev) :=
    (block_state_meas S t).2.mono (block_past_mono S (Nat.le_succ t)) le_rfl
  exact (block_stepUpdate_meas (σ := dynPast S (t + 1)) S.C S.alg (dynState S t) (dynBatch S t) hW hM
    (block_batch_meas S t)).1

private lemma block_upd_meas' (S : DynSetup p P m n B) (t : ℕ) : Measurable (dynUpd S t) :=
  (block_upd_meas S t).mono (block_past_le S _) le_rfl

private lemma block_dynUpd_bound (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) (i : Fin m) (j : Fin n) :
    |dynUpd S t ω i j| ≤ (m : ℝ) + 1 := by
  unfold dynUpd gtRand stepUpdate
  split_ifs with h
  · simp; positivity
  · exact block_Q_entry_bound _ (mul_nonneg (mul_nonneg (by norm_num) (block_risk_nonneg _ _)) S.alg.hϱ.le) _ i j

end dyn


private lemma block_statV_norm {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D M : Mat m n)
    (hD : 0 < riskSigma C D) (r : ℕ) (ω : Ω) :
    stationaryV p C cs t D r ω = Q p.ϱ (normChainPath p C cs t D M ω (r + 1)) := by
  have hc : 0 < Real.sqrt (2 * riskSigma C D) := Real.sqrt_pos.mpr (by linarith)
  have := prop_app_setup_scaling_ii p.ϱ p.hϱ.le (normChainPath p C cs t D M ω (r + 1)) (riskSigma C D) hD
  have e : Real.sqrt (2 * riskSigma C D) • normChainPath p C cs t D M ω (r + 1) =
      (def_app_dyn_chains p C cs t D M ω).stat (r + 1) := by
    simp only [normChainPath, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [e] at this
  simp only [stationaryV, def_app_dyn_chains, physRidge]
  exact this


private lemma block_fro_sq_eq {m n : ℕ} (A : Mat m n) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (by positivity)]
  simp only [Real.norm_eq_abs, sq_abs]

private lemma block_admA_measurable {m n : ℕ} (p : DynParams) (C : Covariances m n) :
    MeasurableSet (admA p C) := by
  have h1 : Measurable (fun Δ : Mat m n => riskSigma C Δ) := (block_risk_cont C).measurable
  have h2 : Measurable (fun Δ : Mat m n => fro Δ ^ 2) := by
    simp_rw [block_fro_sq_eq]; fun_prop
  unfold admA admSetOf admBase
  simp only [Set.setOf_and]
  exact (measurableSet_le measurable_const h1).inter
    ((measurableSet_le h1 measurable_const).inter (measurableSet_le h2 measurable_const))

private lemma block_adm_risk {m n : ℕ} (p : DynParams) (C : Covariances m n) {D : Mat m n}
    (hD : D ∈ admA p C) : p.r0 / 2 ≤ riskSigma C D ∧ riskSigma C D ≤ p.r1 + 1 / 2 ∧
      fro D ^ 2 ≤ p.Estar + 1 := hD

private lemma block_adm_pos {m n : ℕ} (p : DynParams) (C : Covariances m n) {D : Mat m n}
    (hD : D ∈ admA p C) : 0 < riskSigma C D := by
  have := (block_adm_risk p C hD).1
  have := p.hr0
  linarith

private lemma block_adm_entry {m n : ℕ} (p : DynParams) (C : Covariances m n) {D : Mat m n}
    (hD : D ∈ admA p C) (i : Fin m) (j : Fin n) : |D i j| ≤ p.Estar + 2 := by
  have h1 := block_abs_entry_le_fro D i j
  have h2 := (block_adm_risk p C hD).2.2
  have h0 : 0 ≤ fro D := Real.sqrt_nonneg _
  nlinarith [sq_nonneg (fro D - 1), p.hE]



private theorem block_stat_rand_aesm {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Ω → Mat m n) (hD : Measurable D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))) (k : ℕ) :
    AEStronglyMeasurable (fun ω => (def_app_dyn_chains p C cs t (D ω) 0 ω).stat k) P := by
  have hcG : Continuous (fun x : Mat m n × (Fin B → Vec m × Vec n) =>
      batchGrad x.1 (fun a => phys C (x.2 a))) := by
    unfold batchGrad grad resid phys outer
    fun_prop
  have hb : ∀ s : ℤ, Measurable (fun ω => batchGrad (D ω) (physBatch C (cs.act s) ω)) := by
    intro s
    have h1 : Measurable (fun ω => (D ω, fun a => cs.act s a ω)) :=
      hD.prodMk (measurable_pi_iff.mpr fun a => cs.meas_act s a)
    have h2 := hcG.measurable.comp h1
    have e : (fun ω => batchGrad (D ω) (physBatch C (cs.act s) ω)) =
        (fun x : Mat m n × (Fin B → Vec m × Vec n) => batchGrad x.1 (fun a => phys C (x.2 a))) ∘
          (fun ω => (D ω, fun a => cs.act s a ω)) := by
      funext ω; rfl
    rw [e]; exact h2
  induction k with
  | zero =>
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
      ∑ j ∈ Finset.range N,
        emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))
      (fun N => ?_) ?_
    · refine (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ => ?_).aestronglyMeasurable
      have h1 : Measurable (fun ω => (D ω, fun a => cs.aux (t : ℤ) j a ω)) :=
        hD.prodMk (measurable_pi_iff.mpr fun a => cs.meas_aux (t : ℤ) j a)
      exact (hcG.measurable.comp h1).stronglyMeasurable.const_smul (emaW p.β j)
    · filter_upwards [hs] with ω hω
      exact hω.hasSum.tendsto_sum_nat
  | succ k ih =>
    exact (ih.const_smul p.β).add ((hb ((t : ℤ) + k + 1)).stronglyMeasurable.aestronglyMeasurable.const_smul (1 - p.β))

private theorem block_statV_rand_aem {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ)
    (D : Ω → Mat m n) (hD : Measurable D)
    (hs : ∀ᵐ ω ∂P, Summable (fun j : ℕ =>
      emaW p.β j • batchGrad (D ω) (physBatch C (cs.aux (t : ℤ) j) ω))) (r : ℕ) :
    AEMeasurable (fun ω => stationaryV p C cs t (D ω) r ω) P := by
  have hρ : ∀ ω, 0 ≤ physRidge p C (D ω) := fun ω => by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) (block_risk_nonneg _ _)) p.hϱ.le
  have hρm : Measurable (fun ω => (⟨physRidge p C (D ω), hρ ω⟩ : Set.Ici (0 : ℝ))) := by
    unfold physRidge
    exact (((block_risk_cont C).measurable.comp hD).const_mul 2 |>.mul_const p.ϱ).subtype_mk
  have hst := (block_stat_rand_aesm p C cs t D hD hs (r + 1)).aemeasurable
  exact (measurable_Q (m := m) (n := n)).comp_aemeasurable (hρm.aemeasurable.prodMk hst)



private lemma block_bound_of_cont2 {m n : ℕ} (h : Mat m n × Mat m n → ℝ) (hc : Continuous h) (R : ℝ) :
    ∃ K : ℝ, ∀ Y Z : Mat m n, (∀ i j, |Y i j| ≤ R) → (∀ i j, |Z i j| ≤ R) → |h (Y, Z)| ≤ K := by
  have hK0 : IsCompact (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) :=
    isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_Icc
  have hK := hK0.prod hK0
  obtain ⟨K, hK'⟩ := hK.exists_bound_of_continuousOn (f := h) hc.continuousOn
  refine ⟨K, fun Y Z hY hZ => ?_⟩
  have hmem : (Y, Z) ∈ (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) ×ˢ (Set.pi Set.univ fun i : Fin m => Set.pi Set.univ fun j : Fin n => Set.Icc (-R) R :
      Set (Mat m n)) := by
    refine ⟨?_, ?_⟩
    · intro i _ j _; exact abs_le.mp (hY i j)
    · intro i _ j _; exact abs_le.mp (hZ i j)
  have := hK' (Y, Z) hmem
  rwa [Real.norm_eq_abs] at this

private lemma block_integrable_cont2 {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {m n : ℕ} {X Y : Ω' → Mat m n} (hX : AEMeasurable X P')
    (hY : AEMeasurable Y P') (R : ℝ)
    (hbX : ∀ ω i j, |X ω i j| ≤ R) (hbY : ∀ ω i j, |Y ω i j| ≤ R)
    (h : Mat m n × Mat m n → ℝ) (hc : Continuous h) :
    Integrable (fun ω => h (X ω, Y ω)) P' := by
  obtain ⟨K, hK⟩ := block_bound_of_cont2 h hc R
  refine Integrable.of_bound (C := K) (hc.measurable.comp_aemeasurable (hX.prodMk hY)).aestronglyMeasurable ?_
  exact ae_of_all _ fun ω => by simpa using hK (X ω) (Y ω) (hbX ω) (hbY ω)

private lemma block_condExp_sum {Ω : Type} (𝓕 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) {ι : Type*} (s : Finset ι) (g : ι → Ω → ℝ) (hint : ∀ i ∈ s, Integrable (g i) P) :
    condExp 𝓕 P (fun ω => ∑ i ∈ s, g i ω) =ᵐ[P] fun ω => ∑ i ∈ s, condExp 𝓕 P (g i) ω := by
  have := condExp_finsetSum (μ := P) (s := s) (f := g) hint 𝓕
  have e : (fun ω => ∑ i ∈ s, g i ω) = ∑ i ∈ s, g i := by funext ω; simp [Finset.sum_apply]
  rw [e]
  filter_upwards [this] with ω hω
  simpa [Finset.sum_apply] using hω

/-- Pull-out of an `𝓕`-measurable bounded matrix inside `frobIP` under `condExp`. -/
private lemma block_condExp_frobIP_pull {Ω : Type} (𝓕 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) [IsProbabilityMeasure P] (h𝓕 : 𝓕 ≤ mΩ) {m n : ℕ}
    (c u : Ω → Mat m n) (R : ℝ)
    (hc : ∀ i j, Measurable[𝓕] (fun ω => c ω i j)) (hcb : ∀ ω i j, |c ω i j| ≤ R)
    (hu : Measurable u) (hub : ∀ ω i j, |u ω i j| ≤ R) :
    condExp 𝓕 P (fun ω => frobIP (c ω) (u ω)) =ᵐ[P]
      fun ω => frobIP (c ω) (Muon.Foundations.condExpMat 𝓕 P u ω) := by
  have hcm : ∀ i j, Measurable (fun ω => c ω i j) := fun i j => (hc i j).mono h𝓕 le_rfl
  have hui : ∀ i j, Integrable (fun ω => u ω i j) P := fun i j =>
    Integrable.of_bound (C := R) ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hu)).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa using hub ω i j)
  have hcu : ∀ i j, Integrable (fun ω => c ω i j * u ω i j) P := fun i j =>
    Integrable.of_bound (C := R * R) (((hcm i j).mul ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hu))).aestronglyMeasurable)
      (ae_of_all _ fun ω => by
        simp only [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul (hcb ω i j) (hub ω i j) (abs_nonneg _) ((abs_nonneg _).trans (hcb ω i j)))
  have h1 : ∀ i j, condExp 𝓕 P (fun ω => c ω i j * u ω i j) =ᵐ[P]
      fun ω => c ω i j * condExp 𝓕 P (fun ω' => u ω' i j) ω := by
    intro i j
    exact condExp_mul_of_stronglyMeasurable_left (hc i j).stronglyMeasurable (hcu i j) (hui i j)
  have hrow : ∀ i, Integrable (fun ω => ∑ j, c ω i j * u ω i j) P := fun i =>
    integrable_finsetSum _ fun j _ => hcu i j
  have e0 : (fun ω => frobIP (c ω) (u ω)) = fun ω => ∑ i, ∑ j, c ω i j * u ω i j := by
    funext ω; exact block_frobIP_eq_sum _ _
  rw [e0]
  have e1 := block_condExp_sum 𝓕 P (Finset.univ : Finset (Fin m))
    (fun i ω => ∑ j, c ω i j * u ω i j) (fun i _ => hrow i)
  have e2' : ∀ᵐ ω ∂P, ∀ i, condExp 𝓕 P (fun ω => ∑ j, c ω i j * u ω i j) ω =
      ∑ j, condExp 𝓕 P (fun ω => c ω i j * u ω i j) ω :=
    ae_all_iff.2 fun i => block_condExp_sum 𝓕 P (Finset.univ : Finset (Fin n))
      (fun j ω => c ω i j * u ω i j) (fun j _ => hcu i j)
  have e3' : ∀ᵐ ω ∂P, ∀ i j, condExp 𝓕 P (fun ω => c ω i j * u ω i j) ω =
      c ω i j * condExp 𝓕 P (fun ω' => u ω' i j) ω :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => h1 i j
  filter_upwards [e1, e2', e3'] with ω h1ω h2ω h3ω
  rw [h1ω]
  simp only [Finset.sum_apply, h2ω]
  rw [block_frobIP_eq_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h3ω i j]
  rfl



private lemma block_blockLen_pos {B : ℕ} (hB : 0 < B) : 0 < blockLen B := by
  unfold blockLen
  apply Nat.floor_pos.mpr
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma block_statV_bound {m n B : ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    (p : DynParams) (C : Covariances m n) (cs : ChainSamples P m n B) (t : ℕ) (D : Mat m n) (r : ℕ)
    (ω : Ω) (i : Fin m) (j : Fin n) : |stationaryV p C cs t D r ω i j| ≤ (m : ℝ) + 1 := by
  have hnn : 0 ≤ physRidge p C D := by
    unfold physRidge
    exact mul_nonneg (mul_nonneg (by norm_num) (block_risk_nonneg _ _)) p.hϱ.le
  exact block_Q_entry_bound _ hnn _ i j

private lemma block_wfg_cont {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) :
    Continuous (wfg f g C) := by
  unfold wfg; fun_prop

private lemma block_sum_bound {m n : ℕ} {Ω : Type} (s : Finset ℕ) (X : ℕ → Ω → Mat m n) (c : ℝ)
    (h : ∀ r ω i j, |X r ω i j| ≤ c) (ω : Ω) (i : Fin m) (j : Fin n) :
    |(∑ r ∈ s, X r ω) i j| ≤ (s.card : ℝ) * c := by
  simp only [Matrix.sum_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ r ∈ s, |X r ω i j| ≤ ∑ r ∈ s, c := Finset.sum_le_sum fun r _ => h r ω i j
    _ = (s.card : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]

private lemma block_condExp_const_mul {Ω : Type} (𝓕 : MeasurableSpace Ω) {mΩ : MeasurableSpace Ω}
    (P : Measure Ω) (c : ℝ) (f : Ω → ℝ) :
    condExp 𝓕 P (fun ω => c * f ω) =ᵐ[P] fun ω => c * condExp 𝓕 P f ω := by
  have := condExp_smul (μ := P) c f 𝓕
  have e : (fun ω => c * f ω) = c • f := by funext ω; simp
  rw [e]
  filter_upwards [this] with ω hω
  simpa [smul_eq_mul] using hω

section main

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

/-- main lemma: nonempty `admA`, positive `B`. -/
private lemma block_main (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (S' : Muon.Setup.FrozenSamples P' m n B) (SP : SpectralData S.C)
    (FL : Mat m n → (ℝ × ℝ) →₀ ℝ)
    (hFL : ∀ (D : Mat m n) (Fz : Muon.Setup.FrozenParams m n B) (hC : Fz.C = S.C),
      Fz.A = Ahat S.C D → 0 < riskSigma S.C D → Fz.β = p.β →
        FL D = Muon.Volatility.finiteTimeMeasure Fz S' (hC ▸ SP) (blockLen B) p.ϱ)
    (hBpos : 0 < B) (hne : (admA p S.C).Nonempty) [IsProbabilityMeasure P] :
    Integrable ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
      (fun ω => Xfg f g S.C (dynDelta S (b * blockLen B + blockLen B) ω)
        - Xfg f g S.C (dynDelta S (b * blockLen B) ω))) P ∧
    Integrable ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
      (fun ω => 2 * frobIP (dynStatSum p S (b * blockLen B) ω)
          (wfg f g S.C (dynSumErr p S (b * blockLen B) ω))
        + frobIP (dynSumErr p S (b * blockLen B) ω) (wfg f g S.C (dynSumErr p S (b * blockLen B) ω)))) P ∧
    condExp (dynPast S (b * blockLen B)) P
        ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
          (fun ω => Xfg f g S.C (dynDelta S (b * blockLen B + blockLen B) ω)
            - Xfg f g S.C (dynDelta S (b * blockLen B) ω)))
      =ᵐ[P] {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
        (fun ω =>
          -2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (blockLen B),
              frobIP (wfg f g S.C (dynDelta S (b * blockLen B) ω))
                (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
                  (dynUpd S (b * blockLen B + r)) ω)
          + (p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) ^ 2 *
              frobIP (dynVbar p S (b * blockLen B) (dynDelta S (b * blockLen B) ω))
                (wfg f g S.C (dynVbar p S (b * blockLen B) (dynDelta S (b * blockLen B) ω)))
          + (p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) * (B : ℝ) *
              (FL (dynDelta S (b * blockLen B) ω)).sum (fun x r => f x.1 * g x.2 * r)
          + (p.h / (B : ℝ)) ^ 2 * condExp (dynPast S (b * blockLen B)) P
              ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
                (fun ω => 2 * frobIP (dynStatSum p S (b * blockLen B) ω)
                    (wfg f g S.C (dynSumErr p S (b * blockLen B) ω))
                  + frobIP (dynSumErr p S (b * blockLen B) ω)
                    (wfg f g S.C (dynSumErr p S (b * blockLen B) ω)))) ω) := by
  classical
  have hLpos := block_blockLen_pos hBpos
  set t := b * blockLen B with ht
  have h𝓕 : dynPast S t ≤ mΩ := block_past_le S t
  set A : Set Ω := {ω | dynDelta S t ω ∈ admA p S.C} with hA
  have hAF : MeasurableSet[dynPast S t] A := (block_delta_meas S t) (block_admA_measurable p S.C)
  have hAm : MeasurableSet A := h𝓕 _ hAF
  obtain ⟨D0, hD0⟩ := hne
  set D' : Ω → Mat m n := fun ω => if dynDelta S t ω ∈ admA p S.C then dynDelta S t ω else D0 with hD'
  have hD'F : Measurable[dynPast S t] D' := Measurable.ite hAF (block_delta_meas S t) measurable_const
  have hD'adm : ∀ ω, D' ω ∈ admA p S.C := fun ω => by
    simp only [hD']; split_ifs with h
    · exact h
    · exact hD0
  have hD'pos : ∀ ω, 0 < riskSigma S.C (D' ω) := fun ω => block_adm_pos p S.C (hD'adm ω)
  have hD'eq : ∀ ω ∈ A, D' ω = dynDelta S t ω := fun ω hω => by simp only [hD']; exact if_pos hω
  have hD'm : Measurable D' := hD'F.mono h𝓕 le_rfl
  have hDint : Integrable (fun ω => riskSigma S.C (D' ω)) P := by
    refine Integrable.of_bound (C := p.r1 + 1 / 2) ((block_risk_cont S.C).measurable.comp hD'm).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    have := (block_adm_risk p S.C (hD'adm ω)).2.1
    rw [Real.norm_eq_abs, abs_of_nonneg (block_risk_nonneg _ _)]
    exact this
  have hiv := lem_app_dyn_chains_iv (dynPast S t) p S.C S.cs t S.size h𝓕 (block_indep_past_future S t)
    D' (dynBuf S t) hD'F (block_buf_meas S t) (ae_of_all _ hD'pos) hDint
  have hsum := hiv.1
  have hVs_aem : ∀ r, AEMeasurable (fun ω => stationaryV p S.C S.cs t (D' ω) r ω) P := fun r =>
    block_statV_rand_aem p S.C S.cs t D' hD'm hsum r
  have hu_m : ∀ r, Measurable (dynUpd S (t + r)) := fun r => block_upd_meas' S (t + r)
  -- sums
  set Ssum : Ω → Mat m n := fun ω => ∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (D' ω) r ω with hSsum
  set Esum : Ω → Mat m n := fun ω => ∑ r ∈ Finset.range (blockLen B),
    (dynUpd S (t + r) ω - stationaryV p S.C S.cs t (D' ω) r ω) with hEsum
  have hSaem : AEMeasurable Ssum P := Finset.aemeasurable_fun_sum _ fun r _ => hVs_aem r
  have hEaem : AEMeasurable Esum P :=
    Finset.aemeasurable_fun_sum _ fun r _ => (hu_m r).aemeasurable.sub (hVs_aem r)
  set R : ℝ := (blockLen B : ℝ) * (2 * ((m : ℝ) + 1)) + p.Estar + 2 with hR
  have hR0 : 0 ≤ (blockLen B : ℝ) * (2 * ((m : ℝ) + 1)) := by positivity
  have hL1 : (1 : ℝ) ≤ blockLen B := by exact_mod_cast hLpos
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hRL : (blockLen B : ℝ) * ((m : ℝ) + 1) ≤ R := by
    nlinarith [p.hE, (Nat.cast_nonneg m : (0 : ℝ) ≤ m), (Nat.cast_nonneg (blockLen B) : (0 : ℝ) ≤ blockLen B)]
  have hSb : ∀ ω i j, |Ssum ω i j| ≤ R := by
    intro ω i j
    have h1 := block_sum_bound (Finset.range (blockLen B)) (fun r ω => stationaryV p S.C S.cs t (D' ω) r ω) ((m : ℝ) + 1)
      (fun r ω i j => block_statV_bound p S.C S.cs t _ r ω i j) ω i j
    simp only [Finset.card_range] at h1
    exact h1.trans hRL
  have hEb : ∀ ω i j, |Esum ω i j| ≤ R := by
    intro ω i j
    have h1 := block_sum_bound (Finset.range (blockLen B))
      (fun r ω => dynUpd S (t + r) ω - stationaryV p S.C S.cs t (D' ω) r ω) (2 * ((m : ℝ) + 1))
      (fun r ω i j => by
        simp only [Matrix.sub_apply]
        have a1 := block_dynUpd_bound S (t + r) ω i j
        have a2 := block_statV_bound p S.C S.cs t (D' ω) r ω i j
        calc _ ≤ |dynUpd S (t + r) ω i j| + |stationaryV p S.C S.cs t (D' ω) r ω i j| := abs_sub _ _
          _ ≤ _ := by linarith) ω i j
    simp only [Finset.card_range] at h1
    exact h1.trans (by nlinarith [p.hE])
  have hD'b : ∀ ω i j, |D' ω i j| ≤ R := by
    intro ω i j
    exact (block_adm_entry p S.C (hD'adm ω) i j).trans (by nlinarith [p.hE])
  have hub : ∀ r ω i j, |dynUpd S (t + r) ω i j| ≤ R := by
    intro r ω i j
    exact (block_dynUpd_bound S (t + r) ω i j).trans (by nlinarith [p.hE, hL1, hm0, mul_nonneg (sub_nonneg.mpr hL1) (add_nonneg hm0 zero_le_one)])
  -- integrability of the building blocks
  have hT2 : Integrable (fun ω => Xfg f g S.C (Ssum ω)) P :=
    block_integrable_cont hSaem R hSb _ (block_Xfg_cont f g S.C)
  have hT3 : Integrable (fun ω => 2 * frobIP (Ssum ω) (wfg f g S.C (Esum ω)) +
      frobIP (Esum ω) (wfg f g S.C (Esum ω))) P := by
    have hc : Continuous (fun x : Mat m n × Mat m n =>
        2 * frobIP x.1 (wfg f g S.C x.2) + frobIP x.2 (wfg f g S.C x.2)) := by
      have h1 : Continuous (fun x : Mat m n × Mat m n => frobIP x.1 (wfg f g S.C x.2)) :=
        block_frobIP_cont.comp (continuous_fst.prodMk ((block_wfg_cont f g S.C).comp continuous_snd))
      have h2 : Continuous (fun x : Mat m n × Mat m n => frobIP x.2 (wfg f g S.C x.2)) :=
        block_frobIP_cont.comp (continuous_snd.prodMk ((block_wfg_cont f g S.C).comp continuous_snd))
      exact (continuous_const.mul h1).add h2
    exact block_integrable_cont2 hSaem hEaem R hSb hEb _ hc
  have hT1 : ∀ r, Integrable (fun ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) P := by
    intro r
    have hc : Continuous (fun x : Mat m n × Mat m n => frobIP (wfg f g S.C x.1) x.2) :=
      block_frobIP_cont.comp (((block_wfg_cont f g S.C).comp continuous_fst).prodMk continuous_snd)
    exact block_integrable_cont2 hD'm.aemeasurable (hu_m r).aemeasurable R hD'b (hub r) _ hc
  -- the increment on `A`
  set T3 : Ω → ℝ := fun ω => 2 * frobIP (Ssum ω) (wfg f g S.C (Esum ω)) +
      frobIP (Esum ω) (wfg f g S.C (Esum ω)) with hT3def
  set T1 : Ω → ℝ := fun ω => ∑ r ∈ Finset.range (blockLen B), frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω) with hT1def
  set inc' : Ω → ℝ := fun ω => -2 * (p.h / (B : ℝ)) * T1 ω +
      (p.h / (B : ℝ)) ^ 2 * (Xfg f g S.C (Ssum ω) + T3 ω) with hinc'
  have hpt : ∀ ω ∈ A, Xfg f g S.C (dynDelta S (t + blockLen B) ω) - Xfg f g S.C (dynDelta S t ω) = inc' ω := by
    intro ω hω
    have h1 := block_pointwise_identity p S f g t ω
    have e1 : dynStatSum p S t ω = Ssum ω := by
      simp only [dynStatSum, hSsum, hD'eq ω hω]
    have e2 : dynSumErr p S t ω = Esum ω := by
      simp only [dynSumErr, hEsum, hD'eq ω hω]
    rw [h1, e1, e2]
    simp only [hinc', hT1def, hT3def, hD'eq ω hω, Xfg]
    ring
  have hT3pt : ∀ ω ∈ A, 2 * frobIP (dynStatSum p S t ω) (wfg f g S.C (dynSumErr p S t ω)) +
      frobIP (dynSumErr p S t ω) (wfg f g S.C (dynSumErr p S t ω)) = T3 ω := by
    intro ω hω
    have e1 : dynStatSum p S t ω = Ssum ω := by
      simp only [dynStatSum, hSsum, hD'eq ω hω]
    have e2 : dynSumErr p S t ω = Esum ω := by
      simp only [dynSumErr, hEsum, hD'eq ω hω]
    rw [e1, e2]
  have hind_inc : A.indicator (fun ω => Xfg f g S.C (dynDelta S (t + blockLen B) ω) - Xfg f g S.C (dynDelta S t ω))
      = A.indicator inc' := Set.indicator_congr hpt
  have hind_T3 : A.indicator (fun ω => 2 * frobIP (dynStatSum p S t ω) (wfg f g S.C (dynSumErr p S t ω)) +
      frobIP (dynSumErr p S t ω) (wfg f g S.C (dynSumErr p S t ω))) = A.indicator T3 := Set.indicator_congr hT3pt
  have hT1int : Integrable T1 P := integrable_finsetSum _ fun r _ => hT1 r
  have hincint : Integrable inc' P :=
    (hT1int.const_mul _).add ((hT2.add hT3).const_mul _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hind_inc]; exact hincint.indicator hAm
  · rw [hind_T3]; exact hT3.indicator hAm
  · rw [hind_inc, hind_T3]
    -- bounds on `𝒲 D'`
    obtain ⟨K1, hK1⟩ := block_bound_of_cont (fun Y : Mat m n => ∑ a, ∑ b, |wfg f g S.C Y a b|)
      (by
        have hc := block_wfg_cont f g S.C
        have : ∀ a b, Continuous (fun Y : Mat m n => |wfg f g S.C Y a b|) := fun a b => by
          have h1 : Continuous (fun Y : Mat m n => wfg f g S.C Y a b) := by
            have := hc
            exact (continuous_apply b).comp ((continuous_apply a).comp this)
          exact h1.abs
        exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ => this a b) R
    have hWb : ∀ ω i j, |wfg f g S.C (D' ω) i j| ≤ |K1| + R := by
      intro ω i j
      have h1 := hK1 (D' ω) (hD'b ω)
      have h2 : |wfg f g S.C (D' ω) i j| ≤ ∑ a, ∑ b, |wfg f g S.C (D' ω) a b| :=
        (Finset.single_le_sum (f := fun b => |wfg f g S.C (D' ω) i b|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ j)).trans
          (Finset.single_le_sum (f := fun a => ∑ b, |wfg f g S.C (D' ω) a b|)
            (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i))
      have h3 : ∑ a, ∑ b, |wfg f g S.C (D' ω) a b| ≤ |K1| := by
        exact ((le_abs_self _).trans h1).trans (le_abs_self _)
      have hR0' : 0 ≤ R := by nlinarith [p.hE, hm0, hL1]
      linarith
    have hWF : ∀ i j, Measurable[dynPast S t] (fun ω => wfg f g S.C (D' ω) i j) := by
      intro i j
      have h1 : Continuous (fun Y : Mat m n => wfg f g S.C Y i j) :=
        (continuous_apply j).comp ((continuous_apply i).comp (block_wfg_cont f g S.C))
      exact h1.measurable.comp hD'F
    have hE_T1 : ∀ r, condExp (dynPast S t) P (fun ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) =ᵐ[P]
        fun ω => frobIP (wfg f g S.C (D' ω)) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω) := by
      intro r
      refine block_condExp_frobIP_pull (dynPast S t) P h𝓕 (fun ω => wfg f g S.C (D' ω)) (dynUpd S (t + r))
        (|K1| + R) hWF hWb (hu_m r) (fun ω i j => (hub r ω i j).trans (by linarith [abs_nonneg K1]))
    -- freezing for the stationary second moment
    set Φ : (ℕ → Mat m n) → ℝ := fun x =>
        Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), Q p.ϱ (x (r + 1))) with hΦ
    have hΦm : Measurable Φ :=
      (block_Xfg_cont f g S.C).measurable.comp
        (Finset.measurable_sum _ fun r _ => (block_Qmeas p.ϱ p.hϱ.le).comp (measurable_pi_apply (r + 1)))
    obtain ⟨KΦ, hKΦ⟩ := block_bound_of_cont (Xfg f g S.C) (block_Xfg_cont f g S.C)
      ((blockLen B : ℝ) * ((m : ℝ) + 1))
    have hΦb : ∃ K : ℝ, ∀ x : ℕ → Mat m n, |Φ x| ≤ K := by
      refine ⟨KΦ, fun x => hKΦ _ (fun i j => ?_)⟩
      have := block_sum_bound (Finset.range (blockLen B)) (fun r (x : ℕ → Mat m n) => Q p.ϱ (x (r + 1)))
        ((m : ℝ) + 1) (fun r x i j => block_Q_entry_bound _ p.hϱ.le _ i j) x i j
      simpa using this
    have hfrz := hiv.2.2.2 Φ hΦm hΦb
    have hnormsum : ∀ (D M : Mat m n), 0 < riskSigma S.C D → ∀ ω' : Ω,
        ∑ r ∈ Finset.range (blockLen B), Q p.ϱ (normChainPath p S.C S.cs t D M ω' (r + 1)) =
          ∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t D r ω' := by
      intro D M hD ω'
      exact Finset.sum_congr rfl fun r _ => (block_statV_norm p S.C S.cs t D M hD r ω').symm
    have hnormfun : ∀ ω', Φ (normChainPath p S.C S.cs t (D' ω') (dynBuf S t ω') ω') = Xfg f g S.C (Ssum ω') := by
      intro ω'
      simp only [hΦ]
      rw [hnormsum _ _ (hD'pos ω')]
    have hnormint : ∀ ω, ∫ ω', Φ (normChainPath p S.C S.cs t (D' ω) (dynBuf S t ω) ω') ∂P =
        ∫ ω', Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (D' ω) r ω') ∂P := by
      intro ω
      refine integral_congr_ae (ae_of_all _ fun ω' => ?_)
      simp only [hΦ]
      rw [hnormsum _ _ (hD'pos ω)]
    have hE_T2 : condExp (dynPast S t) P (fun ω => Xfg f g S.C (Ssum ω)) =ᵐ[P]
        fun ω => ∫ ω', Xfg f g S.C (∑ r ∈ Finset.range (blockLen B), stationaryV p S.C S.cs t (D' ω) r ω') ∂P := by
      have e1 : (fun ω' => Φ (normChainPath p S.C S.cs t (D' ω') (dynBuf S t ω') ω')) =
          fun ω' => Xfg f g S.C (Ssum ω') := funext hnormfun
      rw [e1] at hfrz
      filter_upwards [hfrz] with ω hω
      rw [hω, hnormint ω]
    -- linearity of the conditional expectation
    have hlin : condExp (dynPast S t) P inc' =ᵐ[P] fun ω =>
        -2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (blockLen B),
          condExp (dynPast S t) P (fun ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) ω +
        (p.h / (B : ℝ)) ^ 2 * (condExp (dynPast S t) P (fun ω => Xfg f g S.C (Ssum ω)) ω +
          condExp (dynPast S t) P T3 ω) := by
      have e1 : condExp (dynPast S t) P inc' =ᵐ[P]
          condExp (dynPast S t) P (fun ω => -2 * (p.h / (B : ℝ)) * T1 ω) +
          condExp (dynPast S t) P (fun ω => (p.h / (B : ℝ)) ^ 2 * (Xfg f g S.C (Ssum ω) + T3 ω)) :=
        condExp_add (hT1int.const_mul _) ((hT2.add hT3).const_mul _) (dynPast S t)
      have e2 := block_condExp_const_mul (dynPast S t) P (-2 * (p.h / (B : ℝ))) T1
      have e3 := block_condExp_sum (dynPast S t) P (Finset.range (blockLen B))
        (fun r ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) (fun r _ => hT1 r)
      have e4 := block_condExp_const_mul (dynPast S t) P ((p.h / (B : ℝ)) ^ 2)
        (fun ω => Xfg f g S.C (Ssum ω) + T3 ω)
      have e5 := condExp_add hT2 hT3 (dynPast S t)
      filter_upwards [e1, e2, e3, e4, e5] with ω h1 h2 h3 h4 h5
      rw [h1]
      simp only [Pi.add_apply]
      rw [h2, h4]
      have h3' : condExp (dynPast S t) P T1 ω = ∑ r ∈ Finset.range (blockLen B),
          condExp (dynPast S t) P (fun ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) ω := h3
      have h5' : condExp (dynPast S t) P (fun ω => Xfg f g S.C (Ssum ω) + T3 ω) ω =
          condExp (dynPast S t) P (fun ω => Xfg f g S.C (Ssum ω)) ω + condExp (dynPast S t) P T3 ω := h5
      rw [h3', h5']
    have hE1 := condExp_indicator (μ := P) hincint hAF
    have hE3 := condExp_indicator (μ := P) hT3 hAF
    have hE_T1' : ∀ᵐ ω ∂P, ∀ r : ℕ, condExp (dynPast S t) P
        (fun ω => frobIP (wfg f g S.C (D' ω)) (dynUpd S (t + r) ω)) ω =
        frobIP (wfg f g S.C (D' ω)) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω) :=
      ae_all_iff.2 hE_T1
    filter_upwards [hE1, hlin, hE3, hE_T1', hE_T2] with ω h1 h2 h3 h4 h5
    by_cases hωA : ω ∈ A
    · have hstat := block_stat_second_moment S f g S' SP FL hFL hBpos t (D' ω) (hD'pos ω)
      rw [h1, Set.indicator_of_mem hωA, h2, h5]
      rw [Set.indicator_of_mem hωA, h3, Set.indicator_of_mem hωA]
      simp only [h4]
      rw [hD'eq ω hωA] at hstat ⊢
      rw [hstat]
      have hX : Xfg f g S.C (dynVbar p S t (dynDelta S t ω)) =
          frobIP (dynVbar p S t (dynDelta S t ω)) (wfg f g S.C (dynVbar p S t (dynDelta S t ω))) := rfl
      rw [hX]
      ring
    · rw [h1, Set.indicator_of_notMem hωA, Set.indicator_of_notMem hωA]
end main


/-- `eqn:app-dyn-block-identity`, snapshot `cr-2026-10-23`, the exact block identity at a block start
`t = b L` (`L = blockLen B`, `lr = h/B`, `𝒲 = 𝒲_{f,g}`, `X = X_{f,g}`, `S = ∑_{r<L} V_r`, `E = ∑_{r<L} 𝖲_{t+r} − S`,
`V̄ = V̄(D)`, `D = Δ_t`). Source, `section.tex` ll. 2182–2188, verbatim:
```latex
\begin{equation}\label{eqn:app-dyn-block-identity}
\begin{aligned}
\EE_t\big[X_{f,g}(\Delta_{t+L})-X_{f,g}(D)\big]={}&-2\lr\Big\langle\mathcal WD,\sum_{r<L}\EE_t{\mathsf S}_{t+r}\Big\rangle
+\lr^2L^2\langle\overline V,\mathcal W\overline V\rangle\\
&+\lr^2LB\int f\tensor g\,\dif\mathfrak F_L(D)
+\lr^2\,\EE_t\big[2\langle S,\mathcal W\mathcal E\rangle+\langle\mathcal E,\mathcal W\mathcal E\rangle\big],
\end{aligned}
```
Encoding: on the event `{Δ_t ∈ 𝒜}` (indicator inside `condExp`, `𝒜 = admA`); `𝔉_L(D)` is the finite-time measure
`FL D`, pinned by `hFL`. The forcing term is `∑ f⊗g dFL(D)` as a finitely supported sum. Part (i) integrability of the
update entries, (ii) of the left side and (iii) of the quadratic term are conclusion conjuncts. -/
theorem eqn_app_dyn_block_identity
    (p : DynParams) {m n B : ℕ} (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (S' : Muon.Setup.FrozenSamples P' m n B) (SP : SpectralData S.C)
    -- the forcing measure `𝔉_L(D)` of `thm:app-vol-joint-forcing`(iv) at `T = L` and state `Â(D)`
    (FL : Mat m n → (ℝ × ℝ) →₀ ℝ)
    (hFL : ∀ (D : Mat m n) (Fz : Muon.Setup.FrozenParams m n B) (hC : Fz.C = S.C),
      Fz.A = Ahat S.C D → 0 < riskSigma S.C D → Fz.β = p.β →
        FL D = Muon.Volatility.finiteTimeMeasure Fz S' (hC ▸ SP) (blockLen B) p.ϱ) :
    (∀ r : ℕ, r < blockLen B → ∀ i j,
      Integrable (fun ω => dynUpd S (b * blockLen B + r) ω i j) P) ∧
    Integrable ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
      (fun ω => Xfg f g S.C (dynDelta S (b * blockLen B + blockLen B) ω)
        - Xfg f g S.C (dynDelta S (b * blockLen B) ω))) P ∧
    Integrable ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
      (fun ω => 2 * frobIP (dynStatSum p S (b * blockLen B) ω)
          (wfg f g S.C (dynSumErr p S (b * blockLen B) ω))
        + frobIP (dynSumErr p S (b * blockLen B) ω) (wfg f g S.C (dynSumErr p S (b * blockLen B) ω)))) P ∧
    condExp (dynPast S (b * blockLen B)) P
        ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
          (fun ω => Xfg f g S.C (dynDelta S (b * blockLen B + blockLen B) ω)
            - Xfg f g S.C (dynDelta S (b * blockLen B) ω)))
      =ᵐ[P] {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
        (fun ω =>
          -2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (blockLen B),
              frobIP (wfg f g S.C (dynDelta S (b * blockLen B) ω))
                (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P
                  (dynUpd S (b * blockLen B + r)) ω)
          + (p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) ^ 2 *
              frobIP (dynVbar p S (b * blockLen B) (dynDelta S (b * blockLen B) ω))
                (wfg f g S.C (dynVbar p S (b * blockLen B) (dynDelta S (b * blockLen B) ω)))
          + (p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) * (B : ℝ) *
              (FL (dynDelta S (b * blockLen B) ω)).sum (fun x r => f x.1 * g x.2 * r)
          + (p.h / (B : ℝ)) ^ 2 * condExp (dynPast S (b * blockLen B)) P
              ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
                (fun ω => 2 * frobIP (dynStatSum p S (b * blockLen B) ω)
                    (wfg f g S.C (dynSumErr p S (b * blockLen B) ω))
                  + frobIP (dynSumErr p S (b * blockLen B) ω)
                    (wfg f g S.C (dynSumErr p S (b * blockLen B) ω)))) ω) := by
  classical
  by_cases hB0 : B = 0
  · subst hB0
    have hL0 : blockLen 0 = 0 := by simp [blockLen]
    simp only [hL0]
    refine ⟨fun r hr => absurd hr (Nat.not_lt_zero r), ?_, ?_, ?_⟩
    · simp
    · simp [dynStatSum, dynSumErr, frobIP, wfg, hL0]
    · simp [dynStatSum, dynSumErr, frobIP, wfg, hL0]
  have hBpos : 0 < B := Nat.pos_of_ne_zero hB0
  haveI hPprob : IsProbabilityMeasure P := block_isProb S hBpos
  have hupd : ∀ r : ℕ, r < blockLen B → ∀ i j,
      Integrable (fun ω => dynUpd S (b * blockLen B + r) ω i j) P := by
    intro r _ i j
    exact Integrable.of_bound (C := (m : ℝ) + 1)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (block_upd_meas' S (b * blockLen B + r)))).aestronglyMeasurable
      (ae_of_all _ fun ω => by simpa using block_dynUpd_bound S (b * blockLen B + r) ω i j)
  by_cases hne : (admA p S.C).Nonempty
  · obtain ⟨h2, h3, h4⟩ := block_main S f g b S' SP FL hFL hBpos hne
    exact ⟨hupd, h2, h3, h4⟩
  · have hA : {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hne ⟨_, h⟩
    rw [hA]
    refine ⟨hupd, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp


/-! ## P-E.12.P1: proof of `lem_app_dyn_block` (helpers) -/

private lemma blk_atom_integral {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ) (q : Fin m → Fin n → ℝ)
    (hq : ∀ i j, 0 ≤ q i j) (φ : ℝ × ℝ → ℝ) :
    Integrable φ (atomMeasure μ lam q) ∧
      ∫ x, φ x ∂(atomMeasure μ lam q) = ∑ i, ∑ j, q i j * φ (μ i, lam j) := by
  unfold atomMeasure
  have hint : ∀ i j, Integrable φ (ENNReal.ofReal (q i j) • Measure.dirac (μ i, lam j)) := fun i j =>
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top
  have hrow : ∀ i, Integrable φ (∑ j, ENNReal.ofReal (q i j) • Measure.dirac (μ i, lam j)) := fun i =>
    (integrable_finset_sum_measure).2 (fun j _ => hint i j)
  refine ⟨(integrable_finset_sum_measure).2 (fun i _ => hrow i), ?_⟩
  rw [integral_finset_sum_measure (fun i _ => hrow i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum_measure (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hq i j), smul_eq_mul]

private lemma blk_stepfun_ii (G : ℕ → ℝ) (Bn : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun σ : ℝ => G ⌊(Bn : ℝ) * σ⌋₊) volume a b := by
  rw [intervalIntegrable_iff]
  have hmeas : Measurable (fun σ : ℝ => G ⌊(Bn : ℝ) * σ⌋₊) :=
    (measurable_from_nat (f := G)).comp (Nat.measurable_floor.comp (measurable_const.mul measurable_id))
  refine Measure.integrableOn_of_bounded (M := ∑ u ∈ Finset.range (⌊(Bn : ℝ) * max a b⌋₊ + 1), |G u|)
    (by simp [Set.uIoc]) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun σ hσ => ?_)
  have hle : σ ≤ max a b := by
    rcases hσ with ⟨_, h⟩
    exact h
  have hK : ⌊(Bn : ℝ) * σ⌋₊ ≤ ⌊(Bn : ℝ) * max a b⌋₊ :=
    Nat.floor_le_floor (mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg Bn))
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (f := fun u => |G u|) (fun u _ => abs_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hK))

private lemma blk_stepfun_integral (G : ℕ → ℝ) (Bn : ℕ) (hB : 0 < Bn) (s : ℝ) (hs : 0 ≤ s) :
    ∫ σ in (0 : ℝ)..s, G ⌊(Bn : ℝ) * σ⌋₊ =
      (1 / (Bn : ℝ)) * ∑ u ∈ Finset.range ⌊(Bn : ℝ) * s⌋₊, G u +
        (s - (⌊(Bn : ℝ) * s⌋₊ : ℝ) / Bn) * G ⌊(Bn : ℝ) * s⌋₊ := by
  have hBpos : (0 : ℝ) < Bn := by exact_mod_cast hB
  set N := ⌊(Bn : ℝ) * s⌋₊ with hN
  have hNle : (N : ℝ) ≤ (Bn : ℝ) * s := Nat.floor_le (by positivity)
  have hNlt : (Bn : ℝ) * s < N + 1 := Nat.lt_floor_add_one _
  have hint := fun a b => blk_stepfun_ii G Bn a b
  have hsplit : ∫ σ in (0 : ℝ)..s, G ⌊(Bn : ℝ) * σ⌋₊ =
      (∫ σ in (0 : ℝ)..((N : ℝ) / Bn), G ⌊(Bn : ℝ) * σ⌋₊) +
        ∫ σ in ((N : ℝ) / Bn)..s, G ⌊(Bn : ℝ) * σ⌋₊ :=
    (intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _)).symm
  have hlast : ∫ σ in ((N : ℝ) / Bn)..s, G ⌊(Bn : ℝ) * σ⌋₊ = (s - (N : ℝ) / Bn) * G N := by
    have hle : (N : ℝ) / Bn ≤ s := by rw [div_le_iff₀ hBpos]; linarith
    rw [intervalIntegral.integral_congr (g := fun _ => G N)]
    · simp
    · intro σ hσ
      rw [Set.uIcc_of_le hle] at hσ
      simp only
      congr 1
      rw [Nat.floor_eq_iff (mul_nonneg hBpos.le (le_trans (by positivity) hσ.1))]
      constructor
      · have := hσ.1; rw [div_le_iff₀ hBpos] at this; linarith
      · have := hσ.2; nlinarith
  have hfirst : ∫ σ in (0 : ℝ)..((N : ℝ) / Bn), G ⌊(Bn : ℝ) * σ⌋₊ =
      (1 / (Bn : ℝ)) * ∑ u ∈ Finset.range N, G u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := fun σ : ℝ => G ⌊(Bn : ℝ) * σ⌋₊)
      (μ := volume) (a := fun u : ℕ => (u : ℝ) / Bn) (n := N) (fun u _ => hint _ _)
    simp only [Nat.cast_zero, zero_div] at h
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    have hle : (u : ℝ) / Bn ≤ ((u + 1 : ℕ) : ℝ) / Bn := by gcongr; simp
    rw [intervalIntegral.integral_of_le hle, integral_Ioc_eq_integral_Ioo,
      setIntegral_congr_fun measurableSet_Ioo (g := fun _ => G u)]
    · simp only [setIntegral_const, Real.volume_real_Ioo_of_le hle, smul_eq_mul]
      push_cast
      field_simp
      ring
    · intro σ hσ
      simp only
      congr 1
      have h1 := hσ.1
      have h2 := hσ.2
      rw [div_lt_iff₀ hBpos] at h1
      rw [lt_div_iff₀ hBpos] at h2
      rw [Nat.floor_eq_iff (mul_nonneg hBpos.le (le_trans (by positivity) hσ.1.le))]
      constructor
      · push_cast at h2 ⊢; nlinarith
      · push_cast at h2 ⊢; nlinarith
  rw [hsplit, hlast, hfirst]

private lemma blk_spec_integral {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n)
    (φ : ℝ × ℝ → ℝ) :
    Integrable φ (specMeasure S Δ) ∧
      ∫ x, φ x ∂(specMeasure S Δ) = ∑ i, ∑ j, modeQ S Δ i j * φ (S.μ i, S.lam j) :=
  blk_atom_integral S.μ S.lam (modeQ S Δ) (fun i j => sq_nonneg _) φ

private lemma blk_modeQ_eq {m n : ℕ} {C : Covariances m n} (SP : SpectralData C) (Y : Mat m n)
    (i : Fin m) (j : Fin n) :
    (SP.uOutᵀ * Y * SP.vIn) i j = SP.u i ⬝ᵥ (Y *ᵥ SP.v j) := by
  simp only [Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, SpectralData.u,
    SpectralData.v, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

private lemma blk_Xfg_eq {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (Δ : Mat m n) :
    Xfg f g C Δ = ∫ x, tensorFG f g x ∂(specMeasure SP Δ) := by
  rw [(blk_spec_integral SP Δ (tensorFG f g)).2]
  unfold Xfg
  rw [block_G_spectral f g SP Δ]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [blk_modeQ_eq]
  unfold modeQ tensorFG
  ring

private lemma blk_riskOf_spec {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Δ : Mat m n) :
    riskOf (specMeasure S Δ) = riskSigma C Δ := by
  unfold riskOf riskSigma
  rw [(blk_spec_integral S Δ (fun x => x.1 * x.2)).2]
  have hsum : ∑ i, ∑ j, modeQ S Δ i j * (S.μ i * S.lam j) =
      ∑ i, ∑ j, S.μ i * S.lam j * modeQ S Δ i j := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hsum, ← lem_app_setup_decomposition_ii S Δ]
  ring

private lemma blk_fieldOp_spec {m n : ℕ} {C : Covariances m n} (p : DynParams) (SP : SpectralData C)
    {B : ℕ} (c : DynCoeff p SP B) (φ : ℝ × ℝ → ℝ) (Δ : Mat m n) :
    fieldOp p.h c.d c.ζ (specMeasure SP Δ) φ =
      if 0 < riskSigma C Δ then
        -(2 * p.h / Real.sqrt (riskSigma C Δ)) *
            (∑ i, ∑ j, modeQ SP Δ i j * (φ (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))) +
          p.h ^ 2 * ∫ x, φ x ∂c.ζ
      else 0 := by
  unfold fieldOp
  rw [blk_riskOf_spec]
  by_cases h : 0 < riskSigma C Δ
  · simp only [h, if_true]
    rw [(blk_spec_integral SP Δ (fun x => φ x * c.d x)).2]
  · simp [h]

private lemma blk_modeQ_cont {m n : ℕ} {C : Covariances m n} (SP : SpectralData C) (i : Fin m) (j : Fin n) :
    Continuous (fun Δ : Mat m n => modeQ SP Δ i j) := by
  unfold modeQ SpectralData.u SpectralData.v
  simp only [dotProduct, Matrix.mulVec]
  fun_prop

private lemma blk_fieldOp_meas {m n : ℕ} {C : Covariances m n} (p : DynParams) (SP : SpectralData C)
    {B : ℕ} (c : DynCoeff p SP B) (φ : ℝ × ℝ → ℝ) :
    Measurable (fun Δ : Mat m n => fieldOp p.h c.d c.ζ (specMeasure SP Δ) φ) := by
  simp_rw [blk_fieldOp_spec p SP c φ]
  refine Measurable.ite (measurableSet_lt measurable_const (block_risk_cont C).measurable) ?_ measurable_const
  have h1 : Measurable (fun Δ : Mat m n => riskSigma C Δ) := (block_risk_cont C).measurable
  refine Measurable.add (Measurable.mul ?_ ?_) measurable_const
  · exact (measurable_const.div h1.sqrt).neg
  · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact ((blk_modeQ_cont SP i j).measurable).mul_const _

/-- The block exit index of a generic path `ψ` (the path version of `blockExitIdx`). -/
private def blkExit {m n : ℕ} (p : DynParams) (C : Covariances m n) (L : ℕ) (ψ : ℕ → Mat m n) : ℕ∞ :=
  ⨅ (b : ℕ) (_ : ψ (b * L) ∉ admA p C), (b : ℕ∞)

/-- Field value along a path: `F_u = F_B(χ(ψ_u))(f ⊗ g)`. -/
private def blkF {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (ψ : ℕ → Mat m n) (u : ℕ) : ℝ :=
  fieldOp p.h c.d c.ζ (specMeasure S (ψ u)) (tensorFG f g)

/-- Discrete residual along a path: `X(ψ_N) − X(ψ_0) − (1/B) ∑_{u<N} F_u`. -/
private def blkU {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (ψ : ℕ → Mat m n) (N : ℕ) : ℝ :=
  Xfg f g C (ψ N) - Xfg f g C (ψ 0) - (1 / (B : ℝ)) * ∑ u ∈ Finset.range N, blkF p S c f g ψ u

/-- The residual of `lem:app-dyn-block` for a generic path `ψ` at the stopped macro time `s`. -/
private lemma blk_res_le {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (ψ : ℕ → Mat m n) (hB : 0 < B) (s : ℝ) (hs : 0 ≤ s) :
    |(∫ x, tensorFG f g x ∂(actMeasure S B ψ s)) - (∫ x, tensorFG f g x ∂(actMeasure S B ψ 0))
      - ∫ σ in (0 : ℝ)..s, fieldOp p.h c.d c.ζ (actMeasure S B ψ σ) (tensorFG f g)| ≤
      |blkU p S c f g ψ ⌊(B : ℝ) * s⌋₊| + |blkF p S c f g ψ ⌊(B : ℝ) * s⌋₊| / B := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  set N := ⌊(B : ℝ) * s⌋₊ with hN
  have hNle : (N : ℝ) ≤ (B : ℝ) * s := Nat.floor_le (by positivity)
  have hNlt : (B : ℝ) * s < N + 1 := Nat.lt_floor_add_one _
  have e1 : ∫ x, tensorFG f g x ∂(actMeasure S B ψ s) = Xfg f g C (ψ N) :=
    (blk_Xfg_eq f g S (ψ N)).symm
  have e0 : ∫ x, tensorFG f g x ∂(actMeasure S B ψ 0) = Xfg f g C (ψ 0) := by
    have : ⌊(B : ℝ) * 0⌋₊ = 0 := by simp
    unfold actMeasure
    rw [this]
    exact (blk_Xfg_eq f g S (ψ 0)).symm
  have eI : ∫ σ in (0 : ℝ)..s, fieldOp p.h c.d c.ζ (actMeasure S B ψ σ) (tensorFG f g) =
      (1 / (B : ℝ)) * ∑ u ∈ Finset.range N, blkF p S c f g ψ u +
        (s - (N : ℝ) / B) * blkF p S c f g ψ N :=
    blk_stepfun_integral (fun u => blkF p S c f g ψ u) B hB s hs
  rw [e1, e0, eI]
  have hfr0 : 0 ≤ s - (N : ℝ) / B := by
    rw [sub_nonneg, div_le_iff₀ hBpos]; linarith
  have hfr1 : s - (N : ℝ) / B ≤ 1 / B := by
    have : s - (N : ℝ) / B = ((B : ℝ) * s - N) / B := by field_simp
    rw [this]
    exact div_le_div_of_nonneg_right (by linarith) hBpos.le
  have hrw : Xfg f g C (ψ N) - Xfg f g C (ψ 0) -
      ((1 / (B : ℝ)) * ∑ u ∈ Finset.range N, blkF p S c f g ψ u + (s - (N : ℝ) / B) * blkF p S c f g ψ N)
      = blkU p S c f g ψ N - (s - (N : ℝ) / B) * blkF p S c f g ψ N := by
    unfold blkU; ring
  rw [hrw]
  refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
  rw [abs_mul, abs_of_nonneg hfr0]
  calc (s - (N : ℝ) / B) * |blkF p S c f g ψ N| ≤ (1 / (B : ℝ)) * |blkF p S c f g ψ N| :=
        mul_le_mul_of_nonneg_right hfr1 (abs_nonneg _)
    _ = |blkF p S c f g ψ N| / B := by ring

/-- The stopped macro time never exceeds the exit block: the blocks `b L < ⌊B s⌋` are all in `𝒜`. -/
private lemma blk_stop_good {m n : ℕ} (p : DynParams) (C : Covariances m n) (L Bn : ℕ) (hBn : 0 < Bn)
    (ψ : ℕ → Mat m n) (τ : ℝ) (hτ : 0 ≤ τ) :
    0 ≤ stopMacro L Bn (blkExit p C L ψ) τ ∧ stopMacro L Bn (blkExit p C L ψ) τ ≤ τ ∧
      ∀ b : ℕ, b * L < ⌊(Bn : ℝ) * stopMacro L Bn (blkExit p C L ψ) τ⌋₊ → ψ (b * L) ∈ admA p C := by
  have hBpos : (0 : ℝ) < Bn := by exact_mod_cast hBn
  unfold stopMacro
  by_cases htop : blkExit p C L ψ = ⊤
  · simp only [htop, if_true]
    refine ⟨hτ, le_rfl, fun b hb => ?_⟩
    by_contra hnot
    have : blkExit p C L ψ ≤ (b : ℕ∞) := iInf₂_le b hnot
    rw [htop] at this
    exact absurd this (by simp)
  · simp only [htop, if_false]
    refine ⟨le_min hτ (by positivity), min_le_left _ _, fun b hb => ?_⟩
    by_contra hnot
    have hle : blkExit p C L ψ ≤ (b : ℕ∞) := iInf₂_le b hnot
    have hto : (blkExit p C L ψ).toNat ≤ b := ENat.toNat_le_of_le_natCast hle
    have hfl : ⌊(Bn : ℝ) * min τ ((L : ℝ) * ((blkExit p C L ψ).toNat : ℝ) / (Bn : ℝ))⌋₊ ≤ L * b := by
      have h1 : (Bn : ℝ) * min τ ((L : ℝ) * ((blkExit p C L ψ).toNat : ℝ) / (Bn : ℝ)) ≤ (L * b : ℕ) := by
        calc (Bn : ℝ) * min τ ((L : ℝ) * ((blkExit p C L ψ).toNat : ℝ) / (Bn : ℝ))
            ≤ (Bn : ℝ) * ((L : ℝ) * ((blkExit p C L ψ).toNat : ℝ) / (Bn : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hBpos.le
          _ = (L : ℝ) * ((blkExit p C L ψ).toNat : ℝ) := by field_simp
          _ ≤ (L * b : ℕ) := by push_cast; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hto) (Nat.cast_nonneg L)
      exact Nat.floor_le_of_le h1
    rw [mul_comm b L] at hb
    omega

private lemma blk_cont_fro_sq {m n : ℕ} : Continuous (fun D : Mat m n => fro D ^ 2) := by
  unfold fro
  fun_prop

private lemma blk_admSet_meas {m n : ℕ} (C : Covariances m n) (t : ℝ × ℝ × ℝ) :
    MeasurableSet (admSetOf C t) := by
  have hr : Measurable (fun D : Mat m n => riskSigma C D) := (block_risk_cont C).measurable
  have hf : Measurable (fun D : Mat m n => fro D ^ 2) := blk_cont_fro_sq.measurable
  exact (measurableSet_le measurable_const hr).inter
    ((measurableSet_le hr measurable_const).inter (measurableSet_le hf measurable_const))

private lemma blk_admA_meas {m n : ℕ} (p : DynParams) (C : Covariances m n) :
    MeasurableSet (admA p C) := blk_admSet_meas C _

open Classical in
/-- The measurable majorant of the sup of residuals: the maximum over `N ≤ TB` of
`1[blocks before `N` in 𝒜] (|U_N| + |F_N|/B)`. -/
private def blkPsi {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (L : ℕ) (T : ℝ) (ψ : ℕ → Mat m n) : ℝ :=
  (Finset.range (⌊T * (B : ℝ)⌋₊ + 1)).sup' ⟨0, Finset.mem_range.2 (Nat.succ_pos _)⟩ (fun N =>
    if ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C then
      |blkU p S c f g ψ N| + |blkF p S c f g ψ N| / (B : ℝ) else 0)

private lemma blk_res_le_psi {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (L : ℕ) (T : ℝ) (ψ : ℕ → Mat m n) (hB : 0 < B)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) T) :
    |(∫ x, tensorFG f g x ∂(actMeasure S B ψ (stopMacro L B (blkExit p C L ψ) τ))) -
        (∫ x, tensorFG f g x ∂(actMeasure S B ψ 0)) -
        ∫ σ in (0 : ℝ)..(stopMacro L B (blkExit p C L ψ) τ),
          fieldOp p.h c.d c.ζ (actMeasure S B ψ σ) (tensorFG f g)| ≤ blkPsi p S c f g L T ψ := by
  classical
  obtain ⟨hs0, hsτ, hgood⟩ := blk_stop_good p C L B hB ψ τ hτ.1
  refine (blk_res_le p S c f g ψ hB _ hs0).trans ?_
  unfold blkPsi
  have hN : ⌊(B : ℝ) * stopMacro L B (blkExit p C L ψ) τ⌋₊ ∈ Finset.range (⌊T * (B : ℝ)⌋₊ + 1) := by
    refine Finset.mem_range.2 (Nat.lt_succ_of_le (Nat.floor_le_floor ?_))
    rw [mul_comm T]
    exact mul_le_mul_of_nonneg_left (hsτ.trans hτ.2) (Nat.cast_nonneg B)
  refine le_trans ?_ (Finset.le_sup' (f := fun N =>
    if ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C then
      |blkU p S c f g ψ N| + |blkF p S c f g ψ N| / (B : ℝ) else 0) hN)
  have hcond : ∀ b ∈ Finset.range ⌊(B : ℝ) * stopMacro L B (blkExit p C L ψ) τ⌋₊,
      b * L < ⌊(B : ℝ) * stopMacro L B (blkExit p C L ψ) τ⌋₊ → ψ (b * L) ∈ admA p C :=
    fun b _ hb => hgood b hb
  rw [if_pos hcond]

private lemma blk_psi_meas {m n B : ℕ} {C : Covariances m n} (p : DynParams) (S : SpectralData C)
    (c : DynCoeff p S B) (f g : ℝ → ℝ) (L : ℕ) (T : ℝ) :
    Measurable (blkPsi p S c f g L T : (ℕ → Mat m n) → ℝ) := by
  classical
  unfold blkPsi
  refine Finset.measurable_range_sup'' (n := ⌊T * (B : ℝ)⌋₊) (δ := ℕ → Mat m n)
    (f := fun N (ψ : ℕ → Mat m n) =>
      if ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C then
        |blkU p S c f g ψ N| + |blkF p S c f g ψ N| / (B : ℝ) else 0) ?_
  intro N _
  have hev : ∀ t : ℕ, Measurable (fun ψ : ℕ → Mat m n => ψ t) := fun t => measurable_pi_apply t
  have hX : ∀ t : ℕ, Measurable (fun ψ : ℕ → Mat m n => Xfg f g C (ψ t)) := fun t =>
    (block_Xfg_cont f g C).measurable.comp (hev t)
  have hF : ∀ t : ℕ, Measurable (fun ψ : ℕ → Mat m n => blkF p S c f g ψ t) := fun t =>
    (blk_fieldOp_meas p S c (tensorFG f g)).comp (hev t)
  refine Measurable.ite ?_ ?_ measurable_const
  · have : {ψ : ℕ → Mat m n | ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C} =
        ⋂ b ∈ Finset.range N, {ψ : ℕ → Mat m n | b * L < N → ψ (b * L) ∈ admA p C} := by
      ext ψ; simp
    rw [this]
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun b _ => ?_
    by_cases hb : b * L < N
    · simp only [hb, true_implies]
      exact (hev (b * L)) (blk_admA_meas p C)
    · simp [hb]
  · have hU : Measurable (fun ψ : ℕ → Mat m n => blkU p S c f g ψ N) := by
      unfold blkU
      exact ((hX N).sub (hX 0)).sub (measurable_const.mul
        (Finset.measurable_sum _ fun u _ => hF u))
    exact hU.abs.add ((hF N).abs.div_const _)

private lemma blk_prob_hyp {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)} (hyp : DynHyp p P m n B C) :
    IsProbabilityMeasure P := by
  have hev : ∀ᶠ k in atTop, 1 ≤ B k := hyp.regime.B_top.eventually (eventually_ge_atTop 1)
  obtain ⟨k, hk⟩ := hev.exists
  let a : Fin (B k) := ⟨0, hk⟩
  refine IsProbabilityMeasure.mk ?_
  have hlaw := (hyp.iid k 0).law a
  have hm := Measure.map_apply_of_aemeasurable ((hyp.iid k 0).meas a) MeasurableSet.univ
  rw [hlaw] at hm
  haveI : IsProbabilityMeasure (dataTarget (C k)) := by unfold dataTarget; infer_instance
  simpa only [Set.preimage_univ, IsProbabilityMeasure.measure_univ] using hm.symm

private lemma blk_run_aem {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (C : Covariances m n) (p : AlgParams m n) (W0 : Mat m n) (M : Ω → Mat m n)
    (hM : AEMeasurable M P) (x : ℕ → Ω → Batch m n B)
    (hx : ∀ u a, AEMeasurable (fun ω => x u ω a) P) (t : ℕ) :
    AEMeasurable (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).W) P ∧
      AEMeasurable (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).Mprev) P := by
  classical
  -- measurable versions
  let xm : ℕ → Ω → Batch m n B := fun u ω a => (hx u a).mk _ ω
  let Mm : Ω → Mat m n := hM.mk M
  have hxm : ∀ u, Measurable (xm u) := fun u =>
    block_pi_meas (fun a => (hx u a).measurable_mk)
  have hMm : Measurable Mm := hM.measurable_mk
  have hae : ∀ᵐ ω ∂P, ∀ u, x u ω = xm u ω := by
    have h1 : ∀ u a, ∀ᵐ ω ∂P, x u ω a = xm u ω a := fun u a => (hx u a).ae_eq_mk
    refine ae_all_iff.2 fun u => ?_
    have := ae_all_iff.2 (h1 u)
    filter_upwards [this] with ω hω
    funext a; exact hω a
  have hae2 : ∀ᵐ ω ∂P, M ω = Mm ω := hM.ae_eq_mk
  have hmeas : Measurable (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).W) ∧
      Measurable (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).Mprev) := by
    induction t with
    | zero => exact ⟨measurable_const, hMm⟩
    | succ k ih =>
      exact block_step_meas (σ := mΩ) C p k (fun ω => run C p (initState W0 (Mm ω)) (fun u => xm u ω) k)
        (xm k) ih.1 ih.2 (hxm k)
  have hrun : ∀ᵐ ω ∂P, run C p (initState W0 (M ω)) (fun u => x u ω) t =
      run C p (initState W0 (Mm ω)) (fun u => xm u ω) t := by
    filter_upwards [hae, hae2] with ω h1 h2
    have hx' : (fun u => x u ω) = (fun u => xm u ω) := funext h1
    rw [hx', h2]
  have e1 : (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).W) =ᵐ[P]
      (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).W) :=
    hrun.mono (fun ω h => by simp only [h])
  have e2 : (fun ω => (run C p (initState W0 (M ω)) (fun u => x u ω) t).Mprev) =ᵐ[P]
      (fun ω => (run C p (initState W0 (Mm ω)) (fun u => xm u ω) t).Mprev) :=
    hrun.mono (fun ω h => by simp only [h])
  exact ⟨hmeas.1.aemeasurable.congr e1.symm, hmeas.2.aemeasurable.congr e2.symm⟩

private lemma blk_errPath_aem {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k : ℕ, Covariances (m k) (n k)} (hyp : DynHyp p P m n B C) (k t : ℕ) :
    AEMeasurable (errPath hyp k t) P := by
  have h := (blk_run_aem (C k) (hyp.alg k) (hyp.W0 k) (hyp.Mm1 k) (hyp.Mm1_meas k) (hyp.x k)
    (fun u a => (hyp.iid k u).meas a) t).1
  have hc : Continuous (fun A : Mat (m k) (n k) => A - (hyp.alg k).Wstar) :=
    continuous_id.sub continuous_const
  exact hc.measurable.comp_aemeasurable h

private lemma blk_paths_ae {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ → ℕ} {C : ∀ k, Covariances (m k) (n k)} (hyp : DynHyp p P m n B C) (k : ℕ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} (pi : Ω' → Ω)
    (S : DynSetup p P' (m k) (n k) (B k))
    (hC : S.C = C k) (hA : S.alg = hyp.alg k) (hW : S.W0 = hyp.W0 k)
    (hM : S.M0 =ᵐ[P'] (hyp.Mm1 k ∘ pi)) (hx : ∀ u, dynBatch S u =ᵐ[P'] (hyp.x k u ∘ pi)) :
    ∀ᵐ ω' ∂P', ∀ t, dynDelta S t ω' = errPath hyp k t (pi ω') := by
  have hx' : ∀ᵐ ω' ∂P', ∀ u, dynBatch S u ω' = hyp.x k u (pi ω') := ae_all_iff.2 hx
  filter_upwards [hx', hM] with ω' h1 h2 t
  have h1' : (fun u => dynBatch S u ω') = (fun u => hyp.x k u (pi ω')) := funext h1
  simp only [dynDelta, devRand, runRand, dynStart, errPath, h1', h2, Function.comp_apply]
  rw [hC, hA, hW]

/-- Transfer of probabilities of path events along a measure-preserving extension. -/
private lemma blk_transfer {Ω Ω' : Type} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
    {P' : Measure Ω'} {M : Type} [MeasurableSpace M] (pi : Ω' → Ω) (hpi : MeasurePreserving pi P' P)
    (γ : ℕ → Ω → M) (hγ : ∀ t, AEMeasurable (γ t) P) (Γ' : ℕ → Ω' → M)
    (hae : ∀ᵐ ω' ∂P', ∀ t, Γ' t ω' = γ t (pi ω'))
    (Φ : (ℕ → M) → ℝ) (hΦ : Measurable Φ) (a : ℝ) :
    P {ω | a < Φ (fun t => γ t ω)} = P' {ω' | a < Φ (fun t => Γ' t ω')} := by
  have hγ' : AEMeasurable (fun ω t => γ t ω) P := AEMeasurable.of_eval hγ
  have hG : NullMeasurableSet {ω | a < Φ (fun t => γ t ω)} P := by
    have : {ω | a < Φ (fun t => γ t ω)} = (fun ω t => γ t ω) ⁻¹' (Φ ⁻¹' Set.Ioi a) := rfl
    rw [this]
    exact (hγ'.nullMeasurable) (hΦ measurableSet_Ioi)
  rw [← hpi.measure_preimage hG]
  refine measure_congr ?_
  filter_upwards [hae] with ω' h
  have : (fun t => Γ' t ω') = fun t => γ t (pi ω') := funext h
  simp only [Set.mem_preimage, Set.mem_setOf_eq, this]

private lemma blk_diag_delta (a : ℕ → ℝ → ℝ≥0∞) (Bk : ℕ → ℕ)
    (ha : ∀ ε : ℝ, 0 < ε → Tendsto (fun k => a k ε) atTop (𝓝 0))
    (hB : Tendsto Bk atTop atTop) :
    ∃ δ : ℕ → ℝ, Antitone δ ∧ (∀ i, 0 < δ i) ∧ Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun k => a k (δ (Bk k))) atTop (𝓝 0) := by
  classical
  set eps : ℕ → ℝ := fun j => ((j : ℝ) + 1)⁻¹ with heps
  have hepspos : ∀ j, 0 < eps j := fun j => by simp only [heps]; positivity
  have hK : ∀ j, ∃ K : ℕ, ∀ k ≥ K, a k (eps j) ≤ ENNReal.ofReal (eps j) := by
    intro j
    have h := ha (eps j) (hepspos j)
    have h2 := (ENNReal.tendsto_nhds_zero.1 h) (ENNReal.ofReal (eps j))
      (ENNReal.ofReal_pos.2 (hepspos j))
    exact eventually_atTop.1 h2
  choose K hK using hK
  set Kp : ℕ → ℕ := fun j => ∑ i ∈ Finset.range (j + 1), K i with hKp
  have hKpK : ∀ j, K j ≤ Kp j := fun j =>
    Finset.single_le_sum (f := K) (fun _ _ => Nat.zero_le _) (Finset.self_mem_range_succ j)
  have hKpmono : Monotone Kp := fun i j hij =>
    Finset.sum_le_sum_of_subset (Finset.range_mono (Nat.succ_le_succ hij))
  set Bth : ℕ → ℕ := fun j => j + 1 + (Finset.range (Kp j)).sup Bk with hBth
  have hBthj : ∀ j, j < Bth j := fun j => by simp only [hBth]; omega
  have hkey : ∀ j k, Bth j ≤ Bk k → Kp j ≤ k := by
    intro j k h
    by_contra hlt
    simp only [not_le] at hlt
    have : Bk k ≤ (Finset.range (Kp j)).sup Bk := Finset.le_sup (Finset.mem_range.2 hlt)
    simp only [hBth] at h
    omega
  have hBthmono : Monotone Bth := by
    intro i j hij
    simp only [hBth]
    have : (Finset.range (Kp i)).sup Bk ≤ (Finset.range (Kp j)).sup Bk :=
      Finset.sup_mono (Finset.range_mono (hKpmono hij))
    omega
  set S : ℕ → Finset ℕ := fun b => (Finset.range (b + 1)).filter (fun j => Bth j ≤ b) with hS
  set J : ℕ → ℕ := fun b => (S b).sup id with hJ
  have hSmono : ∀ b b', b ≤ b' → S b ⊆ S b' := by
    intro b b' hbb j hj
    simp only [hS, Finset.mem_filter, Finset.mem_range] at hj ⊢
    omega
  have hJmono : Monotone J := fun b b' hbb => Finset.sup_mono (hSmono b b' hbb)
  have hmem : ∀ j b, Bth j ≤ b → j ∈ S b := by
    intro j b h
    have := hBthj j
    simp only [hS, Finset.mem_filter, Finset.mem_range]
    omega
  have hJge : ∀ j b, Bth j ≤ b → j ≤ J b := fun j b h =>
    Finset.le_sup (f := id) (hmem j b h)
  have hJspec : ∀ j b, Bth j ≤ b → Bth (J b) ≤ b := by
    intro j b h
    obtain ⟨j', hj', hjj⟩ := Finset.exists_mem_eq_sup (S b) ⟨j, hmem j b h⟩ id
    have : J b = j' := hjj
    rw [this]
    simp only [hS, Finset.mem_filter] at hj'
    exact hj'.2
  refine ⟨fun b => eps (J b), ?_, fun i => hepspos _, ?_, ?_⟩
  · intro b b' hbb
    simp only [heps]
    have := hJmono hbb
    gcongr
  · -- tends to zero
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨j0, hj0⟩ := exists_nat_one_div_lt hε
    refine ⟨Bth j0, fun b hb => ?_⟩
    have h1 : j0 ≤ J b := hJge j0 b hb
    rw [Real.dist_eq, sub_zero, abs_of_pos (hepspos _)]
    calc eps (J b) ≤ eps j0 := by simp only [heps]; gcongr
      _ < ε := by simpa [heps, one_div] using hj0
  · rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨j0, hj0⟩ := ENNReal.exists_inv_nat_lt hε.ne'
    have hev : ∀ᶠ k in atTop, Bth j0 ≤ Bk k := hB.eventually (eventually_ge_atTop _)
    filter_upwards [hev] with k hk
    have hs := hJspec j0 (Bk k) hk
    have hj := hJge j0 (Bk k) hk
    have hk' : K (J (Bk k)) ≤ k := (hKpK _).trans (hkey _ _ hs)
    refine (hK _ k hk').trans ?_
    refine le_trans ?_ hj0.le
    have he : ENNReal.ofReal (eps (J (Bk k))) = ((J (Bk k) + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      simp only [heps]
      have h : ((J (Bk k) : ℝ) + 1) = ((J (Bk k) + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [h, ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
    rw [he]
    exact ENNReal.inv_le_inv.2 (Nat.cast_le.2 (by omega))


private lemma blk_uniform_eventual {m n : ℕ → ℕ} (C : ∀ k : ℕ, Covariances (m k) (n k))
    (e : ∀ k : ℕ, Mat (m k) (n k) → ℝ)
    (e_to_zero : ∀ φ : ℕ → ℕ, StrictMono φ → ∀ A : ∀ j : ℕ, Mat (m (φ j)) (n (φ j)),
      (∀ j : ℕ, A j ∈ NormStates (C (φ j))) →
      Tendsto (fun j : ℕ => opNorm (A j)) atTop (𝓝 0) →
      Tendsto (fun j : ℕ => e (φ j) (A j)) atTop (𝓝 0))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ A ∈ NormStates (C k), opNorm A ≤ δ k → e k A ≤ ε := by
  intro ε hε
  by_contra h
  have hbad : ∃ᶠ k in atTop, ∃ A : Mat (m k) (n k),
      A ∈ NormStates (C k) ∧ opNorm A ≤ δ k ∧ ε < e k A := by
    simpa only [not_forall, not_imp, not_le, exists_prop, and_assoc] using
      (Filter.not_eventually.mp h)
  obtain ⟨φ, hφ, hbadφ⟩ := Filter.extraction_of_frequently_atTop hbad
  choose A hA hnorm he using hbadφ
  have hAz : Tendsto (fun j => opNorm (A j)) atTop (𝓝 0) :=
    squeeze_zero (fun j => by unfold opNorm; exact norm_nonneg _) hnorm
      (hδ.comp hφ.tendsto_atTop)
  have hez := e_to_zero φ hφ A hA hAz
  obtain ⟨j, hj⟩ := ((tendsto_order.mp hez).2 ε hε).exists
  exact (he j).not_gt hj

open scoped Matrix.Norms.L2Operator in
private lemma blk_abs_eig_le_opNorm {k : ℕ} (A : Matrix (Fin k) (Fin k) ℝ) (w : Fin k → ℝ) (μ : ℝ)
    (hw : ∑ a, w a * w a = 1) (he : A *ᵥ w = μ • w) : |μ| ≤ opNorm A := by
  set x : EuclideanSpace ℝ (Fin k) := (EuclideanSpace.equiv (Fin k) ℝ).symm w with hxdef
  have hsum : ∑ a, ‖x a‖ ^ 2 = 1 := by
    have hterm : ∀ a, ‖x a‖ ^ 2 = w a * w a := fun a => by
      rw [Real.norm_eq_abs, sq_abs, sq]
      rfl
    simp only [hterm]
    exact hw
  have hx : ‖x‖ = 1 := by rw [EuclideanSpace.norm_eq, hsum, Real.sqrt_one]
  have h1 := Matrix.l2_opNorm_mulVec A x
  have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (A *ᵥ ⇑x) = μ • x := by
    ext a
    have ha := congrFun he a
    simp only [hxdef, Pi.smul_apply, smul_eq_mul] at ha ⊢
    exact ha
  rw [h2, norm_smul, hx, Real.norm_eq_abs] at h1
  simp only [mul_one] at h1
  rw [opNorm_eq_norm]
  exact h1

private lemma blk_spec_mem {m n : ℕ} {C : Covariances m n} (S : SpectralData C) (Cs : ℝ)
    (hout : opNorm C.Sout ≤ Cs) (hin : opNorm C.Sin ≤ Cs) :
    (∀ i, S.μ i ∈ Icc (0 : ℝ) Cs) ∧ (∀ j, S.lam j ∈ Icc (0 : ℝ) Cs) :=
  ⟨fun i => ⟨μ_nonneg S i, (le_abs_self _).trans ((blk_abs_eig_le_opNorm C.Sout (fun a => S.uOut a i)
      (S.μ i) (sum_col_sq_eq_one S.uOut S.huOut i) (S.eigOut i)).trans hout)⟩,
   fun j => ⟨lam_nonneg S j, (le_abs_self _).trans ((blk_abs_eig_le_opNorm C.Sin (fun a => S.vIn a j)
      (S.lam j) (sum_col_sq_eq_one S.vIn S.hvIn j) (S.eigIn j)).trans hin)⟩⟩

private lemma blk_modeQ_sum {m n : ℕ} {C : Covariances m n} (S : SpectralData C)
    (Δ : Mat m n) : ∑ i, ∑ j, modeQ S Δ i j = fro Δ ^ 2 := by
  have ht : ∀ {a b : ℕ} (Y : Mat a b), (Y * Matrix.transpose Y).trace = fro Y ^ 2 := by
    intro a b Y
    rw [block_fro_sq_eq]
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
  have he : fro (Matrix.transpose S.uOut * Δ * S.vIn) ^ 2 = fro Δ ^ 2 := by
    rw [← ht, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc S.vIn (Matrix.transpose S.vIn), mul_eq_one_comm.mp S.hvIn,
      Matrix.one_mul]
    rw [Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
    rw [mul_eq_one_comm.mp S.huOut, Matrix.mul_one, ht]
  rw [← he, block_fro_sq_eq]
  simp_rw [P_apply, modeQ]

private lemma blk_fro_nn {m n : ℕ} (A : Mat m n) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma blk_modeQ_diff_sum {m n : ℕ} {C' : Covariances m n} (S : SpectralData C')
    (D D' : Mat m n) :
    ∑ i, ∑ j, |modeQ S D' i j - modeQ S D i j| ≤ fro (D' - D) * (fro D' + fro D) := by
  have hlin : ∀ (X Y : Mat m n) i j, S.u i ⬝ᵥ ((X + Y) *ᵥ S.v j) =
      S.u i ⬝ᵥ (X *ᵥ S.v j) + S.u i ⬝ᵥ (Y *ᵥ S.v j) := by
    intro X Y i j
    rw [Matrix.add_mulVec, dotProduct_add]
  have hlin' : ∀ (X Y : Mat m n) i j, S.u i ⬝ᵥ ((X - Y) *ᵥ S.v j) =
      S.u i ⬝ᵥ (X *ᵥ S.v j) - S.u i ⬝ᵥ (Y *ᵥ S.v j) := by
    intro X Y i j
    rw [Matrix.sub_mulVec, dotProduct_sub]
  have hterm : ∀ i j, |modeQ S D' i j - modeQ S D i j| =
      |S.u i ⬝ᵥ ((D' - D) *ᵥ S.v j)| * |S.u i ⬝ᵥ ((D' + D) *ᵥ S.v j)| := by
    intro i j
    rw [← abs_mul, hlin', hlin]
    unfold modeQ
    congr 1
    ring
  have hsq : ∀ X : Mat m n, ∑ i, ∑ j, |S.u i ⬝ᵥ (X *ᵥ S.v j)| ^ 2 = fro X ^ 2 := by
    intro X
    rw [← blk_modeQ_sum S X]
    simp [modeQ, sq_abs]
  have h1 : ∑ i, ∑ j, |modeQ S D' i j - modeQ S D i j| =
      ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' - D) *ᵥ S.v x.2)| *
        |S.u x.1 ⬝ᵥ ((D' + D) *ᵥ S.v x.2)| := by
    rw [Fintype.sum_prod_type]
    simp_rw [hterm]
  rw [h1]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  have e1 : ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' - D) *ᵥ S.v x.2)| ^ 2 = fro (D' - D) ^ 2 := by
    rw [Fintype.sum_prod_type]; exact hsq _
  have e2 : ∑ x : Fin m × Fin n, |S.u x.1 ⬝ᵥ ((D' + D) *ᵥ S.v x.2)| ^ 2 = fro (D' + D) ^ 2 := by
    rw [Fintype.sum_prod_type]; exact hsq _
  rw [e1, e2, Real.sqrt_sq (blk_fro_nn _), Real.sqrt_sq (blk_fro_nn _)]
  refine mul_le_mul_of_nonneg_left ?_ (blk_fro_nn _)
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  exact norm_add_le _ _

private lemma blk_fro_le_add {m n : ℕ} (D D' : Mat m n) : fro D' ≤ fro D + fro (D' - D) := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  have := norm_add_le D (D' - D)
  rwa [add_sub_cancel] at this

private lemma blk_fro_sub_triangle {m n : ℕ} (A B' C : Mat m n) : fro (A - C) ≤ fro (A - B') + fro (B' - C) := by
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  have := norm_add_le (A - B') (B' - C)
  rwa [sub_add_sub_cancel] at this

private lemma blk_inv_sqrt_diff {r x y : ℝ} (hr : 0 < r) (hx : r ≤ x) (hy : r ≤ y) :
    |1 / Real.sqrt x - 1 / Real.sqrt y| ≤ (1 / (Real.sqrt r) ^ 3) * |x - y| := by
  have hs := Real.sqrt_pos.2 hr
  have hxs := Real.sqrt_le_sqrt hx
  have hys := Real.sqrt_le_sqrt hy
  have hx0 : 0 < Real.sqrt x := lt_of_lt_of_le hs hxs
  have hy0 : 0 < Real.sqrt y := lt_of_lt_of_le hs hys
  have he : 1 / Real.sqrt x - 1 / Real.sqrt y =
      (y - x) / (Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y)) := by
    apply (eq_div_iff (by positivity)).2
    field_simp
    nlinarith [Real.sq_sqrt (hr.le.trans hx), Real.sq_sqrt (hr.le.trans hy)]
  have hd : (Real.sqrt r) ^ 3 ≤
      Real.sqrt x * Real.sqrt y * (Real.sqrt x + Real.sqrt y) := by
    have h1 := mul_le_mul hxs hys hs.le (Real.sqrt_nonneg x)
    have h2 := mul_le_mul h1 (show Real.sqrt r ≤ Real.sqrt x + Real.sqrt y by linarith)
      hs.le (mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y))
    nlinarith
  rw [he, abs_div, abs_of_pos (show 0 < Real.sqrt x * Real.sqrt y *
    (Real.sqrt x + Real.sqrt y) by positivity), abs_sub_comm y x]
  calc
    _ ≤ |x - y| / (Real.sqrt r) ^ 3 :=
      div_le_div_of_nonneg_left (abs_nonneg _) (by positivity) hd
    _ = _ := by ring

private lemma blk_atom_mass {m n : ℕ} (μ : Fin m → ℝ) (lam : Fin n → ℝ)
    (q : Fin m → Fin n → ℝ) (hq : ∀ i j, 0 ≤ q i j) :
    (atomMeasure μ lam q).real univ = ∑ i, ∑ j, q i j := by
  unfold atomMeasure
  rw [Measure.real_def]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.sum_ne_top.mpr fun j _ => ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.toReal_sum (fun j _ => ENNReal.ofReal_ne_top)]
  exact Finset.sum_congr rfl fun j _ => ENNReal.toReal_ofReal (hq i j)

private lemma blk_risk_sum {m n : ℕ} {C : Covariances m n} (SP : SpectralData C) (Δ : Mat m n) :
    riskSigma C Δ = (1 / 2) * ∑ i, ∑ j, SP.μ i * SP.lam j * modeQ SP Δ i j := by
  unfold riskSigma
  have := lem_app_setup_decomposition_ii SP Δ
  linarith

section atomicfield

variable {m n B : ℕ} {C : Covariances m n}

private lemma blk_phi_le (p : DynParams) (SP : SpectralData C)
    (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (i : Fin m) (j : Fin n) : |tensorFG f g (SP.μ i, SP.lam j)| ≤ 1 := by
  obtain ⟨hμ, hl⟩ := blk_spec_mem SP p.CSig hout hin
  unfold tensorFG
  rw [abs_mul]
  exact mul_le_one₀ (hf _ (hμ i)) (abs_nonneg _) (hg _ (hl j))

private lemma blk_d_atom (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig) (i : Fin m) (j : Fin n) :
    0 ≤ c.d (SP.μ i, SP.lam j) ∧ c.d (SP.μ i, SP.lam j) ≤ dMax p := by
  obtain ⟨hμ, hl⟩ := blk_spec_mem SP p.CSig hout hin
  have hx : (SP.μ i, SP.lam j) ∈ specRect p.CSig := ⟨hμ i, hl j⟩
  exact ⟨c.d_nonneg _ hx, c.d_le _ hx⟩

private lemma blk_zeta_atoms (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (φ : ℝ × ℝ → ℝ) :
    ∫ x, φ x ∂c.ζ = ∑ i, ∑ j, (c.v i j / (B : ℝ)) * φ (SP.μ i, SP.lam j) := by
  rw [c.ζ_eq]
  exact (blk_atom_integral SP.μ SP.lam _ (fun i j => div_nonneg (c.v_nonneg i j) (Nat.cast_nonneg B)) φ).2

private lemma blk_zeta_atoms_bound (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (φ : ℝ × ℝ → ℝ) (hφ : ∀ i j, |φ (SP.μ i, SP.lam j)| ≤ 1) :
    |∑ i, ∑ j, (c.v i j / (B : ℝ)) * φ (SP.μ i, SP.lam j)| ≤ mZeta p := by
  have hnn : ∀ i j, 0 ≤ c.v i j / (B : ℝ) := fun i j => div_nonneg (c.v_nonneg i j) (Nat.cast_nonneg B)
  have hmass : ∑ i, ∑ j, c.v i j / (B : ℝ) ≤ mZeta p := by
    rw [← blk_atom_mass SP.μ SP.lam _ hnn, ← c.ζ_eq]
    exact c.ζ_mass
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _)) ?_
  refine le_trans (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) hmass
  rw [abs_mul, abs_of_nonneg (hnn i j)]
  exact mul_le_of_le_one_right (hnn i j) (hφ i j)

private lemma blk_F_formula (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B) (f g : ℝ → ℝ)
    (Δ : Mat m n) :
    fieldOp p.h c.d c.ζ (specMeasure SP Δ) (tensorFG f g) =
      if 0 < riskSigma C Δ then
        -(2 * p.h / Real.sqrt (riskSigma C Δ)) *
            (∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))) +
          p.h ^ 2 * ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j)
      else 0 := by
  rw [blk_fieldOp_spec, blk_zeta_atoms]

private lemma blk_A_bound (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (E : ℝ) (Δ : Mat m n) (hE : fro Δ ^ 2 ≤ E) :
    |∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))| ≤
      dMax p * E := by
  have hdM : 0 ≤ dMax p := by unfold dMax; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hterm : ∀ i j, |tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)| ≤ dMax p := by
    intro i j
    obtain ⟨h0, h1⟩ := blk_d_atom p SP c hout hin i j
    rw [abs_mul, abs_of_nonneg h0]
    calc _ ≤ 1 * dMax p := mul_le_mul (blk_phi_le p SP hout hin f g hf hg i j) h1 h0 zero_le_one
      _ = dMax p := one_mul _
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _)) ?_
  have hQ : ∀ i j, 0 ≤ modeQ SP Δ i j := fun i j => sq_nonneg _
  calc ∑ i, ∑ j, |modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))|
      ≤ ∑ i, ∑ j, modeQ SP Δ i j * dMax p := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, abs_of_nonneg (hQ i j)]
        exact mul_le_mul_of_nonneg_left (hterm i j) (hQ i j)
    _ = (∑ i, ∑ j, modeQ SP Δ i j) * dMax p := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    _ ≤ E * dMax p := by
        rw [blk_modeQ_sum]; exact mul_le_mul_of_nonneg_right hE hdM
    _ = dMax p * E := by ring

private lemma blk_F_bound (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (rlo E : ℝ) (hrlo : 0 < rlo) (Δ : Mat m n) (hR : rlo ≤ riskSigma C Δ) (hE : fro Δ ^ 2 ≤ E) :
    |fieldOp p.h c.d c.ζ (specMeasure SP Δ) (tensorFG f g)| ≤
      2 * p.h * dMax p * E / Real.sqrt rlo + p.h ^ 2 * mZeta p := by
  rw [blk_F_formula, if_pos (lt_of_lt_of_le hrlo hR)]
  have hsR : 0 < Real.sqrt rlo := Real.sqrt_pos.2 hrlo
  have hs : Real.sqrt rlo ≤ Real.sqrt (riskSigma C Δ) := Real.sqrt_le_sqrt hR
  have hA : 2 * p.h / Real.sqrt (riskSigma C Δ) ≤ 2 * p.h / Real.sqrt rlo :=
    div_le_div_of_nonneg_left (by linarith [p.hh]) hsR hs
  have hA0 : 0 ≤ 2 * p.h / Real.sqrt (riskSigma C Δ) :=
    div_nonneg (by linarith [p.hh]) (Real.sqrt_nonneg _)
  have hB0 : 0 ≤ 2 * p.h / Real.sqrt rlo := div_nonneg (by linarith [p.hh]) (Real.sqrt_nonneg _)
  have hAb := blk_A_bound p SP c hout hin f g hf hg E Δ hE
  have hZ := blk_zeta_atoms_bound p SP c (tensorFG f g) (blk_phi_le p SP hout hin f g hf hg)
  have t := abs_add_le (-(2 * p.h / Real.sqrt (riskSigma C Δ)) *
      (∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))))
    (p.h ^ 2 * ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j))
  have e1 : |-(2 * p.h / Real.sqrt (riskSigma C Δ)) *
      (∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)))| =
      2 * p.h / Real.sqrt (riskSigma C Δ) * |∑ i, ∑ j, modeQ SP Δ i j *
        (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))| := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_nonneg hA0]
  have e2 : |p.h ^ 2 * ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j)| =
      p.h ^ 2 * |∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j)| := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  have k1 := mul_le_mul hA hAb (abs_nonneg _) hB0
  have k2 := mul_le_mul_of_nonneg_left hZ (sq_nonneg p.h)
  have k3 : 2 * p.h / Real.sqrt rlo * (dMax p * E) = 2 * p.h * dMax p * E / Real.sqrt rlo := by ring
  rw [e1, e2] at t
  linarith

private lemma blk_F_lip (p : DynParams) (SP : SpectralData C) (c : DynCoeff p SP B)
    (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig) (f g : ℝ → ℝ)
    (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (rlo E : ℝ) (hrlo : 0 < rlo) (Δ Δ' : Mat m n) (hR : rlo ≤ riskSigma C Δ)
    (hR' : rlo ≤ riskSigma C Δ') (hE : fro Δ ^ 2 ≤ E) (hE' : fro Δ' ^ 2 ≤ E) :
    |fieldOp p.h c.d c.ζ (specMeasure SP Δ) (tensorFG f g) -
        fieldOp p.h c.d c.ζ (specMeasure SP Δ') (tensorFG f g)| ≤
      (2 * p.h / Real.sqrt rlo * dMax p +
        2 * p.h * (1 / (Real.sqrt rlo) ^ 3) * (p.CSig ^ 2 / 2) * (dMax p * E)) *
        ∑ i, ∑ j, |modeQ SP Δ i j - modeQ SP Δ' i j| := by
  rw [blk_F_formula, blk_F_formula, if_pos (lt_of_lt_of_le hrlo hR), if_pos (lt_of_lt_of_le hrlo hR')]
  set A := ∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)) with hAdef
  set A' := ∑ i, ∑ j, modeQ SP Δ' i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)) with hA'def
  set Z := p.h ^ 2 * ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j)
  set R := riskSigma C Δ
  set R' := riskSigma C Δ'
  set Sq := ∑ i, ∑ j, |modeQ SP Δ i j - modeQ SP Δ' i j| with hSq
  have hdM : 0 ≤ dMax p := by unfold dMax; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hSq0 : 0 ≤ Sq := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hsR : 0 < Real.sqrt rlo := Real.sqrt_pos.2 hrlo
  have hphid : ∀ i j, |tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)| ≤ dMax p := by
    intro i j
    obtain ⟨h0, h1⟩ := blk_d_atom p SP c hout hin i j
    rw [abs_mul, abs_of_nonneg h0]
    calc _ ≤ 1 * dMax p := mul_le_mul (blk_phi_le p SP hout hin f g hf hg i j) h1 h0 zero_le_one
      _ = dMax p := one_mul _
  -- |A - A'| ≤ dMax * Sq
  have hAA : |A - A'| ≤ dMax p * Sq := by
    have : A - A' = ∑ i, ∑ j, (modeQ SP Δ i j - modeQ SP Δ' i j) *
        (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)) := by
      simp only [hAdef, hA'def, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    rw [this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine le_trans (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _)) ?_
    rw [hSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, mul_comm (dMax p)]
    exact mul_le_mul_of_nonneg_left (hphid i j) (abs_nonneg _)
  have hA' : |A'| ≤ dMax p * E := blk_A_bound p SP c hout hin f g hf hg E Δ' hE'
  -- |R - R'| ≤ (CSig²/2) * Sq
  have hRR : |R - R'| ≤ p.CSig ^ 2 / 2 * Sq := by
    obtain ⟨hμ, hl⟩ := blk_spec_mem SP p.CSig hout hin
    have e : R - R' = (1 / 2) * ∑ i, ∑ j, SP.μ i * SP.lam j * (modeQ SP Δ i j - modeQ SP Δ' i j) := by
      simp only [R, R']
      rw [blk_risk_sum SP Δ, blk_risk_sum SP Δ', ← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hb : |∑ i, ∑ j, SP.μ i * SP.lam j * (modeQ SP Δ i j - modeQ SP Δ' i j)| ≤ p.CSig ^ 2 * Sq := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine le_trans (Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _)) ?_
      rw [hSq, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [abs_mul, abs_of_nonneg (mul_nonneg (hμ i).1 (hl j).1)]
      have : SP.μ i * SP.lam j ≤ p.CSig ^ 2 := by
        rw [sq]; exact mul_le_mul (hμ i).2 (hl j).2 (hl j).1 ((hμ i).1.trans (hμ i).2)
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    nlinarith
  have hinvR : 1 / Real.sqrt R ≤ 1 / Real.sqrt rlo :=
    one_div_le_one_div_of_le hsR (Real.sqrt_le_sqrt hR)
  have hinvdiff := blk_inv_sqrt_diff hrlo hR hR'
  have hdiff : -(2 * p.h / Real.sqrt R) * A + Z - (-(2 * p.h / Real.sqrt R') * A' + Z) =
      -(2 * p.h) * ((A - A') * (1 / Real.sqrt R) + A' * (1 / Real.sqrt R - 1 / Real.sqrt R')) := by
    field_simp
    ring
  rw [hdiff, abs_mul, abs_neg, abs_of_pos (by linarith [p.hh] : 0 < 2 * p.h)]
  have hb1 : |(A - A') * (1 / Real.sqrt R)| ≤ dMax p * Sq * (1 / Real.sqrt rlo) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt R)]
    exact mul_le_mul hAA hinvR (by positivity) (by positivity)
  have hb2 : |A' * (1 / Real.sqrt R - 1 / Real.sqrt R')| ≤
      dMax p * E * ((1 / (Real.sqrt rlo) ^ 3) * (p.CSig ^ 2 / 2 * Sq)) := by
    rw [abs_mul]
    refine mul_le_mul hA' (hinvdiff.trans ?_) (abs_nonneg _) (le_trans (abs_nonneg _) hA')
    exact mul_le_mul_of_nonneg_left hRR (by positivity)
  have hsum := abs_add_le ((A - A') * (1 / Real.sqrt R)) (A' * (1 / Real.sqrt R - 1 / Real.sqrt R'))
  have : 2 * p.h * (|(A - A') * (1 / Real.sqrt R) + A' * (1 / Real.sqrt R - 1 / Real.sqrt R')|) ≤
      2 * p.h * (dMax p * Sq * (1 / Real.sqrt rlo) +
        dMax p * E * ((1 / (Real.sqrt rlo) ^ 3) * (p.CSig ^ 2 / 2 * Sq))) :=
    mul_le_mul_of_nonneg_left (hsum.trans (add_le_add hb1 hb2)) (by linarith [p.hh])
  refine this.trans (le_of_eq ?_)
  field_simp

end atomicfield

private lemma blk_sum_blocks (F : ℕ → ℝ) (L : ℕ) (j r : ℕ) :
    ∑ u ∈ Finset.range (j * L + r), F u =
      ∑ b ∈ Finset.range j, ∑ i ∈ Finset.range L, F (b * L + i) + ∑ i ∈ Finset.range r, F (j * L + i) := by
  rw [Finset.sum_range_add]
  congr 1
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ← ih, show (j + 1) * L = j * L + L by ring, Finset.sum_range_add]

/-- Pure real-sequence decomposition of the discrete residual. -/
private lemma blk_seq_bound (x F μ' lam : ℕ → ℝ) (L Bn j r : ℕ) (hBn : 0 < Bn)
    (a0 a1 CE ℓ : ℝ) (ha0 : 0 ≤ a0) (hCE : 0 ≤ CE) (hℓ : 0 ≤ ℓ)
    (h1 : ∀ b, 1 ≤ b → b < j →
      x ((b + 1) * L) - x (b * L) = μ' b + lam b + (L : ℝ) / Bn * F (b * L))
    (h2 : 1 ≤ j → |x L - x 0| ≤ a0)
    (h3 : 1 ≤ j → ∀ i < L, |F i| ≤ CE)
    (h4 : ∀ b, 1 ≤ b → b < j → ∀ i < L, |F (b * L) - F (b * L + i)| ≤ ℓ)
    (h5 : |x (j * L + r) - x (j * L)| ≤ a1)
    (h6 : ∀ i < r, |F (j * L + i)| ≤ CE) (h7 : |F (j * L + r)| ≤ CE) (hr : r < L) :
    |x (j * L + r) - x 0 - (1 / (Bn : ℝ)) * ∑ u ∈ Finset.range (j * L + r), F u| +
        |F (j * L + r)| / Bn ≤
      a0 + L * CE / Bn + |∑ b ∈ Finset.Ico 1 j, μ' b| + ∑ b ∈ Finset.Ico 1 j, |lam b| +
        (j : ℝ) * L * ℓ / Bn + a1 + L * CE / Bn + CE / Bn := by
  have hBpos : (0 : ℝ) < Bn := by exact_mod_cast hBn
  have hBinv : 0 ≤ 1 / (Bn : ℝ) := by positivity
  set ρ : ℕ → ℝ := fun b => x ((b + 1) * L) - x (b * L) - (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L, F (b * L + i)
    with hρ
  set V : ℝ := x (j * L + r) - x (j * L) - (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range r, F (j * L + i) with hV
  have hdecomp : x (j * L + r) - x 0 - (1 / (Bn : ℝ)) * ∑ u ∈ Finset.range (j * L + r), F u =
      ∑ b ∈ Finset.range j, ρ b + V := by
    rw [blk_sum_blocks]
    have htel := Finset.sum_range_sub (fun b => x (b * L)) j
    simp only [hρ, hV, Finset.sum_sub_distrib, ← Finset.mul_sum, htel]
    ring
  -- bound on V
  have hVb : |V| ≤ a1 + L * CE / Bn := by
    have hs : |∑ i ∈ Finset.range r, F (j * L + i)| ≤ r * CE := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i ∈ Finset.range r, |F (j * L + i)| ≤ ∑ i ∈ Finset.range r, CE :=
            Finset.sum_le_sum fun i hi => h6 i (Finset.mem_range.1 hi)
        _ = r * CE := by simp
    have hrL : (r : ℝ) ≤ L := by exact_mod_cast hr.le
    calc |V| ≤ |x (j * L + r) - x (j * L)| + |(1 / (Bn : ℝ)) * ∑ i ∈ Finset.range r, F (j * L + i)| :=
          abs_sub _ _
      _ ≤ a1 + 1 / (Bn : ℝ) * (r * CE) := by
          refine add_le_add h5 ?_
          rw [abs_mul, abs_of_nonneg hBinv]
          exact mul_le_mul_of_nonneg_left hs hBinv
      _ ≤ a1 + L * CE / Bn := by
          have : 1 / (Bn : ℝ) * (r * CE) ≤ L * CE / Bn := by
            rw [one_div, ← div_eq_inv_mul]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hrL hCE) hBpos.le
          linarith
  -- bound on the block sum
  have hρb : ∀ b ∈ Finset.Ico 1 j, ρ b = μ' b + lam b +
      (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L, (F (b * L) - F (b * L + i)) := by
    intro b hb
    obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
    simp only [hρ]
    rw [h1 b hb1 hb2, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
    ring
  have hblock : |∑ b ∈ Finset.range j, ρ b| ≤ a0 + L * CE / Bn + (|∑ b ∈ Finset.Ico 1 j, μ' b| +
      ∑ b ∈ Finset.Ico 1 j, |lam b| + (j : ℝ) * L * ℓ / Bn) := by
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      simp only [Finset.range_zero, Finset.sum_empty, abs_zero, Finset.Ico_self, Nat.cast_zero,
        zero_mul, zero_div, add_zero]
      positivity
    · rw [Finset.sum_range_eq_add_Ico _ hj]
      have h0 : |ρ 0| ≤ a0 + L * CE / Bn := by
        have hs : |∑ i ∈ Finset.range L, F i| ≤ L * CE := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          calc ∑ i ∈ Finset.range L, |F i| ≤ ∑ i ∈ Finset.range L, CE :=
                Finset.sum_le_sum fun i hi => h3 hj i (Finset.mem_range.1 hi)
            _ = L * CE := by simp
        simp only [hρ, zero_add, one_mul, zero_mul]
        calc |x L - x 0 - 1 / (Bn : ℝ) * ∑ i ∈ Finset.range L, F i| ≤
            |x L - x 0| + |1 / (Bn : ℝ) * ∑ i ∈ Finset.range L, F i| := abs_sub _ _
          _ ≤ a0 + L * CE / Bn := by
            refine add_le_add (h2 hj) ?_
            rw [abs_mul, abs_of_nonneg hBinv]
            calc 1 / (Bn : ℝ) * |∑ i ∈ Finset.range L, F i| ≤ 1 / (Bn : ℝ) * (L * CE) :=
                  mul_le_mul_of_nonneg_left hs hBinv
              _ = L * CE / Bn := by ring
      have hrest : |∑ b ∈ Finset.Ico 1 j, ρ b| ≤ |∑ b ∈ Finset.Ico 1 j, μ' b| +
          ∑ b ∈ Finset.Ico 1 j, |lam b| + (j : ℝ) * L * ℓ / Bn := by
        rw [Finset.sum_congr rfl hρb, Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hS : |∑ b ∈ Finset.Ico 1 j, (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L,
            (F (b * L) - F (b * L + i))| ≤ (j : ℝ) * L * ℓ / Bn := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          have hterm : ∀ b ∈ Finset.Ico 1 j, |(1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L,
              (F (b * L) - F (b * L + i))| ≤ L * ℓ / Bn := by
            intro b hb
            obtain ⟨hb1, hb2⟩ := Finset.mem_Ico.1 hb
            rw [abs_mul, abs_of_nonneg hBinv]
            have : |∑ i ∈ Finset.range L, (F (b * L) - F (b * L + i))| ≤ L * ℓ := by
              refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
              calc ∑ i ∈ Finset.range L, |F (b * L) - F (b * L + i)| ≤ ∑ i ∈ Finset.range L, ℓ :=
                    Finset.sum_le_sum fun i hi => h4 b hb1 hb2 i (Finset.mem_range.1 hi)
                _ = L * ℓ := by simp
            calc 1 / (Bn : ℝ) * |∑ i ∈ Finset.range L, (F (b * L) - F (b * L + i))|
                ≤ 1 / (Bn : ℝ) * (L * ℓ) := mul_le_mul_of_nonneg_left this hBinv
              _ = L * ℓ / Bn := by ring
          calc ∑ b ∈ Finset.Ico 1 j, |(1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L, (F (b * L) - F (b * L + i))|
              ≤ ∑ b ∈ Finset.Ico 1 j, ((L : ℝ) * ℓ / Bn) := Finset.sum_le_sum hterm
            _ = ((j - 1 : ℕ) : ℝ) * (L * ℓ / Bn) := by simp
            _ ≤ (j : ℝ) * (L * ℓ / Bn) := by
                have : ((j - 1 : ℕ) : ℝ) ≤ j := by exact_mod_cast Nat.sub_le j 1
                exact mul_le_mul_of_nonneg_right this (by positivity)
            _ = (j : ℝ) * L * ℓ / Bn := by ring
        calc _ ≤ |∑ b ∈ Finset.Ico 1 j, μ' b + ∑ b ∈ Finset.Ico 1 j, lam b| +
              |∑ b ∈ Finset.Ico 1 j, (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L,
                (F (b * L) - F (b * L + i))| := by
                  have := abs_add_le (∑ b ∈ Finset.Ico 1 j, μ' b + ∑ b ∈ Finset.Ico 1 j, lam b)
                    (∑ b ∈ Finset.Ico 1 j, (1 / (Bn : ℝ)) * ∑ i ∈ Finset.range L,
                      (F (b * L) - F (b * L + i)))
                  exact this
          _ ≤ (|∑ b ∈ Finset.Ico 1 j, μ' b| + ∑ b ∈ Finset.Ico 1 j, |lam b|) + (j : ℝ) * L * ℓ / Bn := by
                refine add_le_add ?_ hS
                refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
                exact Finset.abs_sum_le_sum_abs _ _
      calc |ρ 0 + ∑ b ∈ Finset.Ico 1 j, ρ b| ≤ |ρ 0| + |∑ b ∈ Finset.Ico 1 j, ρ b| := abs_add_le _ _
        _ ≤ _ := by linarith
  rw [hdecomp]
  have h7' : |F (j * L + r)| / Bn ≤ CE / Bn := div_le_div_of_nonneg_right h7 hBpos.le
  calc |∑ b ∈ Finset.range j, ρ b + V| + |F (j * L + r)| / Bn ≤
      (|∑ b ∈ Finset.range j, ρ b| + |V|) + CE / Bn := add_le_add (abs_add_le _ _) h7'
    _ ≤ _ := by linarith

private lemma blk_frobIP_le {m n : ℕ} (T R : Mat m n) : |frobIP T R| ≤ fro T * fro R := by
  have htr : frobIP T R = ∑ x : Fin m × Fin n, T x.1 x.2 * R x.1 x.2 := by
    simp [frobIP, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  calc
    |∑ x : Fin m × Fin n, T x.1 x.2 * R x.1 x.2| ≤
        ∑ x : Fin m × Fin n, |T x.1 x.2| * |R x.1 x.2| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun x : Fin m × Fin n => T x.1 x.2 * R x.1 x.2) Finset.univ
    _ ≤ _ := by
      have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
        (fun x => |T x.1 x.2|) (fun x => |R x.1 x.2|)
      simpa [fro, Fintype.sum_prod_type, Real.norm_eq_abs] using h

private lemma blk_wfg_conj {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (Y : Mat m n) :
    SP.uOutᵀ * wfg f g C Y * SP.vIn =
      Matrix.diagonal (fun i => f (SP.μ i)) * (SP.uOutᵀ * Y * SP.vIn) *
        Matrix.diagonal (fun j => g (SP.lam j)) := by
  have hU := SP.huOut
  have hV := SP.hvIn
  have hUU : SP.uOut * SP.uOutᵀ = 1 := mul_eq_one_comm.mp hU
  have hVV : SP.vIn * SP.vInᵀ = 1 := mul_eq_one_comm.mp hV
  set Z := SP.uOutᵀ * Y * SP.vIn with hZ
  have hY : Y = SP.uOut * Z * SP.vInᵀ := by
    rw [hZ]
    calc Y = (SP.uOut * SP.uOutᵀ) * Y * (SP.vIn * SP.vInᵀ) := by rw [hUU, hVV]; simp
      _ = _ := by simp only [Matrix.mul_assoc]
  have hW : wfg f g C Y = SP.uOut * (Matrix.diagonal (fun i => f (SP.μ i)) * Z *
      Matrix.diagonal (fun j => g (SP.lam j))) * SP.vInᵀ := by
    unfold wfg
    rw [Sout_eq_spectral SP, Sin_eq_spectral SP, block_cfc_spectral _ hU, block_cfc_spectral _ hV]
    conv_lhs => rw [hY]
    calc _ = SP.uOut * Matrix.diagonal (fun i => f (SP.μ i)) * (SP.uOutᵀ * SP.uOut) * Z *
          (SP.vInᵀ * SP.vIn) * Matrix.diagonal (fun j => g (SP.lam j)) * SP.vInᵀ := by
            simp only [Matrix.mul_assoc]
      _ = _ := by rw [hU, hV]; simp only [Matrix.mul_assoc, Matrix.mul_one]
  rw [hW]
  calc SP.uOutᵀ * (SP.uOut * (Matrix.diagonal (fun i => f (SP.μ i)) * Z *
        Matrix.diagonal (fun j => g (SP.lam j))) * SP.vInᵀ) * SP.vIn
      = (SP.uOutᵀ * SP.uOut) * (Matrix.diagonal (fun i => f (SP.μ i)) * Z *
        Matrix.diagonal (fun j => g (SP.lam j))) * (SP.vInᵀ * SP.vIn) := by
          simp only [Matrix.mul_assoc]
    _ = _ := by rw [hU, hV]; simp only [Matrix.one_mul, Matrix.mul_one]

private lemma blk_wfg_fro_le {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (hf : ∀ i, |f (SP.μ i)| ≤ 1) (hg : ∀ j, |g (SP.lam j)| ≤ 1) (Y : Mat m n) :
    fro (wfg f g C Y) ≤ fro Y := by
  have hentry : ∀ i j, modeQ SP (wfg f g C Y) i j =
      (f (SP.μ i) * g (SP.lam j)) ^ 2 * modeQ SP Y i j := by
    intro i j
    have h := congrFun (congrFun (blk_wfg_conj f g SP Y) i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    unfold modeQ
    rw [← blk_modeQ_eq, ← blk_modeQ_eq, h]
    ring
  have hsq : fro (wfg f g C Y) ^ 2 ≤ fro Y ^ 2 := by
    rw [← blk_modeQ_sum SP, ← blk_modeQ_sum SP]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    rw [hentry]
    have h1 : (f (SP.μ i) * g (SP.lam j)) ^ 2 ≤ 1 := by
      rw [mul_pow]
      have a1 : f (SP.μ i) ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hf i)
      have a2 : g (SP.lam j) ^ 2 ≤ 1 := by
        rw [← sq_abs]; exact pow_le_one₀ (abs_nonneg _) (hg j)
      exact mul_le_one₀ a1 (sq_nonneg _) a2
    exact mul_le_of_le_one_left (sq_nonneg _) h1
  have := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (blk_fro_nn _), Real.sqrt_sq (blk_fro_nn _)] at this

private lemma blk_Xfg_diff {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (hf : ∀ i, |f (SP.μ i)| ≤ 1) (hg : ∀ j, |g (SP.lam j)| ≤ 1) (D D' : Mat m n) :
    |Xfg f g C D' - Xfg f g C D| ≤ fro (D' - D) * (fro D' + fro D) := by
  have hid : Xfg f g C D' - Xfg f g C D = frobIP (D' - D) (wfg f g C (D' + D)) := by
    unfold Xfg
    have hadd : wfg f g C (D' + D) = wfg f g C D' + wfg f g C D := by
      unfold wfg; simp only [Matrix.mul_add, Matrix.add_mul]
    have l1 : ∀ X Y Z : Mat m n, frobIP (X - Y) Z = frobIP X Z - frobIP Y Z := by
      intro X Y Z; simp only [frobIP, Matrix.sub_mul, Matrix.trace_sub]
    have l2 : ∀ X Y Z : Mat m n, frobIP X (Y + Z) = frobIP X Y + frobIP X Z := by
      intro X Y Z; simp only [frobIP, Matrix.transpose_add, Matrix.mul_add, Matrix.trace_add]
    have c1 := block_wfg_self_adjoint f g C D' D
    have c2 := block_frobIP_comm D (wfg f g C D')
    rw [hadd, l2, l1, l1]
    linarith
  rw [hid]
  refine (blk_frobIP_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (blk_fro_nn _)
  refine (blk_wfg_fro_le f g SP hf hg _).trans ?_
  open scoped Matrix.Norms.Frobenius in
  simp only [fro_eq_norm]
  exact norm_add_le _ _

/-- `E⁺ = 2(E⋆+1)+2`, the Frobenius bound squared on `𝒜⁺`. -/
private def blkEplus (p : DynParams) : ℝ := 2 * (p.Estar + 1) + 2
private def blkRplus (p : DynParams) : ℝ := Real.sqrt (blkEplus p)
private def blkCEp (p : DynParams) : ℝ :=
  2 * p.h * dMax p * blkEplus p / Real.sqrt (p.r0 / 4) + p.h ^ 2 * mZeta p
private def blkKF (p : DynParams) : ℝ :=
  2 * p.h / Real.sqrt (p.r0 / 4) * dMax p +
    2 * p.h * (1 / (Real.sqrt (p.r0 / 4)) ^ 3) * (p.CSig ^ 2 / 2) * (dMax p * blkEplus p)
private def blkNu (p : DynParams) (B : ℕ) : ℝ :=
  p.h * Real.sqrt p.γstar * (blockLen B : ℝ) / Real.sqrt (B : ℝ)
private def blkEdet (p : DynParams) (T : ℝ) (B : ℕ) : ℝ :=
  (4 + 2 * T * blkKF p) * blkRplus p * blkNu p B + (2 * (blockLen B : ℝ) + 1) * blkCEp p / (B : ℝ)

private lemma blk_Eplus_pos (p : DynParams) : 0 ≤ blkEplus p := by
  unfold blkEplus; linarith [p.hE]

private lemma blk_dMax_nn (p : DynParams) : 0 ≤ dMax p := by
  unfold dMax; exact div_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)

private lemma blk_mZeta_nn (p : DynParams) : 0 ≤ mZeta p := by
  unfold mZeta
  have hk : 0 ≤ kStar p.CSig p.γstar p.ϱ := by
    unfold kStar
    have : 0 ≤ p.CSig := le_trans zero_le_one p.hC
    exact mul_nonneg this (Real.sqrt_nonneg _)
  obtain ⟨hb0, hb1⟩ := p.hβ
  have hb2 : 0 < 1 - p.β := by linarith
  have hg := p.hγ
  have : 0 ≤ 2 * kStar p.CSig p.γstar p.ϱ * p.β / (1 - p.β) := by positivity
  linarith

private lemma blk_CEp_nn (p : DynParams) : 0 ≤ blkCEp p := by
  unfold blkCEp
  have h1 := blk_Eplus_pos p
  have h2 := blk_dMax_nn p
  have h3 := blk_mZeta_nn p
  have := p.hh
  positivity

private lemma blk_KF_nn (p : DynParams) : 0 ≤ blkKF p := by
  unfold blkKF
  have h1 := blk_Eplus_pos p
  have h2 := blk_dMax_nn p
  have := p.hh
  positivity

private lemma blk_Nu_nn (p : DynParams) (B : ℕ) : 0 ≤ blkNu p B := by
  unfold blkNu
  have := p.hh
  have := p.hγ
  positivity

private lemma blk_mem_Aplus {m n : ℕ} {C : Covariances m n} (p : DynParams) {Δ : Mat m n}
    (h : Δ ∈ admAplus p C) : p.r0 / 4 ≤ riskSigma C Δ ∧ fro Δ ^ 2 ≤ blkEplus p := by
  simp only [admAplus, admSetOf, enl, admBase, Set.mem_setOf_eq] at h
  refine ⟨by linarith [h.1], ?_⟩
  unfold blkEplus
  linarith [h.2.2]

private lemma blk_A_sub_Aplus {m n : ℕ} {C : Covariances m n} (p : DynParams) {Δ : Mat m n}
    (h : Δ ∈ admA p C) : fro Δ ^ 2 ≤ blkEplus p := by
  simp only [admA, admSetOf, admBase, Set.mem_setOf_eq] at h
  unfold blkEplus
  linarith [h.2.2, p.hE]

private lemma blk_fro_le_Rplus {m n : ℕ} (p : DynParams) {Δ : Mat m n} (h : fro Δ ^ 2 ≤ blkEplus p) :
    fro Δ ≤ blkRplus p := by
  unfold blkRplus
  exact Real.le_sqrt_of_sq_le h

private lemma blk_A_Aplus {m n : ℕ} {C : Covariances m n} (p : DynParams) {Δ : Mat m n}
    (h : Δ ∈ admA p C) : Δ ∈ admAplus p C := by
  simp only [admA, admAplus, admSetOf, enl, admBase, Set.mem_setOf_eq] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by linarith [p.hr0], by linarith [p.hr, p.hr0, h2], by linarith [p.hE]⟩

private lemma blk_path_bound {m n B : ℕ} {C : Covariances m n} (p : DynParams) (SP : SpectralData C)
    (c : DynCoeff p SP B) (hout : opNorm C.Sout ≤ p.CSig) (hin : opNorm C.Sin ≤ p.CSig)
    (f g : ℝ → ℝ) (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (L : ℕ) (hL : 0 < L) (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) (ν : ℝ) (hν : 0 ≤ ν)
    (ψ : ℕ → Mat m n) (mu lam : ℕ → ℝ) (h0 : ψ 0 ∈ admA p C)
    (hwin : ∀ b, ψ (b * L) ∈ admA p C → ∀ u, b * L ≤ u → u ≤ b * L + L →
        ψ u ∈ admAplus p C ∧ fro (ψ u - ψ (b * L)) ≤ ν)
    (N : ℕ) (hN : N ≤ ⌊T * (B : ℝ)⌋₊)
    (hgood : ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C)
    (hid : ∀ b, 1 ≤ b → b < N / L →
      Xfg f g C (ψ ((b + 1) * L)) - Xfg f g C (ψ (b * L)) =
        mu b + lam b + (L : ℝ) / B * blkF p SP c f g ψ (b * L)) :
    |blkU p SP c f g ψ N| + |blkF p SP c f g ψ N| / B ≤
      (4 + 2 * T * blkKF p) * blkRplus p * ν + (2 * (L : ℝ) + 1) * blkCEp p / B +
        |∑ b ∈ Finset.Ico 1 (N / L), mu b| + ∑ b ∈ Finset.Ico 1 (N / L), |lam b| := by
  classical
  obtain ⟨hμ, hl⟩ := blk_spec_mem SP p.CSig hout hin
  have hf' : ∀ i, |f (SP.μ i)| ≤ 1 := fun i => hf _ (hμ i)
  have hg' : ∀ j, |g (SP.lam j)| ≤ 1 := fun j => hg _ (hl j)
  have hrlo : 0 < p.r0 / 4 := by linarith [p.hr0]
  have hRp : 0 ≤ blkRplus p := Real.sqrt_nonneg _
  have hKF := blk_KF_nn p
  have hCE := blk_CEp_nn p
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  -- windows for blocks starting before N
  have hblk : ∀ b, b * L < N → ∀ u, b * L ≤ u → u ≤ b * L + L →
      ψ u ∈ admAplus p C ∧ fro (ψ u - ψ (b * L)) ≤ ν := by
    intro b hb u hu1 hu2
    have hbN : b ∈ Finset.range N := by
      refine Finset.mem_range.2 (lt_of_le_of_lt ?_ hb)
      exact Nat.le_mul_of_pos_right b hL
    exact hwin b (hgood b hbN hb) u hu1 hu2
  -- every index u ≤ N lies in 𝒜⁺
  have hAp : ∀ u, u ≤ N → ψ u ∈ admAplus p C := by
    intro u hu
    rcases Nat.eq_zero_or_pos u with rfl | hupos
    · exact blk_A_Aplus p h0
    · obtain ⟨b, hbdef⟩ : ∃ b, b = (u - 1) / L := ⟨_, rfl⟩
      have hdm := Nat.div_add_mod' (u - 1) L
      rw [← hbdef] at hdm
      have hml := Nat.mod_lt (u - 1) hL
      have h1 : b * L ≤ u - 1 := by omega
      have h2 : u ≤ b * L + L := by omega
      exact (hblk b (by omega) u (by omega) h2).1
  have hFb : ∀ u, u ≤ N → |blkF p SP c f g ψ u| ≤ blkCEp p := by
    intro u hu
    obtain ⟨hr, he⟩ := blk_mem_Aplus p (hAp u hu)
    exact blk_F_bound p SP c hout hin f g hf hg (p.r0 / 4) (blkEplus p) hrlo (ψ u) hr he
  have hfroA : ∀ b, b * L < N → fro (ψ (b * L)) ≤ blkRplus p := by
    intro b hb
    have hbN : b ∈ Finset.range N := Finset.mem_range.2
      (lt_of_le_of_lt (Nat.le_mul_of_pos_right b hL) hb)
    exact blk_fro_le_Rplus p (blk_A_sub_Aplus p (hgood b hbN hb))
  have hfroAp : ∀ u, u ≤ N → fro (ψ u) ≤ blkRplus p := fun u hu =>
    blk_fro_le_Rplus p (blk_mem_Aplus p (hAp u hu)).2
  have hXb : ∀ b, b * L < N → ∀ u, b * L ≤ u → u ≤ b * L + L → u ≤ N →
      |Xfg f g C (ψ u) - Xfg f g C (ψ (b * L))| ≤ 2 * blkRplus p * ν := by
    intro b hb u hu1 hu2 huN
    obtain ⟨_, hfr⟩ := hblk b hb u hu1 hu2
    refine (blk_Xfg_diff f g SP hf' hg' (ψ (b * L)) (ψ u)).trans ?_
    have h1 := hfroAp u huN
    have h2 := hfroA b hb
    calc fro (ψ u - ψ (b * L)) * (fro (ψ u) + fro (ψ (b * L))) ≤ ν * (blkRplus p + blkRplus p) :=
          mul_le_mul hfr (add_le_add h1 h2) (add_nonneg (blk_fro_nn _) (blk_fro_nn _)) hν
      _ = 2 * blkRplus p * ν := by ring
  have hFlip : ∀ b, b * L < N → ∀ u, b * L ≤ u → u ≤ b * L + L → u ≤ N →
      |blkF p SP c f g ψ (b * L) - blkF p SP c f g ψ u| ≤ blkKF p * (2 * blkRplus p * ν) := by
    intro b hb u hu1 hu2 huN
    obtain ⟨_, hfr⟩ := hblk b hb u hu1 hu2
    have hbL : b * L ≤ N := hb.le
    obtain ⟨hr1, he1⟩ := blk_mem_Aplus p (hAp (b * L) hbL)
    obtain ⟨hr2, he2⟩ := blk_mem_Aplus p (hAp u huN)
    have hlip := blk_F_lip p SP c hout hin f g hf hg (p.r0 / 4) (blkEplus p) hrlo (ψ (b * L)) (ψ u)
      hr1 hr2 he1 he2
    have hsum : ∑ i, ∑ j, |modeQ SP (ψ (b * L)) i j - modeQ SP (ψ u) i j| ≤
        fro (ψ u - ψ (b * L)) * (fro (ψ u) + fro (ψ (b * L))) := by
      have := blk_modeQ_diff_sum SP (ψ (b * L)) (ψ u)
      simpa only [abs_sub_comm] using this
    have hb2 : fro (ψ u - ψ (b * L)) * (fro (ψ u) + fro (ψ (b * L))) ≤ 2 * blkRplus p * ν := by
      have h1 := hfroAp u huN
      have h2 := hfroA b hb
      calc _ ≤ ν * (blkRplus p + blkRplus p) :=
            mul_le_mul hfr (add_le_add h1 h2) (add_nonneg (blk_fro_nn _) (blk_fro_nn _)) hν
        _ = 2 * blkRplus p * ν := by ring
    refine hlip.trans ?_
    unfold blkKF
    exact mul_le_mul_of_nonneg_left (hsum.trans hb2) (by simpa [blkKF] using hKF)
  -- decomposition N = j L + r
  set j := N / L with hj
  set r := N % L with hrdef
  have hNdec : N = j * L + r := (Nat.div_add_mod' N L).symm
  have hrL : r < L := Nat.mod_lt N hL
  have key := blk_seq_bound (fun u => Xfg f g C (ψ u)) (fun u => blkF p SP c f g ψ u) mu lam L B j r hB
    (2 * blkRplus p * ν) (2 * blkRplus p * ν) (blkCEp p) (blkKF p * (2 * blkRplus p * ν))
    (by positivity) hCE (by positivity)
    (fun b hb1 hb2 => hid b hb1 hb2)
    (by
      intro hj1
      have hLN : L ≤ N := by
        have : 1 ≤ N / L := hj1
        exact (Nat.le_div_iff_mul_le hL).1 this |> fun h => by simpa using h
      have := hXb 0 (by simpa using lt_of_lt_of_le hL hLN) L (by simp) (by simp) hLN
      simpa using this)
    (by
      intro hj1 i hi
      have hLN : L ≤ N := by
        have : 1 ≤ N / L := hj1
        exact (Nat.le_div_iff_mul_le hL).1 this |> fun h => by simpa using h
      exact hFb i (by omega))
    (by
      intro b hb1 hb2 i hi
      have hbj : (b + 1) * L ≤ N := by
        have : b + 1 ≤ N / L := hb2
        exact (Nat.le_div_iff_mul_le hL).1 this
      have hbN : b * L < N := by nlinarith
      exact hFlip b hbN (b * L + i) (by omega) (by omega) (by nlinarith))
    (by
      rcases Nat.eq_zero_or_pos r with hr0 | hr0
      · rw [hr0]; simp; positivity
      · have hjN : j * L < N := by omega
        exact hXb j hjN (j * L + r) (by omega) (by omega) (by omega))
    (fun i hi => hFb _ (by omega))
    (hFb _ (by omega)) hrL
  have hNdec' : j * L + r = N := hNdec.symm
  rw [hNdec'] at key
  have hjL : (j : ℝ) * L ≤ T * B := by
    have h1 : ((j * L : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : j * L ≤ N)
    have h2 : (N : ℝ) ≤ T * B := (Nat.cast_le.2 hN).trans (Nat.floor_le (by positivity))
    push_cast at h1
    linarith
  have hℓ0 : 0 ≤ blkKF p * (2 * blkRplus p * ν) := by positivity
  have hjl : (j : ℝ) * L * (blkKF p * (2 * blkRplus p * ν)) / B ≤
      T * (blkKF p * (2 * blkRplus p * ν)) := by
    rw [div_le_iff₀ hBpos]
    calc (j : ℝ) * L * (blkKF p * (2 * blkRplus p * ν)) ≤ (T * B) * (blkKF p * (2 * blkRplus p * ν)) :=
          mul_le_mul_of_nonneg_right hjL hℓ0
      _ = T * (blkKF p * (2 * blkRplus p * ν)) * B := by ring
  unfold blkU
  have e1 : L * blkCEp p / B + L * blkCEp p / B + blkCEp p / B = (2 * (L : ℝ) + 1) * blkCEp p / B := by ring
  nlinarith [key, hjl, e1]

private lemma blk_opNorm_cont {m n : ℕ} : Continuous (fun A : Mat m n => opNorm A) := by
  open scoped Matrix.Norms.L2Operator in
    simpa only [opNorm_eq_norm] using (continuous_norm : Continuous (fun A : Mat m n => ‖A‖))

private lemma blk_diffuseness_meas {m n : ℕ} (C : Covariances m n) :
    Measurable (fun Δ : Mat m n => diffuseness C Δ) := by
  unfold diffuseness normState Ahat
  have h1 : Measurable (fun Δ : Mat m n => (Real.sqrt (2 * riskSigma C Δ))⁻¹) :=
    (((block_risk_cont C).measurable.const_mul 2).sqrt).inv
  have h2 : Continuous (fun Δ : Mat m n => Arot C Δ) := by unfold Arot; fun_prop
  exact blk_opNorm_cont.measurable.comp (h1.smul h2.measurable)

section blkmaster

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

/-- Block `b` is good: `Δ_{bL} ∈ 𝒜` and `δ(Δ_{bL}) ≤ d`. -/
private def blkGood (S : DynSetup p P m n B) (d : ℝ) (b : ℕ) (ω : Ω) : Prop :=
  dynDelta S (b * blockLen B) ω ∈ admA p S.C ∧ diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ d

open Classical in
/-- The (truncated) stopping block index `b⋆ ∧ J`. -/
private def blkBstar (S : DynSetup p P m n B) (d : ℝ) (J : ℕ) (ω : Ω) : ℕ :=
  Nat.findGreatest (fun j => ∀ b < j, blkGood S d b ω) J

private lemma blk_bstar_lt_iff (S : DynSetup p P m n B) (d : ℝ) (J : ℕ) (ω : Ω) (b : ℕ) :
    b < blkBstar S d J ω ↔ b < J ∧ ∀ b' ≤ b, blkGood S d b' ω := by
  classical
  unfold blkBstar
  constructor
  · intro hb
    refine ⟨lt_of_lt_of_le hb (Nat.findGreatest_le J), fun b' hb' => ?_⟩
    have hspec := Nat.findGreatest_spec (P := fun j => ∀ b < j, blkGood S d b ω) (m := 0) (Nat.zero_le J)
      (fun b hb => absurd hb (Nat.not_lt_zero b))
    exact hspec b' (lt_of_le_of_lt hb' hb)
  · rintro ⟨hbJ, hgood⟩
    have : b + 1 ≤ Nat.findGreatest (fun j => ∀ b < j, blkGood S d b ω) J :=
      Nat.le_findGreatest (by omega) (fun b'' hb'' => hgood b'' (by omega))
    omega

private lemma blk_bstar_A (S : DynSetup p P m n B) (d : ℝ) (J : ℕ) (ω : Ω) (b : ℕ)
    (hb : b < blkBstar S d J ω) : dynDelta S (b * blockLen B) ω ∈ admA p S.C :=
  ((blk_bstar_lt_iff S d J ω b).1 hb).2 b le_rfl |>.1

private lemma blk_good_meas (S : DynSetup p P m n B) (d : ℝ) (b : ℕ) :
    MeasurableSet[dynPast S (b * blockLen B)] {ω | blkGood S d b ω} := by
  have hD : Measurable[dynPast S (b * blockLen B)] (dynDelta S (b * blockLen B)) :=
    block_delta_meas S _
  exact (hD (blk_admA_meas p S.C)).inter
    (measurableSet_le ((blk_diffuseness_meas S.C).comp hD) measurable_const)

private lemma blk_bstar_meas (S : DynSetup p P m n B) (d : ℝ) (J : ℕ) (b : ℕ) :
    MeasurableSet[dynPast S (b * blockLen B)] {ω | b < blkBstar S d J ω} := by
  by_cases hbJ : b < J
  · have hset : {ω | b < blkBstar S d J ω} = ⋂ b' ∈ Finset.range (b + 1), {ω | blkGood S d b' ω} := by
      ext ω
      simp only [blk_bstar_lt_iff, Set.mem_setOf_eq, Set.mem_iInter, Finset.mem_range]
      constructor
      · rintro ⟨_, h⟩ b' hb'
        exact h b' (by omega)
      · intro h
        exact ⟨hbJ, fun b' hb' => h b' (by omega)⟩
    rw [hset]
    refine MeasurableSet.biInter (Finset.countable_toSet _) fun b' hb' => ?_
    have hb'b : b' ≤ b := Nat.lt_succ_iff.1 (Finset.mem_range.1 hb')
    exact (block_past_mono S (Nat.mul_le_mul_right _ hb'b)) _ (blk_good_meas S d b')
  · have hset : {ω | b < blkBstar S d J ω} = ∅ := by
      ext ω
      simp only [blk_bstar_lt_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro h; exact absurd h hbJ
    rw [hset]
    exact @MeasurableSet.empty Ω (dynPast S (b * blockLen B))

end blkmaster

section blkpw

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

/-- The cap on block indices: `J = ⌊TB/L⌋ + 1`. -/
private def blkJ (T : ℝ) (B : ℕ) : ℕ := ⌊T * (B : ℝ) / (blockLen B : ℝ)⌋₊ + 1

/-- The drift defect `Λ_b = 𝔼_{t_b}[X(Δ_{t_{b+1}}) − X(Δ_{t_b})] − (L/B) F(χ(Δ_{t_b}))(f ⊗ g)`. -/
private def blkLam (S : DynSetup p P m n B) {C : Covariances m n} (SP : SpectralData C)
    (c : DynCoeff p SP B) (f g : ℝ → ℝ) (b : ℕ) (ω : Ω) : ℝ :=
  condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b) ω -
    (blockLen B : ℝ) / B * blkF p SP c f g (fun t => dynDelta S t ω) (b * blockLen B)

private lemma blk_pw (S : DynSetup p P m n B) (SP : SpectralData S.C) (c : DynCoeff p SP B)
    (f g : ℝ → ℝ) (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) (d : ℝ) (ω : Ω)
    (h0 : dynDelta S 0 ω ∈ admA p S.C)
    (hwin : ∀ b, dynDelta S (b * blockLen B) ω ∈ admA p S.C → ∀ u, b * blockLen B ≤ u →
        u ≤ b * blockLen B + blockLen B →
        dynDelta S u ω ∈ admAplus p S.C ∧
          fro (dynDelta S u ω - dynDelta S (b * blockLen B) ω) ≤ blkNu p B)
    (hGd : ∀ b < blkJ T B, (∀ b' ≤ b, dynDelta S (b' * blockLen B) ω ∈ admA p S.C) →
        diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ d)
    (N : ℕ) (hN : N ≤ ⌊T * (B : ℝ)⌋₊)
    (hgood : ∀ b ∈ Finset.range N, b * blockLen B < N → dynDelta S (b * blockLen B) ω ∈ admA p S.C) :
    |blkU p SP c f g (fun t => dynDelta S t ω) N| +
        |blkF p SP c f g (fun t => dynDelta S t ω) N| / B ≤
      blkEdet p T B + 2 * Real.sqrt (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω) +
        ∑ b ∈ Finset.Ico 1 (blkJ T B),
          (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| := by
  classical
  have hLpos : 0 < blockLen B := block_blockLen_pos hB
  set J := blkJ T B with hJdef
  set bs := blkBstar S d J with hbs
  set L := blockLen B with hL
  have hout : opNorm S.C.Sout ≤ p.CSig := S.size.2.1
  have hin : opNorm S.C.Sin ≤ p.CSig := S.size.2.2
  have hNL : N / L ≤ ⌊T * (B : ℝ) / (L : ℝ)⌋₊ := by
    rw [Nat.floor_div_natCast]
    exact Nat.div_le_div_right hN
  have hNLJ : N / L < J := by
    have h1 : J = ⌊T * (B : ℝ) / (L : ℝ)⌋₊ + 1 := rfl
    omega
  -- membership in bstar
  have hlt : ∀ b, b < N / L → b < bs ω := by
    intro b hb
    rw [hbs, blk_bstar_lt_iff]
    refine ⟨by omega, fun b' hb' => ⟨?_, ?_⟩⟩
    · have hb'N : (b' + 1) * L ≤ N := (Nat.le_div_iff_mul_le hLpos).1 (by omega)
      have hlt' : b' * L < N := by nlinarith
      exact hgood b' (Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_mul_of_pos_right b' hLpos) hlt')) hlt'
    · refine hGd b' (by omega) (fun b'' hb'' => ?_)
      have hb'N : (b'' + 1) * L ≤ N := (Nat.le_div_iff_mul_le hLpos).1 (by omega)
      have hlt' : b'' * L < N := by nlinarith
      exact hgood b'' (Finset.mem_range.2 (lt_of_le_of_lt (Nat.le_mul_of_pos_right b'' hLpos) hlt')) hlt'
  have hpath := blk_path_bound p SP c hout hin f g hf hg L hLpos hB T hT (blkNu p B) (blk_Nu_nn p B)
    (fun t => dynDelta S t ω)
    (fun b => blockMartDiff p f g S bs b ω)
    (fun b => (if b < bs ω then (1 : ℝ) else 0) * blkLam S SP c f g b ω)
    h0 hwin N hN hgood (by
      intro b hb1 hb2
      have hb := hlt b hb2
      simp only [if_pos hb, one_mul, blockMartDiff, blkLam]
      show blockIncr p f g S b ω = _
      ring)
  -- martingale part
  have hMj : ∀ j', j' ≤ ⌊T * (B : ℝ) / (L : ℝ)⌋₊ →
      |∑ b ∈ Finset.range j', blockMartDiff p f g S bs b ω| ≤
        Real.sqrt (blockMaxSq p f g S bs T ω) := by
    intro j' hj'
    apply Real.abs_le_sqrt
    unfold blockMaxSq
    exact Finset.le_sup' (f := fun j => (∑ b ∈ Finset.range j, blockMartDiff p f g S bs b ω) ^ 2)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hj'))
  have hmu : |∑ b ∈ Finset.Ico 1 (N / L), blockMartDiff p f g S bs b ω| ≤
      2 * Real.sqrt (blockMaxSq p f g S bs T ω) := by
    have hnn : 0 ≤ Real.sqrt (blockMaxSq p f g S bs T ω) := Real.sqrt_nonneg _
    by_cases hj1 : 1 ≤ N / L
    · rw [Finset.sum_Ico_eq_sub _ hj1]
      have h1 := hMj (N / L) hNL
      have h2 := hMj 1 (le_trans hj1 hNL)
      calc _ ≤ |∑ b ∈ Finset.range (N / L), blockMartDiff p f g S bs b ω| +
            |∑ b ∈ Finset.range 1, blockMartDiff p f g S bs b ω| := abs_sub _ _
        _ ≤ _ := by linarith
    · have : N / L ≤ 1 := by omega
      rw [Finset.Ico_eq_empty_of_le this]
      simp only [Finset.sum_empty, abs_zero]
      positivity
  have habs : ∀ b, |(if b < bs ω then (1 : ℝ) else 0) * blkLam S SP c f g b ω| =
      (if b < bs ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| := by
    intro b; by_cases h : b < bs ω <;> simp [h]
  have hlam : ∑ b ∈ Finset.Ico 1 (N / L), |(if b < bs ω then (1 : ℝ) else 0) * blkLam S SP c f g b ω| ≤
      ∑ b ∈ Finset.Ico 1 J, (if b < bs ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| := by
    simp_rw [habs]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ico_subset_Ico_right hNLJ.le)
      (fun b _ _ => by positivity)
  unfold blkEdet
  linarith [hpath, hmu, hlam]

end blkpw

private lemma blk_markov {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (f : Ω → ℝ) (hf0 : ∀ ω, 0 ≤ f ω) (hf : Integrable f P) (a : ℝ) (ha : 0 < a) :
    P {ω | a ≤ f ω} ≤ ENNReal.ofReal ((∫ ω, f ω ∂P) / a) := by
  have h := mul_meas_ge_le_integral_of_nonneg (μ := P) (f := f) (Eventually.of_forall hf0) hf a
  have hfin : P {ω | a ≤ f ω} ≠ ⊤ := measure_ne_top _ _
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ ha]
  have : (P {ω | a ≤ f ω}).toReal = P.real {ω | a ≤ f ω} := rfl
  rw [this]
  linarith

section blkpsi

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma blk_Edet_nn (p : DynParams) (T : ℝ) (hT : 0 ≤ T) (B : ℕ) : 0 ≤ blkEdet p T B := by
  unfold blkEdet
  have h1 := blk_KF_nn p
  have h2 : 0 ≤ blkRplus p := Real.sqrt_nonneg _
  have h3 := blk_Nu_nn p B
  have h4 := blk_CEp_nn p
  positivity

private lemma blk_psi_le (S : DynSetup p P m n B) (SP : SpectralData S.C) (c : DynCoeff p SP B)
    (f g : ℝ → ℝ) (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) (d : ℝ) (ω : Ω)
    (h0 : dynDelta S 0 ω ∈ admA p S.C)
    (hwin : ∀ b, dynDelta S (b * blockLen B) ω ∈ admA p S.C → ∀ u, b * blockLen B ≤ u →
        u ≤ b * blockLen B + blockLen B →
        dynDelta S u ω ∈ admAplus p S.C ∧
          fro (dynDelta S u ω - dynDelta S (b * blockLen B) ω) ≤ blkNu p B)
    (hGd : ∀ b < blkJ T B, (∀ b' ≤ b, dynDelta S (b' * blockLen B) ω ∈ admA p S.C) →
        diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ d) :
    blkPsi p SP c f g (blockLen B) T (fun t => dynDelta S t ω) ≤
      blkEdet p T B + 2 * Real.sqrt (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω) +
        ∑ b ∈ Finset.Ico 1 (blkJ T B),
          (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| := by
  classical
  have hnn : 0 ≤ blkEdet p T B + 2 * Real.sqrt (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω) +
        ∑ b ∈ Finset.Ico 1 (blkJ T B),
          (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| := by
    have := blk_Edet_nn p T hT B
    have h2 := Real.sqrt_nonneg (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω)
    have h3 : 0 ≤ ∑ b ∈ Finset.Ico 1 (blkJ T B),
          (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| :=
      Finset.sum_nonneg fun b _ => by positivity
    linarith
  unfold blkPsi
  refine Finset.sup'_le _ _ fun N hN => ?_
  by_cases hcond : ∀ b ∈ Finset.range N, b * blockLen B < N → dynDelta S (b * blockLen B) ω ∈ admA p S.C
  · rw [if_pos hcond]
    exact blk_pw S SP c f g hf hg hB T hT d ω h0 hwin hGd N (Nat.lt_succ_iff.1 (Finset.mem_range.1 hN)) hcond
  · rw [if_neg hcond]; exact hnn

end blkpsi

section blkprob

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

/-- The diffuseness event `G_d`: along the blocks inside `𝒜`, the diffuseness is at most `d`. -/
private def blkGd (S : DynSetup p P m n B) (T d : ℝ) (ω : Ω) : Prop :=
  ∀ b < blkJ T B, (∀ b' ≤ b, dynDelta S (b' * blockLen B) ω ∈ admA p S.C) →
    diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ d

private lemma blk_master [IsProbabilityMeasure P] (S : DynSetup p P m n B) (SP : SpectralData S.C)
    (c : DynCoeff p SP B)
    (f g : ℝ → ℝ) (hf : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) (hg : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1)
    (hB : 0 < B) (T : ℝ) (hT : 0 ≤ T) (d : ℝ)
    (h0 : ∀ ω, dynDelta S 0 ω ∈ admA p S.C)
    (hwin : ∀ ω b, dynDelta S (b * blockLen B) ω ∈ admA p S.C → ∀ u, b * blockLen B ≤ u →
        u ≤ b * blockLen B + blockLen B →
        dynDelta S u ω ∈ admAplus p S.C ∧
          fro (dynDelta S u ω - dynDelta S (b * blockLen B) ω) ≤ blkNu p B)
    (Em lamB : ℝ)
    (hMart : Integrable (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T) P ∧
      ∫ ω, blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω ∂P ≤ Em)
    (hLam : ∀ b ∈ Finset.Ico 1 (blkJ T B),
      Integrable (fun ω => (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) *
        |blkLam S SP c f g b ω|) P ∧
      ∫ ω, (if b < blkBstar S d (blkJ T B) ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| ∂P ≤ lamB)
    (hlamB : 0 ≤ lamB) (ε : ℝ) (hε : 0 < ε) (hEdet : blkEdet p T B ≤ ε / 3) :
    P {ω | ε < blkPsi p SP c f g (blockLen B) T (fun t => dynDelta S t ω)} ≤
      P {ω | ¬ blkGd S T d ω} + ENNReal.ofReal (36 * Em / ε ^ 2) +
        ENNReal.ofReal (3 * (blkJ T B : ℝ) * lamB / ε) := by
  classical
  set bs := blkBstar S d (blkJ T B) with hbs
  set MS := blockMaxSq p f g S bs T with hMS
  set Y : Ω → ℝ := fun ω => ∑ b ∈ Finset.Ico 1 (blkJ T B),
    (if b < bs ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| with hY
  have hMS0 : ∀ ω, 0 ≤ MS ω := by
    intro ω
    rw [hMS]
    unfold blockMaxSq
    refine le_trans (sq_nonneg _) (Finset.le_sup' (f := fun j =>
      (∑ b ∈ Finset.range j, blockMartDiff p f g S bs b ω) ^ 2) (Finset.mem_range.2 (Nat.succ_pos _)))
  have hY0 : ∀ ω, 0 ≤ Y ω := fun ω => Finset.sum_nonneg fun b _ => by positivity
  have hYint : Integrable Y P := integrable_finset_sum _ fun b hb => (hLam b hb).1
  have hYle : ∫ ω, Y ω ∂P ≤ (blkJ T B : ℝ) * lamB := by
    rw [hY, integral_finset_sum _ (fun b hb => (hLam b hb).1)]
    calc ∑ b ∈ Finset.Ico 1 (blkJ T B), ∫ ω, (if b < bs ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω| ∂P
        ≤ ∑ b ∈ Finset.Ico 1 (blkJ T B), lamB := Finset.sum_le_sum fun b hb => (hLam b hb).2
      _ = ((blkJ T B - 1 : ℕ) : ℝ) * lamB := by simp
      _ ≤ (blkJ T B : ℝ) * lamB := by
          apply mul_le_mul_of_nonneg_right _ hlamB
          exact_mod_cast Nat.sub_le _ _
  have hsub : {ω | ε < blkPsi p SP c f g (blockLen B) T (fun t => dynDelta S t ω)} ⊆
      {ω | ¬ blkGd S T d ω} ∪ ({ω | (ε / 6) ^ 2 ≤ MS ω} ∪ {ω | ε / 3 ≤ Y ω}) := by
    intro ω hω
    by_cases hG : blkGd S T d ω
    · right
      have hle := blk_psi_le S SP c f g hf hg hB T hT d ω (h0 ω) (hwin ω) hG
      have h1 : ε < blkEdet p T B + 2 * Real.sqrt (MS ω) + Y ω := lt_of_lt_of_le hω hle
      by_cases hX : ε / 6 < Real.sqrt (MS ω)
      · left
        have := (Real.lt_sqrt (by positivity)).1 hX
        exact le_of_lt this
      · right
        rw [not_lt] at hX
        show ε / 3 ≤ Y ω
        linarith
    · left; exact hG
  have hP1 : P {ω | (ε / 6) ^ 2 ≤ MS ω} ≤ ENNReal.ofReal (36 * Em / ε ^ 2) := by
    refine (blk_markov MS hMS0 hMart.1 _ (by positivity)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    have hpos : 0 < (ε / 6) ^ 2 := by positivity
    rw [div_le_div_iff₀ hpos (by positivity)]
    have := hMart.2
    nlinarith [sq_nonneg ε]
  have hP2 : P {ω | ε / 3 ≤ Y ω} ≤ ENNReal.ofReal (3 * (blkJ T B : ℝ) * lamB / ε) := by
    refine (blk_markov Y hY0 hYint _ (by positivity)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [div_le_div_iff₀ (by positivity) hε]
    nlinarith [hYle]
  calc _ ≤ P ({ω | ¬ blkGd S T d ω} ∪ ({ω | (ε / 6) ^ 2 ≤ MS ω} ∪ {ω | ε / 3 ≤ Y ω})) := measure_mono hsub
    _ ≤ P {ω | ¬ blkGd S T d ω} + P ({ω | (ε / 6) ^ 2 ≤ MS ω} ∪ {ω | ε / 3 ≤ Y ω}) := measure_union_le _ _
    _ ≤ P {ω | ¬ blkGd S T d ω} + (P {ω | (ε / 6) ^ 2 ≤ MS ω} + P {ω | ε / 3 ≤ Y ω}) :=
        add_le_add le_rfl (measure_union_le _ _)
    _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add (add_le_add le_rfl hP1) hP2

end blkprob

private lemma blk_window (p : DynParams) :
    ∃ B0 : ℕ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (m n B : ℕ) (S : DynSetup p P m n B),
      B0 ≤ B → ∀ (ω : Ω) (b : ℕ), dynDelta S (b * blockLen B) ω ∈ admA p S.C →
        ∀ u : ℕ, b * blockLen B ≤ u → u ≤ b * blockLen B + blockLen B →
          dynDelta S u ω ∈ admAplus p S.C ∧
            fro (dynDelta S u ω - dynDelta S (b * blockLen B) ω) ≤ blkNu p B := by
  have hrlo : 0 < p.r0 / 2 := by linarith [p.hr0]
  have hle : p.r0 / 2 ≤ p.r1 + 1 / 2 := by linarith [p.hr, p.hr0]
  obtain ⟨B0, hB0⟩ := lem_app_dyn_movement_ii p (p.r0 / 2) (p.r1 + 1 / 2) (p.Estar + 1) hrlo hle
  refine ⟨B0, fun Ω _ P m n B S hB ω b hb u hu1 hu2 => ?_⟩
  obtain ⟨hstop, hwin⟩ := hB0 Ω P m n B S hB ω (b * blockLen B) hb
  refine ⟨hwin u (by
      have : |((u : ℤ) - ((b * blockLen B : ℕ) : ℤ))| ≤ 4 * (blockLen B : ℤ) := by
        rw [abs_le]; constructor <;> omega
      exact this), ?_⟩
  have hu : (u : ℕ∞) < dynStop S ω := by
    refine lt_of_le_of_lt ?_ hstop
    exact_mod_cast (by omega : u ≤ b * blockLen B + 4 * blockLen B)
  obtain ⟨_, h2, _⟩ := lem_app_dyn_movement_i p S ω (b * blockLen B) u hu1 hu
  refine h2.trans ?_
  unfold blkNu
  rcases Nat.eq_zero_or_pos B with rfl | hBpos
  · simp
  · have hsq : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hBpos)
    rw [div_le_div_iff_of_pos_right hsq]
    have hcast : ((u : ℝ) - ((b * blockLen B : ℕ) : ℝ)) ≤ (blockLen B : ℝ) := by
      have : ((u : ℕ) : ℝ) ≤ ((b * blockLen B + blockLen B : ℕ) : ℝ) := by exact_mod_cast hu2
      push_cast at this ⊢
      linarith
    have hc : 0 ≤ p.h * Real.sqrt p.γstar := mul_nonneg p.hh.le (Real.sqrt_nonneg _)
    exact mul_le_mul_of_nonneg_left hcast hc

private lemma blk_h0 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}
    (S : DynSetup p P m n B) (ω : Ω) : dynDelta S 0 ω ∈ admA p S.C := by
  have hdef : dynDelta S 0 ω = S.W0 - S.alg.Wstar := rfl
  rw [hdef]
  simp only [admA, admSetOf, admBase, Set.mem_setOf_eq]
  have h1 := S.W0_risk
  have h2 := S.W0_norm
  refine ⟨by linarith [p.hr0, h1.1], by linarith [h1.2], by linarith [h2]⟩

private lemma blk_mart_hyp (certP : Muon.External.GaussianPoincare)
    (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (f g : ℝ → ℝ),
      (∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1) → (∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1) →
      B0 ≤ B → ∀ (d T : ℝ), 0 < T →
        Integrable (blockMaxSq p f g S (blkBstar S d (blkJ T B)) T) P ∧
        ∫ ω, blockMaxSq p f g S (blkBstar S d (blkJ T B)) T ω ∂P ≤
          K * (T + 1) * ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) +
            (blockLen B : ℝ) ^ 3 / (B : ℝ) + 1 / (blockLen B : ℝ)) := by
  obtain ⟨B0, K, hK⟩ := lem_app_dyn_martingale certP certOp p
  refine ⟨B0, K, fun Ω _ P _ m n B S f g hf hg hB d T hT => ?_⟩
  exact (hK Ω P m n B S f g (blkBstar S d (blkJ T B)) hB hf hg
    (fun b => blk_bstar_meas S d (blkJ T B) b)
    (fun b ω hb => blk_bstar_A S d (blkJ T B) ω b hb)).2 T hT

private def blkFrozen {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} (cs : ChainSamples P m n B) :
    FrozenSamples P m n B where
  zw := fun s a => cs.act s a
  meas := cs.meas_act
  indep := by
    have := cs.indep.precomp (g := fun p : ℤ × Fin B => (Sum.inl p : (ℤ × Fin B) ⊕ (ℤ × ℕ × Fin B)))
      (fun a b h => by simpa using h)
    simpa using this
  law := cs.law_act

private def blkShift {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} (S0 : FrozenSamples P m n B)
    (t : ℤ) : FrozenSamples P m n B where
  zw := fun s a => S0.zw (s - t) a
  meas := fun s a => S0.meas _ a
  indep := by
    have := S0.indep.precomp (g := fun p : ℤ × Fin B => ((p.1 - t, p.2) : ℤ × Fin B))
      (fun a b h => by
        simp only [Prod.mk.injEq] at h
        exact Prod.ext (by omega) h.2)
    exact this
  law := fun s a => S0.law _ a

private theorem blkShift_buf {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ} (F : FrozenParams m n B)
    (S0 : FrozenSamples P m n B) (t : ℤ) (ω : Ω) :
    frozenBuf F (blkShift S0 t) t ω = frozenBuf F S0 0 ω := by
  unfold frozenBuf frozenBatchG
  refine tsum_congr fun j => ?_
  simp only [blkShift]
  have : t + 1 - (j : ℤ) - t = 0 + 1 - (j : ℤ) := by ring
  simp only [this]


private def blkRegime (p : DynParams) {m n B : ℕ → ℕ} (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hreg : ProportionalRegime m n B (fun k => (F k).C))
    (hdims : ∀ k, ((max (m k) (n k) : ℕ) : ℝ) ≤ p.γstar * (B k : ℝ))
    (hnorm : ∀ k, opNorm (F k).C.Sin ≤ p.CSig ∧ opNorm (F k).C.Sout ≤ p.CSig)
    (hβ : ∀ k, (F k).β = p.β)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (A : ∀ j, Mat (m (φ j)) (n (φ j))) (hA : ∀ j, fro (A j) = 1)
    (hAz : Tendsto (fun j => opNorm (A j)) atTop (𝓝 0)) : SetupRegime where
  m := fun j => m (φ j)
  n := fun j => n (φ j)
  B := fun j => B (φ j)
  F := fun j => withState (F (φ j)) (A j) (hA j)
  prop :=
    { γin := hreg.γin
      γout := hreg.γout
      γin_pos := hreg.γin_pos
      γout_pos := hreg.γout_pos
      B_top := hreg.B_top.comp hφ.tendsto_atTop
      ratio_in := hreg.ratio_in.comp hφ.tendsto_atTop
      ratio_out := hreg.ratio_out.comp hφ.tendsto_atTop
      bdd := hreg.bdd.imp fun c hc => ⟨hc.1, fun k => hc.2 (φ k)⟩ }
  γstar := p.γstar
  CSig := p.CSig
  hC := p.hC
  dims := fun j => hdims (φ j)
  normOut := fun j => (hnorm (φ j)).2
  normIn := fun j => (hnorm (φ j)).1
  β := p.β
  hβ := fun j => hβ (φ j)
  ϱlo := p.ϱ
  ϱhi := p.ϱ
  hϱ := ⟨p.hϱ, le_rfl⟩
  diffuse := hAz

private lemma blk_frobIP_conj {m n : ℕ} {C : Covariances m n} (SP : SpectralData C) (X Y : Mat m n) :
    frobIP X Y = ∑ i, ∑ j, (SP.uOutᵀ * X * SP.vIn) i j * (SP.uOutᵀ * Y * SP.vIn) i j := by
  have hU := SP.huOut
  have hV := SP.hvIn
  have hUU : SP.uOut * SP.uOutᵀ = 1 := mul_eq_one_comm.mp hU
  have hVV : SP.vIn * SP.vInᵀ = 1 := mul_eq_one_comm.mp hV
  rw [← block_frobIP_eq_sum]
  unfold frobIP
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose]
  have h1 : (SP.uOutᵀ * X * SP.vIn * (SP.vInᵀ * Yᵀ * SP.uOut)).trace = (X * Yᵀ).trace := by
    calc (SP.uOutᵀ * X * SP.vIn * (SP.vInᵀ * Yᵀ * SP.uOut)).trace
        = (SP.uOutᵀ * ((X * (SP.vIn * SP.vInᵀ) * Yᵀ) * SP.uOut)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (((X * (SP.vIn * SP.vInᵀ) * Yᵀ) * SP.uOut) * SP.uOutᵀ).trace := Matrix.trace_mul_comm _ _
      _ = (X * (SP.vIn * SP.vInᵀ) * Yᵀ * (SP.uOut * SP.uOutᵀ)).trace := by
          simp only [Matrix.mul_assoc]
      _ = (X * Yᵀ).trace := by rw [hVV, hUU]; simp
  simp only [Matrix.mul_assoc] at h1 ⊢
  exact h1.symm

private lemma blk_frobIP_wfg_left {m n : ℕ} (f g : ℝ → ℝ) {C : Covariances m n} (SP : SpectralData C)
    (X Y : Mat m n) :
    frobIP (wfg f g C X) Y = ∑ i, ∑ j, f (SP.μ i) * g (SP.lam j) *
      ((SP.u i ⬝ᵥ (X *ᵥ SP.v j)) * (SP.u i ⬝ᵥ (Y *ᵥ SP.v j))) := by
  rw [blk_frobIP_conj SP]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun (blk_wfg_conj f g SP X) i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  rw [h, blk_modeQ_eq, blk_modeQ_eq]
  ring

private lemma blk_dot_mean {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {m n : ℕ}
    (X : Ω' → Mat m n) (hX : ∀ i j, Integrable (fun ω => X ω i j) P') (u : Fin m → ℝ) (v : Fin n → ℝ) :
    dotProduct u (Muon.mean P' X *ᵥ v) = ∫ ω, dotProduct u (X ω *ᵥ v) ∂P' := by
  have hint : ∀ i j, Integrable (fun ω => u i * (X ω i j * v j)) P' := fun i j =>
    ((hX i j).mul_const (v j)).const_mul (u i)
  have hrow : ∀ i, Integrable (fun ω => ∑ j, u i * (X ω i j * v j)) P' := fun i =>
    integrable_finsetSum _ fun j _ => hint i j
  have e : (fun ω => ∑ i, u i * ∑ j, X ω i j * v j) = fun ω => ∑ i, ∑ j, u i * (X ω i j * v j) := by
    funext ω; simp_rw [Finset.mul_sum]
  simp only [dotProduct, Matrix.mulVec, Muon.mean, Matrix.of_apply]
  rw [e, integral_finsetSum _ (fun i _ => hrow i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hint i j), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]

private lemma blk_frozenUpd_int {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P' m n B)
    (ϱ : ℝ) (hϱ : 0 ≤ ϱ) (s : ℤ) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => frozenUpd F S ϱ s ω i j) P' :=
  block_integrable_cont (block_upd_aem F S ϱ hϱ s) ((m : ℝ) + 1)
    (fun ω i j => block_upd_entry_bound F S ϱ hϱ s ω i j) (fun A => A i j) (by fun_prop)

private lemma blk_le_biSup (g : ℝ → ℝ) (s : Set ℝ) (hb : BddAbove (g '' s)) {x : ℝ} (hx : x ∈ s) :
    g x ≤ ⨆ ϱ ∈ s, g ϱ := by
  obtain ⟨M, hM⟩ := hb
  have hbdd : BddAbove (Set.range fun ϱ => ⨆ (_ : ϱ ∈ s), g ϱ) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨ϱ, rfl⟩
    by_cases h : ϱ ∈ s
    · simp only [ciSup_pos h]
      exact (hM ⟨ϱ, h, rfl⟩).trans (le_max_left _ _)
    · haveI : IsEmpty (ϱ ∈ s) := ⟨h⟩
      show (⨆ _ : ϱ ∈ s, g ϱ : ℝ) ≤ max M 0
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  have h1 : g x ≤ (⨆ _ : x ∈ s, g x : ℝ) := by rw [ciSup_pos hx]
  exact h1.trans (le_ciSup (f := fun ϱ => ⨆ (_ : ϱ ∈ s), g ϱ) hbdd x)


/-- Dependent cons on `ℕ`. -/
private def blkCons {α : ℕ → Type} (a0 : α 0) (rest : ∀ j, α (j + 1)) : ∀ j, α j
  | 0 => a0
  | j + 1 => rest j

section blkdrift

variable {p : DynParams} {m n B : ℕ → ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

/-- The drift error number `e₁(k, A) = ε_B` of the frozen model at the normalized state `A`. -/
private def blkE1 (p : DynParams) {m n B : ℕ → ℕ} (F : ∀ k, FrozenParams (m k) (n k) (B k))
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] {P' : ∀ k, Measure (Ω' k)}
    (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k)) (k : ℕ) (A : Mat (m k) (n k)) : ℝ :=
  if hA : fro A = 1 then
    Muon.Drift.epsB (emaW p.β) (withState (F k) A hA) (S0 k) 0 (Muon.Drift.specOutFM (withState (F k) A hA))
      (Muon.Drift.specInFM (withState (F k) A hA)) p.ϱ p.ϱ
  else 0

private lemma blk_withState_congr {m n B : ℕ} (F : FrozenParams m n B) {A A' : Mat m n} (h : A = A')
    (hA : fro A = 1) (hA' : fro A' = 1) : withState F A hA = withState F A' hA' := by
  subst h; rfl

private lemma blk_drift_state (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (k0 : ℕ) (D0 : Mat (m k0) (n k0))
    (hR : 0 < riskSigma (F k0).C D0) (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) :
    (|frobIP (wfg f g (F k0).C D0)
        (Muon.mean (P' k0) (fun ω => frozenUpd (withState (F k0) (Ahat (F k0).C D0)
          (block_Ahat_norm _ _ hR)) (S0 k0) p.ϱ 0 ω)) -
      (Real.sqrt (riskSigma (F k0).C D0))⁻¹ * ∑ i, ∑ j, modeQ (SD k0) D0 i j *
        (tensorFG f g ((SD k0).μ i, (SD k0).lam j) *
          Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM (F k0)) (Muon.Drift.specInFM (F k0)) p.ϱ ((SD k0).μ i) ((SD k0).lam j))| ≤
      fro D0 * blkE1 p F S0 k0 (Ahat (F k0).C D0)) ∧
    fro (Muon.mean (P' k0) (fun ω => frozenUpd (withState (F k0) (Ahat (F k0).C D0)
          (block_Ahat_norm _ _ hR)) (S0 k0) p.ϱ 0 ω)) ≤
      p.CSig / Real.sqrt p.ϱ + blkE1 p F S0 k0 (Ahat (F k0).C D0) := by
  classical
  set φ : ℕ → ℕ := fun j => k0 + j with hφdef
  have hφ : StrictMono φ := fun a b h => by simpa [hφdef] using h
  set A0 : ∀ j, Mat (m (φ j)) (n (φ j)) :=
    blkCons (α := fun j => Mat (m (φ j)) (n (φ j))) (Ahat (F k0).C D0)
      (fun j => Ahat (F (φ (j + 1))).C (dev0 hyp (φ (j + 1)))) with hA0def
  set Dt : ∀ j, Mat (m (φ j)) (n (φ j)) :=
    blkCons (α := fun j => Mat (m (φ j)) (n (φ j))) D0 (fun j => dev0 hyp (φ (j + 1))) with hDtdef
  have hrisk0 : ∀ j, 0 < riskSigma (F j).C (dev0 hyp j) := fun j =>
    lt_of_lt_of_le p.hr0 (hyp.W0_risk j).1
  have hRt : ∀ j, 0 < riskSigma (F (φ j)).C (Dt j) := by
    intro j
    cases j with
    | zero => exact hR
    | succ j => exact hrisk0 _
  have hDt : ∀ j, A0 j = Ahat (F (φ j)).C (Dt j) := by
    intro j
    cases j with
    | zero => rfl
    | succ j => rfl
  have hA : ∀ j, fro (A0 j) = 1 := fun j => by rw [hDt j]; exact block_Ahat_norm _ _ (hRt j)
  have hAz : Tendsto (fun j => opNorm (A0 j)) atTop (𝓝 0) := by
    refine (hyp.W0_hat.comp hφ.tendsto_atTop).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with j hj
    obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rfl
  set R := blkRegime p F hyp.regime hyp.dims hyp.normBd hβ φ hφ A0 hA hAz with hRdef
  obtain ⟨hmain, -, -, -, htest⟩ := Muon.Drift.cor_app_drift_kernel_i R (fun j => P' (φ j))
    (fun j => S0 (φ j)) 0 (fun j => SD (φ j)) Dt hDt hRt
  set Fk := withState (F k0) (Ahat (F k0).C D0) (block_Ahat_norm _ _ hR) with hFk
  set V := Muon.mean (P' k0) (fun ω => frozenUpd Fk (S0 k0) p.ϱ 0 ω) with hVdef
  have hw : ∀ ω, Muon.DetEquiv.WeightedBuf (emaW p.β) Fk (S0 k0) 0 ω = frozenBuf Fk (S0 k0) 0 ω := by
    intro ω
    rw [← hβ k0]
    exact Muon.DetEquiv.weightedBuf_emaW_eq_frozenBuf Fk _ _ _
  have hV : ∀ i j, dotProduct ((SD k0).u i) (V *ᵥ (SD k0).v j) =
      Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM (F k0)) (Muon.Drift.specInFM (F k0)) p.ϱ
          ((SD k0).μ i) ((SD k0).lam j) / Real.sqrt (riskSigma (F k0).C D0) *
        dotProduct ((SD k0).u i) (D0 *ᵥ (SD k0).v j) +
      Muon.Drift.Erho (emaW p.β) Fk (SD k0) (S0 k0) 0 (Muon.Drift.specOutFM Fk)
        (Muon.Drift.specInFM Fk) p.ϱ i j := by
    intro i j
    have h1 := (hmain 0 i j p.ϱ ⟨le_rfl, le_rfl⟩).2
    have hint : ∀ a b, Integrable (fun ω => frozenUpd Fk (S0 k0) p.ϱ 0 ω a b) (P' k0) := fun a b =>
      blk_frozenUpd_int Fk (S0 k0) p.ϱ p.hϱ.le 0 a b
    calc dotProduct ((SD k0).u i) (V *ᵥ (SD k0).v j)
        = ∫ ω, dotProduct ((SD k0).u i) (frozenUpd Fk (S0 k0) p.ϱ 0 ω *ᵥ (SD k0).v j) ∂(P' k0) :=
          blk_dot_mean _ hint _ _
      _ = ∫ ω, dotProduct ((SD k0).u i)
            (Q p.ϱ (Muon.DetEquiv.WeightedBuf (emaW p.β) Fk (S0 k0) 0 ω) *ᵥ (SD k0).v j) ∂(P' k0) := by
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [hw ω]; rfl
      _ = _ := h1
  have hE1 : blkE1 p F S0 k0 (Ahat (F k0).C D0) =
      Muon.Drift.epsB (emaW p.β) Fk (S0 k0) 0 (Muon.Drift.specOutFM Fk) (Muon.Drift.specInFM Fk) p.ϱ p.ϱ := by
    unfold blkE1
    rw [dif_pos (block_Ahat_norm _ _ hR)]
  refine ⟨?_, ?_⟩
  swap
  · obtain ⟨hG, -, -, htr⟩ := Muon.Drift.thm_app_drift_mean R (fun j => P' (φ j)) (fun j => S0 (φ j)) 0
    have hGb := (hG 0 p.ϱ ⟨le_rfl, le_rfl⟩).2
    have hVEQ : V = Muon.Drift.EQ (emaW p.β) Fk (S0 k0) 0 p.ϱ := by
      unfold Muon.Drift.EQ
      rw [hVdef]
      congr 1
      funext ω
      rw [hw ω]
      rfl
    set Gb := Muon.Drift.Gbar (emaW p.β) Fk (Muon.Drift.specOutFM Fk) (Muon.Drift.specInFM Fk) p.ϱ with hGbdef
    set E0 := V - Gb with hE0def
    obtain ⟨hbdd, hsup⟩ := htr 0 E0
    have hε0 : 0 ≤ Muon.Drift.epsB (emaW p.β) Fk (S0 k0) 0 (Muon.Drift.specOutFM Fk)
        (Muon.Drift.specInFM Fk) p.ϱ p.ϱ :=
      Real.iSup_nonneg fun ϱ => Real.iSup_nonneg fun _ => blk_fro_nn _
    have htr2 : (E0 * E0ᵀ).trace = fro E0 ^ 2 := by
      rw [block_fro_sq_eq]
      simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, pow_two]
    have hle := blk_le_biSup (fun ϱ => |(E0 * (Muon.Drift.EQ (emaW p.β) Fk (S0 k0) 0 ϱ -
        Muon.Drift.Gbar (emaW p.β) Fk (Muon.Drift.specOutFM Fk) (Muon.Drift.specInFM Fk) ϱ)ᵀ).trace|)
      (Set.Icc p.ϱ p.ϱ) hbdd ⟨le_rfl, le_rfl⟩
    have hle2 : fro E0 ^ 2 ≤ fro E0 * Muon.Drift.epsB (emaW p.β) Fk (S0 k0) 0
        (Muon.Drift.specOutFM Fk) (Muon.Drift.specInFM Fk) p.ϱ p.ϱ := by
      have e : Muon.Drift.EQ (emaW p.β) Fk (S0 k0) 0 p.ϱ -
          Muon.Drift.Gbar (emaW p.β) Fk (Muon.Drift.specOutFM Fk) (Muon.Drift.specInFM Fk) p.ϱ = E0 := by
        rw [hE0def, hVEQ]
      have h1 := hle
      simp only [e] at h1
      rw [htr2, abs_of_nonneg (sq_nonneg _)] at h1
      exact h1.trans hsup
    have hE0le : fro E0 ≤ Muon.Drift.epsB (emaW p.β) Fk (S0 k0) 0 (Muon.Drift.specOutFM Fk)
        (Muon.Drift.specInFM Fk) p.ϱ p.ϱ := by
      by_cases h0 : fro E0 = 0
      · rw [h0]; exact hε0
      · have hpos : 0 < fro E0 := lt_of_le_of_ne (blk_fro_nn _) (Ne.symm h0)
        nlinarith
    rw [hE1]
    have hGb' : fro Gb ≤ p.CSig / Real.sqrt p.ϱ := hGb
    have := blk_fro_le_add Gb V
    have hsub : V - Gb = E0 := rfl
    rw [hsub] at this
    linarith
  -- the tested bound
  have htest0 := htest 0 p.ϱ ⟨le_rfl, le_rfl⟩ (fun x y => f x * g y) 1
    (fun x y _ _ => by
      rw [abs_mul]
      exact mul_le_one₀ (hf x) (abs_nonneg _) (hg y))
  rw [hE1]
  rw [blk_frobIP_wfg_left f g (SD k0) D0 V]
  have hterm : ∀ i j, f ((SD k0).μ i) * g ((SD k0).lam j) *
        (dotProduct ((SD k0).u i) (D0 *ᵥ (SD k0).v j) * dotProduct ((SD k0).u i) (V *ᵥ (SD k0).v j)) -
      (Real.sqrt (riskSigma (F k0).C D0))⁻¹ * (modeQ (SD k0) D0 i j *
        (tensorFG f g ((SD k0).μ i, (SD k0).lam j) *
          Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM (F k0)) (Muon.Drift.specInFM (F k0)) p.ϱ
            ((SD k0).μ i) ((SD k0).lam j))) =
      f ((SD k0).μ i) * g ((SD k0).lam j) * dotProduct ((SD k0).u i) (D0 *ᵥ (SD k0).v j) *
        Muon.Drift.Erho (emaW p.β) Fk (SD k0) (S0 k0) 0 (Muon.Drift.specOutFM Fk)
          (Muon.Drift.specInFM Fk) p.ϱ i j := by
    intro i j
    rw [hV i j]
    unfold modeQ tensorFG
    ring
  have hsum : ∑ i, ∑ j, f ((SD k0).μ i) * g ((SD k0).lam j) *
        (dotProduct ((SD k0).u i) (D0 *ᵥ (SD k0).v j) * dotProduct ((SD k0).u i) (V *ᵥ (SD k0).v j)) -
      (Real.sqrt (riskSigma (F k0).C D0))⁻¹ * ∑ i, ∑ j, modeQ (SD k0) D0 i j *
        (tensorFG f g ((SD k0).μ i, (SD k0).lam j) *
          Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM (F k0)) (Muon.Drift.specInFM (F k0)) p.ϱ
            ((SD k0).μ i) ((SD k0).lam j)) =
      ∑ i, ∑ j, f ((SD k0).μ i) * g ((SD k0).lam j) * dotProduct ((SD k0).u i) (D0 *ᵥ (SD k0).v j) *
        Muon.Drift.Erho (emaW p.β) Fk (SD k0) (S0 k0) 0 (Muon.Drift.specOutFM Fk)
          (Muon.Drift.specInFM Fk) p.ϱ i j := by
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [hsum]
  rw [one_mul] at htest0
  exact htest0


private lemma blk_norm_fro {m n : ℕ} {C : Covariances m n} {A : Mat m n} (hA : A ∈ NormStates C) :
    fro A = 1 := by
  obtain ⟨Δ, hΔ, rfl⟩ := hA
  exact block_Ahat_norm C Δ hΔ

private lemma blk_drift_uniform (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ A ∈ NormStates (F k).C, opNorm A ≤ δ k →
      blkE1 p F S0 k A ≤ ε := by
  refine blk_uniform_eventual (fun k => (F k).C) (fun k A => blkE1 p F S0 k A) ?_ δ hδ
  intro φ hφ A hAN hAz
  have hA : ∀ j, fro (A j) = 1 := fun j => blk_norm_fro (hAN j)
  set R := blkRegime p F hyp.regime hyp.dims hyp.normBd hβ φ hφ A hA hAz with hRdef
  obtain ⟨-, -, hT, -⟩ := Muon.Drift.thm_app_drift_mean R (fun j => P' (φ j)) (fun j => S0 (φ j)) 0
  refine hT.congr fun j => ?_
  unfold blkE1
  rw [dif_pos (hA j)]
  rfl

end blkdrift

section blkforce

variable {p : DynParams} {m n B : ℕ → ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

private lemma blk_finInt_sub (a b : (ℝ × ℝ) →₀ ℝ) (φ : ℝ × ℝ → ℝ) :
    Muon.Volatility.finInt (a - b) φ = Muon.Volatility.finInt a φ - Muon.Volatility.finInt b φ := by
  unfold Muon.Volatility.finInt
  exact Finsupp.sum_sub_index (fun _ _ _ => by ring)

private lemma blk_finInt_le (a : (ℝ × ℝ) →₀ ℝ) (φ : ℝ × ℝ → ℝ) (hφ : ∀ x, |φ x| ≤ 1) :
    |Muon.Volatility.finInt a φ| ≤ Muon.Volatility.finTV a := by
  unfold Muon.Volatility.finInt Muon.Volatility.finTV Finsupp.sum
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (hφ x)

/-- The forcing error number `e₂(k, A)`. -/
private def blkE2 (cert : Muon.External.GaussianOpNorm) (p : DynParams) {m n B : ℕ → ℕ}
    (F : ∀ k, FrozenParams (m k) (n k) (B k)) {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)]
    {P' : ∀ k, Measure (Ω' k)} (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (f g : ℝ → ℝ) (k : ℕ) (A : Mat (m k) (n k)) : ℝ :=
  if hA : fro A = 1 then
    |Muon.Volatility.finInt (Muon.Volatility.measureInt (withState (F k) A hA) (S0 k) (SD k) 0 p.ϱ -
      Muon.Volatility.measureZeta cert p.γstar p.CSig (withState (F k) A hA) (SD k) p.ϱ)
      (fun q => f q.1 * g q.2)|
  else 0

/-- The finite-time error `2 K⋆ (β^L/(1−β) + β/(L(1−β)²))` of `thm:app-vol-joint-forcing`(iv). -/
private def blkTVL (p : DynParams) (L : ℕ) : ℝ :=
  2 * kStar p.CSig p.γstar p.ϱ * (p.β ^ L / (1 - p.β) + p.β / ((L : ℝ) * (1 - p.β) ^ 2))

private lemma blk_forcing_state (cert : Muon.External.GaussianOpNorm)
    (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (k0 : ℕ) (D0 : Mat (m k0) (n k0))
    (hR : 0 < riskSigma (F k0).C D0) (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (hL : 1 ≤ blockLen (B k0)) :
    |(Muon.Volatility.finiteTimeMeasure (withState (F k0) (Ahat (F k0).C D0) (block_Ahat_norm _ _ hR))
        (S0 k0) (SD k0) (blockLen (B k0)) p.ϱ).sum (fun x r => f x.1 * g x.2 * r) -
      Muon.Volatility.finInt (Muon.Volatility.measureZeta cert p.γstar p.CSig (F k0) (SD k0) p.ϱ)
        (fun q => f q.1 * g q.2)| ≤
      blkTVL p (blockLen (B k0)) + blkE2 cert p F S0 SD f g k0 (Ahat (F k0).C D0) := by
  set Fz := withState (F k0) (Ahat (F k0).C D0) (block_Ahat_norm _ _ hR) with hFz
  have hS : Muon.Volatility.SizeFin Fz.C (B k0) p.γstar p.CSig :=
    ⟨hyp.dims k0, (hyp.normBd k0).2, (hyp.normBd k0).1⟩
  obtain ⟨-, hiv⟩ := Muon.Volatility.thm_app_vol_joint_forcing_iv cert p.γstar p.CSig Fz (S0 k0) (SD k0)
    hS p.hC p.ϱ p.ϱ ⟨p.hϱ, le_rfl⟩
  obtain ⟨-, hTV⟩ := hiv 0 (blockLen (B k0)) hL p.ϱ ⟨le_rfl, le_rfl⟩
  set φ : ℝ × ℝ → ℝ := fun q => f q.1 * g q.2 with hφ
  have hφb : ∀ x, |φ x| ≤ 1 := fun x => by
    simp only [hφ, abs_mul]
    exact mul_le_one₀ (hf _) (abs_nonneg _) (hg _)
  have e1 : (Muon.Volatility.finiteTimeMeasure Fz (S0 k0) (SD k0) (blockLen (B k0)) p.ϱ).sum
      (fun x r => f x.1 * g x.2 * r) =
      Muon.Volatility.finInt (Muon.Volatility.finiteTimeMeasure Fz (S0 k0) (SD k0) (blockLen (B k0)) p.ϱ) φ := by
    unfold Muon.Volatility.finInt
    exact Finsupp.sum_congr fun x _ => by simp only [hφ]; ring
  rw [e1]
  set FLm := Muon.Volatility.finiteTimeMeasure Fz (S0 k0) (SD k0) (blockLen (B k0)) p.ϱ
  set Im := Muon.Volatility.measureInt Fz (S0 k0) (SD k0) 0 p.ϱ
  set Zm := Muon.Volatility.measureZeta cert p.γstar p.CSig (F k0) (SD k0) p.ϱ
  have hsplit : Muon.Volatility.finInt FLm φ - Muon.Volatility.finInt Zm φ =
      Muon.Volatility.finInt (FLm - Im) φ + Muon.Volatility.finInt (Im - Zm) φ := by
    rw [blk_finInt_sub, blk_finInt_sub]; ring
  rw [hsplit]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (blk_finInt_le _ _ hφb).trans ?_
    unfold blkTVL
    have hb : Fz.β = p.β := hβ k0
    have := hTV
    rw [hb] at this
    exact this
  · unfold blkE2
    rw [dif_pos (block_Ahat_norm _ _ hR)]
    exact le_rfl


private lemma blk_forcing_uniform (cert : Muon.External.GaussianOpNorm)
    (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ A ∈ NormStates (F k).C, opNorm A ≤ δ k →
      blkE2 cert p F S0 SD f g k A ≤ ε := by
  refine blk_uniform_eventual (fun k => (F k).C) (fun k A => blkE2 cert p F S0 SD f g k A) ?_ δ hδ
  intro φ hφ A hAN hAz
  have hA : ∀ j, fro (A j) = 1 := fun j => blk_norm_fro (hAN j)
  set R := blkRegime p F hyp.regime hyp.dims hyp.normBd hβ φ hφ A hA hAz with hRdef
  have hlim := Muon.Volatility.thm_app_vol_joint_forcing_iii_limit cert R (fun j => Ω' (φ j))
    (fun j => P' (φ j)) (fun j => S0 (φ j)) (fun j => SD (φ j))
  rw [tendsto_order]
  refine ⟨fun a ha => Eventually.of_forall fun j => ?_, fun a ha => ?_⟩
  · have : 0 ≤ blkE2 cert p F S0 SD f g (φ j) (A j) := by
      unfold blkE2
      split_ifs
      · exact abs_nonneg _
      · exact le_rfl
    linarith
  · filter_upwards [hlim (a / 2) (by linarith)] with j hj
    have h2 := ((hj 0 p.ϱ ⟨le_rfl, le_rfl⟩).2 f g hf hg)
    have : blkE2 cert p F S0 SD f g (φ j) (A j) ≤ a / 2 := by
      unfold blkE2
      rw [dif_pos (hA j)]
      exact h2
    linarith

end blkforce

section blkF1

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma blk_delta_entry_bdd (S : DynSetup p P m n B) (s : ℕ) :
    ∃ R : ℝ, ∀ (ω : Ω) (i : Fin m) (j : Fin n), |dynDelta S s ω i j| ≤ R := by
  induction s with
  | zero => exact ⟨fro (S.W0 - S.alg.Wstar), fun ω i j => block_abs_entry_le_fro _ i j⟩
  | succ s ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨R + p.h / B * ((m : ℝ) + 1), fun ω i j => ?_⟩
    have h1 := block_delta_sum p S s 1 ω
    simp only [Finset.range_one, Finset.sum_singleton, add_zero] at h1
    rw [h1, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have h2 := block_dynUpd_bound S s ω i j
    have hc : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg B)
    calc |dynDelta S s ω i j - p.h / B * dynUpd S s ω i j|
        ≤ |dynDelta S s ω i j| + |p.h / B * dynUpd S s ω i j| := abs_sub _ _
      _ ≤ R + p.h / B * ((m : ℝ) + 1) := by
          refine add_le_add (hR ω i j) ?_
          rw [abs_mul, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left h2 hc

private lemma blk_Xfg_delta_int [IsProbabilityMeasure P] (S : DynSetup p P m n B) (f g : ℝ → ℝ) (s : ℕ) :
    Integrable (fun ω => Xfg f g S.C (dynDelta S s ω)) P := by
  obtain ⟨R, hR⟩ := blk_delta_entry_bdd S s
  exact block_integrable_cont ((block_delta_meas S s).mono (block_past_le S s) le_rfl).aemeasurable R hR
    (Xfg f g S.C) (block_Xfg_cont f g S.C)

private lemma blk_incr_int [IsProbabilityMeasure P] (S : DynSetup p P m n B) (f g : ℝ → ℝ) (b : ℕ) :
    Integrable (blockIncr p f g S b) P :=
  (blk_Xfg_delta_int S f g _).sub (blk_Xfg_delta_int S f g _)

private lemma blk_tauPlus_iff (S : DynSetup p P m n B) (t : ℕ) (ω : Ω) :
    (t : ℕ∞) < tauPlus p S ω ↔ ∀ s ≤ t, dynDelta S s ω ∈ admAplus p S.C := by
  unfold tauPlus
  constructor
  · intro h s hs
    by_contra hnot
    have h1 : (⨅ (t' : ℕ) (_ : dynDelta S t' ω ∉ admAplus p S.C), (t' : ℕ∞)) ≤ (s : ℕ∞) := iInf₂_le s hnot
    exact absurd (lt_of_lt_of_le h h1) (by exact_mod_cast not_lt.2 hs)
  · intro h
    have h1 : ((t + 1 : ℕ) : ℕ∞) ≤ ⨅ (t' : ℕ) (_ : dynDelta S t' ω ∉ admAplus p S.C), (t' : ℕ∞) := by
      refine le_iInf₂ fun s hs => ?_
      have : ¬ s ≤ t := fun hst => hs (h s hst)
      exact_mod_cast Nat.succ_le_of_lt (not_le.1 this)
    exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self t) h1

private lemma blk_tauPlus_meas (S : DynSetup p P m n B) (t : ℕ) :
    MeasurableSet[dynPast S t] {ω | (t : ℕ∞) < tauPlus p S ω} := by
  have : {ω | (t : ℕ∞) < tauPlus p S ω} = ⋂ s ∈ Finset.range (t + 1), {ω | dynDelta S s ω ∈ admAplus p S.C} := by
    ext ω
    simp only [Set.mem_setOf_eq, blk_tauPlus_iff, Set.mem_iInter, Finset.mem_range]
    constructor
    · intro h s hs; exact h s (by omega)
    · intro h s hs; exact h s (by omega)
  rw [this]
  refine MeasurableSet.biInter (Finset.countable_toSet _) fun s hs => ?_
  have hst : s ≤ t := Nat.lt_succ_iff.1 (Finset.mem_range.1 hs)
  have hD : Measurable[dynPast S s] (dynDelta S s) := block_delta_meas S s
  exact (block_past_mono S hst) _ (hD (blk_admSet_meas S.C _))

end blkF1

section blkF1b

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma blk_tau_of_good (S : DynSetup p P m n B) (ω : Ω) (hL : 0 < blockLen B)
    (h0 : dynDelta S 0 ω ∈ admA p S.C)
    (hwin : ∀ b, dynDelta S (b * blockLen B) ω ∈ admA p S.C → ∀ u, b * blockLen B ≤ u →
        u ≤ b * blockLen B + blockLen B → dynDelta S u ω ∈ admAplus p S.C)
    (b : ℕ) (hb : ∀ b' ≤ b, dynDelta S (b' * blockLen B) ω ∈ admA p S.C) :
    ((b * blockLen B : ℕ) : ℕ∞) < tauPlus p S ω := by
  rw [blk_tauPlus_iff]
  intro s hs
  rcases Nat.eq_zero_or_pos s with rfl | hpos
  · exact blk_A_Aplus p h0
  · obtain ⟨b', hb'def⟩ : ∃ b', b' = (s - 1) / blockLen B := ⟨_, rfl⟩
    have hdm := Nat.div_add_mod' (s - 1) (blockLen B)
    rw [← hb'def] at hdm
    have hml := Nat.mod_lt (s - 1) hL
    have h1 : b' * blockLen B ≤ s - 1 := by omega
    have h2 : s ≤ b' * blockLen B + blockLen B := by omega
    have hb'b : b' ≤ b := by
      by_contra hcon
      have h3 : (b + 1) * blockLen B ≤ b' * blockLen B := Nat.mul_le_mul_right _ (by omega)
      rw [Nat.succ_mul] at h3
      omega
    exact hwin b' (hb b' hb'b) s (by omega) h2

end blkF1b

/-- The selfadjoint contraction `𝒲_{f,g}` as a linear map. -/
private def blkW {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) : Mat m n →ₗ[ℝ] Mat m n where
  toFun := wfg f g C
  map_add' := fun X Y => by unfold wfg; simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' := fun c X => by
    unfold wfg; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]

private lemma blkW_apply {m n : ℕ} (f g : ℝ → ℝ) (C : Covariances m n) (X : Mat m n) :
    blkW f g C X = wfg f g C X := rfl

section blkF1c

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma blk_cE_sum [IsProbabilityMeasure P] (S : DynSetup p P m n B) (t : ℕ) (Pt : Ω → Mat m n)
    (RP : ℝ) (hPm : ∀ i j, Measurable[dynPast S t] (fun ω => Pt ω i j))
    (hPb : ∀ ω i j, |Pt ω i j| ≤ RP) (s : Finset ℕ) :
    (fun ω => ∑ r ∈ s, frobIP (Pt ω)
        (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω)) =ᵐ[P]
      condExp (dynPast S t) P (fun ω => ∑ r ∈ s, frobIP (Pt ω) (dynUpd S (t + r) ω)) := by
  have hPmeas : Measurable Pt := block_mat_meas fun i j => (hPm i j).mono (block_past_le S t) le_rfl
  have hR : ∀ r, ∀ ω i j, |dynUpd S (t + r) ω i j| ≤ max RP ((m : ℝ) + 1) := fun r ω i j =>
    (block_dynUpd_bound S (t + r) ω i j).trans (le_max_right _ _)
  have hint : ∀ r ∈ s, Integrable (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω)) P := fun r _ =>
    block_integrable_cont2 hPmeas.aemeasurable (block_upd_meas' S (t + r)).aemeasurable (max RP ((m : ℝ) + 1))
      (fun ω i j => (hPb ω i j).trans (le_max_left _ _)) (hR r)
      (fun x : Mat m n × Mat m n => frobIP x.1 x.2) block_frobIP_cont
  have h1 := block_condExp_sum (dynPast S t) P s (fun r ω => frobIP (Pt ω) (dynUpd S (t + r) ω)) hint
  have h2 : ∀ r ∈ s, condExp (dynPast S t) P (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω)) =ᵐ[P]
      fun ω => frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω) :=
    fun r _ => block_condExp_frobIP_pull (dynPast S t) P (block_past_le S t) Pt (dynUpd S (t + r))
      (max RP ((m : ℝ) + 1)) hPm (fun ω i j => (hPb ω i j).trans (le_max_left _ _))
      (block_upd_meas' S (t + r)) (hR r)
  have h3 : ∀ᵐ ω ∂P, ∀ r ∈ s, condExp (dynPast S t) P (fun ω => frobIP (Pt ω) (dynUpd S (t + r) ω)) ω =
      frobIP (Pt ω) (Muon.Foundations.condExpMat (dynPast S t) P (dynUpd S (t + r)) ω) := by
    exact (Finset.eventually_all s).2 fun r hr => h2 r hr
  filter_upwards [h1, h3] with ω hω1 hω2
  rw [hω1]
  exact (Finset.sum_congr rfl fun r hr => (hω2 r hr)).symm

end blkF1c

private lemma blk_U1_bound (certP : Muon.External.GaussianPoincare)
    (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K : ℝ, ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n)
      (_hW : ∀ X : Mat m n, fro (W X) ≤ 1 * fro X) (t : ℕ), B0 ≤ B → prefixLen p.β B ≤ t →
      ∀ (Pt : Ω → Mat m n) (I : Set Ω), MeasurableSet[dynPast S t] I →
        (∀ ω ∈ I, (t : ℕ∞) < tauPlus p S ω) → (∀ ω ∈ I, Pt ω = W (dynDelta S t ω)) →
        ∫ ω in I, |condExp (dynPast S t) P (fun ω => ∑ r ∈ Finset.range (prefixLen p.β B),
            frobIP (Pt ω) (dynUpd S (t + r) ω)) ω| ∂P ≤ K * (prefixLen p.β B : ℝ) ^ 2 := by
  obtain ⟨B0, K, hK⟩ := lem_app_dyn_prefix_ii certP certOp p 1 zero_le_one
  refine ⟨B0, K, fun Ω _ P _ m n B S W hW t hB hq Pt I hI hIτ hIP => ?_⟩
  obtain ⟨hint, hbound⟩ := hK Ω P m n B S W hB hW t hq
  set G : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hG
  set ZW : Ω → ℝ := fun ω => |∑ r ∈ Finset.range (prefixLen p.β B), frobIP (W (dynDelta S t ω)) (dynUpd S (t + r) ω)|
    with hZW
  have hIm : MeasurableSet I := block_past_le S t _ hI
  have hGm : MeasurableSet G := block_past_le S t _ (blk_tauPlus_meas S t)
  have h1 := setIntegral_abs_condExp_le (μ := P) hI
    (fun ω => ∑ r ∈ Finset.range (prefixLen p.β B), frobIP (Pt ω) (dynUpd S (t + r) ω))
  refine h1.trans ?_
  have h2 : ∫ ω in I, |∑ r ∈ Finset.range (prefixLen p.β B), frobIP (Pt ω) (dynUpd S (t + r) ω)| ∂P =
      ∫ ω in I, ZW ω ∂P := by
    refine setIntegral_congr_fun hIm fun ω hω => ?_
    simp only [hZW, hIP ω hω]
  rw [h2]
  have hint' : Integrable (G.indicator ZW) P := hint
  have hIG : ∫ ω in I, ZW ω ∂P ≤ ∫ ω in G, ZW ω ∂P :=
    setIntegral_mono_set ((integrable_indicator_iff hGm).1 hint') (Eventually.of_forall fun ω => abs_nonneg _)
      (Eventually.of_forall fun ω hω => hIτ ω hω)
  refine hIG.trans ?_
  rw [← integral_indicator hGm]
  exact hbound

/-- The quantity `r̄_B = L⁻¹ + B^{-1/2} + L²/B + L^{3/2}/√B + L/√B + L³/B` of `lem:app-dyn-block`(c). -/
private def blkRbar (B : ℕ) : ℝ :=
  1 / (blockLen B : ℝ) + 1 / Real.sqrt (B : ℝ) + (blockLen B : ℝ) ^ 2 / (B : ℝ) +
    (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (B : ℝ) + (blockLen B : ℝ) / Real.sqrt (B : ℝ) +
    (blockLen B : ℝ) ^ 3 / (B : ℝ)

private lemma blk_r_le (B : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x + (1 + x) ^ 2) / (blockLen B : ℝ) + (1 + x) / Real.sqrt (B : ℝ) +
      (blockLen B : ℝ) ^ 2 / (B : ℝ) + (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (B : ℝ) +
      (1 + x) * (blockLen B : ℝ) / Real.sqrt (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) ≤
    (7 / 2 + 5 / 2 * x ^ 2) * blkRbar B := by
  unfold blkRbar
  have hL : 0 ≤ (blockLen B : ℝ) := Nat.cast_nonneg _
  have hB : 0 ≤ (B : ℝ) := Nat.cast_nonneg _
  have hs : 0 ≤ Real.sqrt (B : ℝ) := Real.sqrt_nonneg _
  have hr : 0 ≤ (blockLen B : ℝ) ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hL _
  set Λ : ℝ := 7 / 2 + 5 / 2 * x ^ 2 with hΛ
  have h1 : 1 + x + (1 + x) ^ 2 ≤ Λ := by nlinarith [sq_nonneg (x - 1)]
  have h2 : 1 + x ≤ Λ := by nlinarith [sq_nonneg (x - 1)]
  have h3 : 1 ≤ Λ := by nlinarith [sq_nonneg x]
  have e1 : (1 + x + (1 + x) ^ 2) / (blockLen B : ℝ) ≤ Λ * (1 / (blockLen B : ℝ)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right h1 hL
  have e2 : (1 + x) / Real.sqrt (B : ℝ) ≤ Λ * (1 / Real.sqrt (B : ℝ)) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right h2 hs
  have e3 : (blockLen B : ℝ) ^ 2 / (B : ℝ) ≤ Λ * ((blockLen B : ℝ) ^ 2 / (B : ℝ)) :=
    le_mul_of_one_le_left (by positivity) h3
  have e4 : (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (B : ℝ) ≤
      Λ * ((blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (B : ℝ)) :=
    le_mul_of_one_le_left (by positivity) h3
  have e5 : (1 + x) * (blockLen B : ℝ) / Real.sqrt (B : ℝ) ≤ Λ * ((blockLen B : ℝ) / Real.sqrt (B : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h2 hL) hs
  have e6 : (blockLen B : ℝ) ^ 3 / (B : ℝ) ≤ Λ * ((blockLen B : ℝ) ^ 3 / (B : ℝ)) :=
    le_mul_of_one_le_left (by positivity) h3
  linarith

private lemma blk_U3_bound (certOp : Muon.External.GaussianOpNormL6) (p : DynParams) :
    ∃ B0 : ℕ, ∃ K Cb : ℝ, 0 ≤ K ∧ 0 ≤ Cb ∧ ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (m n B : ℕ) (S : DynSetup p P m n B) (W : Mat m n →ₗ[ℝ] Mat m n)
      (_hsa : ∀ X Y : Mat m n, frobIP (W X) Y = frobIP X (W Y)) (_hc : ∀ X : Mat m n, fro (W X) ≤ fro X)
      (t : ℕ), B0 ≤ B → 0 < B →
      ∀ (I : Set Ω), MeasurableSet[dynPast S t] I → (∀ ω ∈ I, (t : ℕ∞) < tauPlus p S ω) →
        (∀ ω ∈ I, dynDelta S t ω ∈ admA p S.C) →
        ∫ ω in I, |condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
            (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
              frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω)))) ω| ∂P ≤
          (blockLen B : ℝ) * B * K * Cb * blkRbar B := by
  obtain ⟨B1, K1, hq⟩ := lem_app_dyn_quadratic certOp p
  have hrlo : 0 < p.r0 / 2 / 2 := by linarith [p.hr0]
  have hle : p.r0 / 2 / 2 ≤ 2 * (p.r1 + 1 / 2) := by linarith [p.hr, p.hr0]
  have hbuf := lem_app_dyn_buffer_i p (p.r0 / 2 / 2) (2 * (p.r1 + 1 / 2)) (2 * (p.Estar + 1) + 2) hrlo hle
  set Mb : ℝ := 2 * p.cM + 4 * cMConst p.CSig p.γstar * (2 * (p.r1 + 1 / 2)) with hMb
  have hMb0 : 0 ≤ Mb := by
    have := p.hcM
    have h1 : 0 ≤ cMConst p.CSig p.γstar := by unfold cMConst; positivity
    have : 0 ≤ 2 * (p.r1 + 1 / 2) := by linarith [p.hr, p.hr0]
    positivity
  refine ⟨B1, |K1|, 7 / 2 + 5 / 2 * Mb, abs_nonneg _, by positivity, ?_⟩
  intro Ω _ P _ m n B S W hsa hc t hB hBpos I hI hIτ hIA
  obtain ⟨-, hqa⟩ := hq Ω P m n B S hB t W hsa hc
  have hIm : MeasurableSet I := block_past_le S t _ hI
  have hbuf' := hbuf Ω P m n B S (tauPlus p S) (fun t' => blk_tauPlus_meas S t')
    (fun t' ω h => (blk_tauPlus_iff S t' ω).1 h t' le_rfl) t
  set f : Ω → ℝ := fun ω => fro (dynBuf S t ω) ^ 2 with hfdef
  have hfm : Measurable f :=
    blk_cont_fro_sq.measurable.comp ((block_buf_meas S t).mono (block_past_le S t) le_rfl)
  have hf0 : ∀ ω, 0 ≤ f ω := fun ω => sq_nonneg _
  set G : Set Ω := {ω | (t : ℕ∞) ≤ tauPlus p S ω} with hG
  set G0 : Set Ω := {ω | (t : ℕ∞) < tauPlus p S ω} with hG0
  have hG0m : MeasurableSet G0 := block_past_le S t _ (blk_tauPlus_meas S t)
  have hGint : Integrable (G.indicator f) P := hbuf'.1
  have hG0int : Integrable (G0.indicator f) P := by
    refine hGint.mono' (hfm.indicator hG0m).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ G0
    · have : ω ∈ G := le_of_lt (show (t : ℕ∞) < tauPlus p S ω from h)
      simp [Set.indicator_of_mem h, Set.indicator_of_mem this, abs_of_nonneg (hf0 ω)]
    · simp [Set.indicator_of_notMem h]
      exact Set.indicator_nonneg (fun ω _ => hf0 ω) ω
  have hfI : ∫ ω in I, f ω ∂P ≤ Mb * B := by
    have h1 : ∫ ω in I, f ω ∂P ≤ ∫ ω in G0, f ω ∂P :=
      setIntegral_mono_set ((integrable_indicator_iff hG0m).1 hG0int) (Eventually.of_forall hf0)
        (Eventually.of_forall fun ω hω => hIτ ω hω)
    have h2 : ∫ ω in G0, f ω ∂P ≤ ∫ ω, G.indicator f ω ∂P := by
      rw [← integral_indicator hG0m]
      refine integral_mono hG0int hGint fun ω => ?_
      by_cases h : ω ∈ G0
      · have : ω ∈ G := le_of_lt (show (t : ℕ∞) < tauPlus p S ω from h)
        simp [Set.indicator_of_mem h, Set.indicator_of_mem this]
      · simp [Set.indicator_of_notMem h]
        exact Set.indicator_nonneg (fun ω _ => hf0 ω) ω
    have h3 := hbuf'.2
    refine h1.trans (h2.trans (h3.trans ?_))
    simp only [hMb]
    nlinarith
  have hfIint : IntegrableOn f I P :=
    ((integrable_indicator_iff hG0m).1 hG0int).mono_set (fun ω hω => hIτ ω hω)
  set rb := blkRbar B with hrb
  have hrb0 : 0 ≤ rb := by
    rw [hrb]; unfold blkRbar
    have : 0 ≤ (blockLen B : ℝ) := Nat.cast_nonneg _
    positivity
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  set g : Ω → ℝ := fun ω => (blockLen B : ℝ) * B * |K1| * rb * (7 / 2 + 5 / 2 * (f ω / B)) with hgdef
  have hgint : IntegrableOn g I P := by
    have : IntegrableOn (fun ω => (7 / 2 : ℝ) + 5 / 2 * (f ω / B)) I P :=
      (integrableOn_const (by simp [measure_lt_top])).add ((hfIint.div_const _).const_mul _)
    exact this.const_mul _
  have hae : ∀ᵐ ω ∂P, ω ∈ I → |condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
            (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
              frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω)))) ω| ≤ g ω := by
    filter_upwards [hqa] with ω hω hωI
    have h1 := hω (hIA ω hωI)
    have hL : (0 : ℝ) < (blockLen B : ℝ) * B := by
      have : 0 < blockLen B := block_blockLen_pos hBpos
      positivity
    rw [div_le_iff₀ hL] at h1
    have hx : 0 ≤ fro (dynBuf S t ω) / Real.sqrt B := div_nonneg (blk_fro_nn _) (Real.sqrt_nonneg _)
    have hr := blk_r_le B _ hx
    have hxx : (fro (dynBuf S t ω) / Real.sqrt B) ^ 2 = f ω / B := by
      rw [div_pow, Real.sq_sqrt hBr.le]
    rw [hxx] at hr
    have hK : K1 ≤ |K1| := le_abs_self _
    calc _ ≤ K1 * _ * ((blockLen B : ℝ) * B) := h1
      _ ≤ |K1| * ((7 / 2 + 5 / 2 * (f ω / B)) * rb) * ((blockLen B : ℝ) * B) := by
          refine mul_le_mul_of_nonneg_right ?_ hL.le
          have hr0 : 0 ≤ (1 + fro (dynBuf S t ω) / Real.sqrt B + (1 + fro (dynBuf S t ω) / Real.sqrt B) ^ 2) /
              (blockLen B : ℝ) + (1 + fro (dynBuf S t ω) / Real.sqrt B) / Real.sqrt B +
              (blockLen B : ℝ) ^ 2 / B + (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt B +
              (1 + fro (dynBuf S t ω) / Real.sqrt B) * (blockLen B : ℝ) / Real.sqrt B +
              (blockLen B : ℝ) ^ 3 / B := by
            have : 0 ≤ (blockLen B : ℝ) := Nat.cast_nonneg _
            positivity
          calc _ ≤ |K1| * _ := mul_le_mul_of_nonneg_right hK hr0
            _ ≤ _ := mul_le_mul_of_nonneg_left hr (abs_nonneg _)
      _ = g ω := by simp only [hgdef]; ring
  have hmono := integral_mono_of_nonneg (μ := P.restrict I) (f := fun ω => |condExp (dynPast S t) P ({ω | dynDelta S t ω ∈ admA p S.C}.indicator
            (fun ω => 2 * frobIP (dynStatSum p S t ω) (W (dynSumErr p S t ω)) +
              frobIP (dynSumErr p S t ω) (W (dynSumErr p S t ω)))) ω|) (g := g)
    (Eventually.of_forall fun ω => abs_nonneg _) hgint ((ae_restrict_iff' hIm).2 hae)
  refine hmono.trans ?_
  have hc0 : 0 ≤ (blockLen B : ℝ) * B * |K1| * rb := by positivity
  have hcalc : ∫ ω in I, g ω ∂P =
      (blockLen B : ℝ) * B * |K1| * rb * ∫ ω in I, (7 / 2 + 5 / 2 * (f ω / B)) ∂P := by
    simp only [hgdef]
    exact integral_const_mul _ _
  rw [hcalc]
  have h1 : ∫ ω in I, (7 / 2 + 5 / 2 * (f ω / B)) ∂P ≤ 7 / 2 + 5 / 2 * Mb := by
    have hint1 : IntegrableOn (fun _ : Ω => (7 / 2 : ℝ)) I P := integrableOn_const (by simp)
    have hint2 : IntegrableOn (fun ω => 5 / 2 * (f ω / B)) I P := (hfIint.div_const _).const_mul _
    rw [integral_add hint1 hint2, setIntegral_const, integral_const_mul, integral_div]
    have hμ : P.real I ≤ 1 := measureReal_le_one
    have h2 : (∫ ω in I, f ω ∂P) / B ≤ Mb := by
      rw [div_le_iff₀ hBr]; linarith
    simp only [smul_eq_mul]
    nlinarith
  calc _ ≤ (blockLen B : ℝ) * B * |K1| * rb * (7 / 2 + 5 / 2 * Mb) := mul_le_mul_of_nonneg_left h1 hc0
    _ = _ := by ring

private lemma blk_lam_alg {m n : ℕ} (h Bn R A Z FLsum CQ Wv : ℝ) (L q : ℕ) (hq : q ≤ L) (hB : Bn ≠ 0)
    (Wd Vb : Mat m n) (cE : ℕ → Mat m n) :
    -2 * (h / Bn) * (∑ r ∈ Finset.range L, frobIP Wd (cE r)) + (h / Bn) ^ 2 * (L : ℝ) ^ 2 * Wv +
        (h / Bn) ^ 2 * (L : ℝ) * Bn * FLsum + (h / Bn) ^ 2 * CQ -
        (L : ℝ) / Bn * (-(2 * h / Real.sqrt R) * A + h ^ 2 * Z) =
      (-2 * (h / Bn) * ∑ r ∈ Finset.range q, frobIP Wd (cE r - Vb)) +
      (-2 * (h / Bn) * ∑ r ∈ Finset.Ico q L, frobIP Wd (cE r - Vb)) +
      (h / Bn) ^ 2 * CQ + (h / Bn) ^ 2 * (L : ℝ) ^ 2 * Wv +
      (-2 * (h / Bn) * (L : ℝ) * (frobIP Wd Vb - (Real.sqrt R)⁻¹ * A)) +
      (h ^ 2 * (L : ℝ) / Bn * (FLsum - Z)) := by
  have hlin : ∀ r, frobIP Wd (cE r - Vb) = frobIP Wd (cE r) - frobIP Wd Vb := by
    intro r
    unfold frobIP
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
  simp only [hlin, Finset.sum_sub_distrib]
  have hsplit := Finset.sum_range_add_sum_Ico (fun r => frobIP Wd (cE r)) hq
  simp only [Finset.sum_const, Finset.card_range, Nat.card_Ico, nsmul_eq_mul] at *
  have e1 : ∑ r ∈ Finset.Ico q L, frobIP Wd (cE r) =
      ∑ r ∈ Finset.range L, frobIP Wd (cE r) - ∑ r ∈ Finset.range q, frobIP Wd (cE r) := by
    linarith
  rw [e1]
  have hq' : ((L - q : ℕ) : ℝ) = (L : ℝ) - q := by push_cast [Nat.cast_sub hq]; ring
  rw [hq']
  field_simp
  ring

private lemma blk_opNorm_le_fro {m n : ℕ} (K : Mat m n) : opNorm K ≤ fro K := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, fro,
    ← Real.sqrt_mul (by positivity)]
  refine Real.sqrt_le_sqrt ?_
  have hK : ∀ i, ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i =
      ∑ j, K i j * x.ofLp j := fun i => by
    simp [Matrix.toEuclideanLin, Matrix.mulVec, dotProduct]
  have hi : ∀ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤
      (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) := by
    intro i
    calc
      ‖∑ j, K i j * x.ofLp j‖ ^ 2 ≤ (∑ j, ‖K i j‖ * ‖x.ofLp j‖) ^ 2 := by
        refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        exact norm_mul _ _
      _ ≤ (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  calc
    ∑ i, ‖((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)) x).ofLp i‖ ^ 2 =
        ∑ i, ‖∑ j, K i j * x.ofLp j‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => by rw [hK i]
    _ ≤ ∑ i, (∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = (∑ i, ∑ j, ‖K i j‖ ^ 2) * (∑ j, ‖x.ofLp j‖ ^ 2) :=
      (Finset.sum_mul _ _ _).symm

private lemma blk_U1_alg (a q CE X M : ℝ) (ha : 0 ≤ a) (hq : 0 ≤ q) (hX : |X| ≤ M) :
    |(-2 * a) * (CE - q * X)| ≤ 2 * a * |CE| + 2 * a * q * M := by
  rw [abs_mul, show |(-2 * a)| = 2 * a by rw [abs_of_nonpos (by linarith)]; ring]
  have h1 : |CE - q * X| ≤ |CE| + q * M := by
    refine (abs_sub _ _).trans (add_le_add le_rfl ?_)
    rw [abs_mul, abs_of_nonneg hq]
    exact mul_le_mul_of_nonneg_left hX hq
  calc 2 * a * |CE - q * X| ≤ 2 * a * (|CE| + q * M) := mul_le_mul_of_nonneg_left h1 (by linarith)
    _ = _ := by ring

private lemma blk_U2_alg (a L S : ℝ) (ha : 0 ≤ a) (hL : 0 < L) :
    |(-2 * a) * S| = 2 * a * L * |(1 / L) * S| := by
  have e1 : |(-2 * a) * S| = 2 * a * |S| := by
    rw [abs_mul, show |(-2 * a)| = 2 * a by rw [abs_of_nonpos (by linarith)]; ring]
  have e2 : |(1 / L) * S| = (1 / L) * |S| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / L)]
  rw [e1, e2]
  field_simp

private lemma blk_tri6 (a b c d e f : ℝ) :
    |a + b + c + d + e + f| ≤ |a| + |b| + |c| + |d| + |e| + |f| := by
  have h1 := abs_add_le (a + b + c + d + e) f
  have h2 := abs_add_le (a + b + c + d) e
  have h3 := abs_add_le (a + b + c) d
  have h4 := abs_add_le (a + b) c
  have h5 := abs_add_le a b
  linarith

set_option maxHeartbeats 4000000 in
private theorem blk_lam_bound (certQ : Muon.External.GaussianQuadFormLp)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (p : DynParams) (δ : ℕ → ℝ) (hδ : Antitone δ) (hδ0 : Tendsto δ atTop (𝓝 0)) :
    ∃ (B0 : ℕ) (Kp Kr Kq Cb : ℝ), 0 ≤ Kp ∧ 0 ≤ Kq ∧ 0 ≤ Cb ∧
      ∀ (Ω : Type) [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (m n B : ℕ)
        (S : DynSetup p P m n B) (SP : SpectralData S.C) (c : DynCoeff p SP B) (f g : ℝ → ℝ)
        (_hf : ∀ x, |f x| ≤ 1) (_hg : ∀ x, |g x| ≤ 1) (T : ℝ) (_hT : 0 ≤ T)
        (Ω'' : Type) [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
        (S'' : FrozenSamples P'' m n B) (FL : Mat m n → (ℝ × ℝ) →₀ ℝ)
        (_hFL : ∀ (D : Mat m n) (Fz : FrozenParams m n B) (hC : Fz.C = S.C),
          Fz.A = Ahat S.C D → 0 < riskSigma S.C D → Fz.β = p.β →
            FL D = Muon.Volatility.finiteTimeMeasure Fz S'' (hC ▸ SP) (blockLen B) p.ϱ)
        (CV e1 e2 : ℝ) (_hCV : 0 ≤ CV) (_he1 : 0 ≤ e1) (_he2 : 0 ≤ e2)
        (_hVb : ∀ (t : ℕ) (D : Mat m n), D ∈ admA p S.C → diffuseness S.C D ≤ δ B →
          fro (dynVbar p S t D) ≤ CV)
        (_hDR : ∀ (t : ℕ) (D : Mat m n), D ∈ admA p S.C → diffuseness S.C D ≤ δ B →
          |frobIP (wfg f g S.C D) (dynVbar p S t D) - (Real.sqrt (riskSigma S.C D))⁻¹ *
            ∑ i, ∑ j, modeQ SP D i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))| ≤
            fro D * e1)
        (_hFR : ∀ (D : Mat m n), D ∈ admA p S.C → diffuseness S.C D ≤ δ B →
          |(FL D).sum (fun x r => f x.1 * g x.2 * r) -
            ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j)| ≤ e2),
        B0 ≤ B → 0 < B → prefixLen p.β B ≤ blockLen B →
        ∀ b ∈ Finset.Ico 1 (blkJ T B),
          Integrable (fun ω => (if b < blkBstar S (δ B) (blkJ T B) ω then (1 : ℝ) else 0) *
            |blkLam S SP c f g b ω|) P ∧
          ∫ ω, (if b < blkBstar S (δ B) (blkJ T B) ω then (1 : ℝ) else 0) *
            |blkLam S SP c f g b ω| ∂P ≤
            (blockLen B : ℝ) / B * (2 * p.h * Kp * (prefixLen p.β B : ℝ) ^ 2 / (blockLen B : ℝ) +
              2 * p.h * (prefixLen p.β B : ℝ) * Real.sqrt (p.Estar + 1) * CV / (blockLen B : ℝ) +
              2 * p.h * responseRho p Kr (Real.sqrt (p.Estar + 1)) δ B +
              p.h ^ 2 * Kq * Cb * blkRbar B + p.h ^ 2 * (blockLen B : ℝ) * CV ^ 2 / B +
              2 * p.h * Real.sqrt (p.Estar + 1) * e1 + p.h ^ 2 * e2) := by
  classical
  obtain ⟨Bw, hBw⟩ := blk_window p
  obtain ⟨B1, K1, hK1⟩ := blk_U1_bound certP certOp p
  obtain ⟨B3, K3, Cb, hK3, hCb, hK3b⟩ := blk_U3_bound certOp p
  obtain ⟨B2, K2, hK2⟩ := prop_app_dyn_response_i certQ certOp certP p (Real.sqrt (p.Estar + 1)) δ hδ hδ0
  refine ⟨max (max Bw B1) (max B2 B3), |K1|, K2, K3, Cb, abs_nonneg _, hK3, hCb, ?_⟩
  intro Ω _ P _ m n B S SP c f g hf hg T hT Ω'' _ P'' _ S'' FL hFL CV e1 e2 hCV he1 he2 hVb hDR hFR
    hB hBpos hqL b hb
  have hBw' : Bw ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hB1 : B1 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hB2 : B2 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB3 : B3 ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hLpos : 0 < blockLen B := block_blockLen_pos hBpos
  obtain ⟨hb1, hbJ⟩ := Finset.mem_Ico.1 hb
  have hwinB := hBw Ω P m n B S hBw'
  set RA : ℝ := Real.sqrt (p.Estar + 1) with hRA
  have hRA0 : 0 ≤ RA := Real.sqrt_nonneg _
  have hAfro : ∀ D : Mat m n, D ∈ admA p S.C → fro D ≤ RA := by
    intro D hD
    simp only [admA, admSetOf, admBase, Set.mem_setOf_eq] at hD
    exact Real.le_sqrt_of_sq_le hD.2.2
  have hout : opNorm S.C.Sout ≤ p.CSig := S.size.2.1
  have hin : opNorm S.C.Sin ≤ p.CSig := S.size.2.2
  obtain ⟨hμm, hlm⟩ := blk_spec_mem SP p.CSig hout hin
  have hf' : ∀ i, |f (SP.μ i)| ≤ 1 := fun i => hf _
  have hg' : ∀ j, |g (SP.lam j)| ≤ 1 := fun j => hg _
  have hfI : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1 := fun x _ => hf x
  have hgI : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1 := fun x _ => hg x
  -- the stopping event
  set d : ℝ := δ B with hd
  set J := blkJ T B with hJ
  set bs := blkBstar S d J with hbs
  set I : Set Ω := {ω | b < bs ω} with hIdef
  have hI : MeasurableSet[dynPast S (b * blockLen B)] I := blk_bstar_meas S d J b
  have hIm : MeasurableSet I := block_past_le S _ _ hI
  have hIA : ∀ ω ∈ I, dynDelta S (b * blockLen B) ω ∈ admA p S.C := fun ω hω =>
    blk_bstar_A S d J ω b hω
  have hIδ : ∀ ω ∈ I, diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ d := fun ω hω =>
    (((blk_bstar_lt_iff S d J ω b).1 hω).2 b le_rfl).2
  have hIτ : ∀ ω ∈ I, ((b * blockLen B : ℕ) : ℕ∞) < tauPlus p S ω := by
    intro ω hω
    refine blk_tau_of_good S ω hLpos (blk_h0 S ω)
      (fun b' hb' u h1 h2 => (hwinB ω b' hb' u h1 h2).1) b
      (fun b' hb' => blk_bstar_A S d J ω b' (lt_of_le_of_lt hb' hω))
  have hqt : prefixLen p.β B ≤ b * blockLen B := hqL.trans (Nat.le_mul_of_pos_left _ hb1)
  -- the test matrix
  set Pt : Ω → Mat m n := fun ω => if dynDelta S (b * blockLen B) ω ∈ admA p S.C then
    wfg f g S.C (dynDelta S (b * blockLen B) ω) else 0 with hPt
  have hPtI : ∀ ω ∈ I, Pt ω = blkW f g S.C (dynDelta S (b * blockLen B) ω) := fun ω hω => by
    simp only [hPt, if_pos (hIA ω hω)]; rfl
  have hIPt := hPtI
  have hPtb : ∀ ω i j, |Pt ω i j| ≤ RA := by
    intro ω i j
    by_cases h : dynDelta S (b * blockLen B) ω ∈ admA p S.C
    · simp only [hPt, if_pos h]
      exact (block_abs_entry_le_fro _ i j).trans ((blk_wfg_fro_le f g SP hf' hg' _).trans (hAfro _ h))
    · simp only [hPt, if_neg h]; simpa using hRA0
  have hPtf : ∀ ω, fro (Pt ω) ≤ RA ∧ opNorm (Pt ω) ≤ RA := by
    intro ω
    by_cases h : dynDelta S (b * blockLen B) ω ∈ admA p S.C
    · simp only [hPt, if_pos h]
      have h1 : fro (wfg f g S.C (dynDelta S (b * blockLen B) ω)) ≤ RA :=
        (blk_wfg_fro_le f g SP hf' hg' _).trans (hAfro _ h)
      exact ⟨h1, (blk_opNorm_le_fro _).trans h1⟩
    · simp only [hPt, if_neg h]
      have : fro (0 : Mat m n) = 0 := by simp [fro]
      have h2 : opNorm (0 : Mat m n) = 0 := by simp [opNorm]
      exact ⟨by rw [this]; exact hRA0, by rw [h2]; exact hRA0⟩
  have hPtm : ∀ i j, Measurable[dynPast S (b * blockLen B)] (fun ω => Pt ω i j) := by
    intro i j
    have hD : Measurable[dynPast S (b * blockLen B)] (dynDelta S (b * blockLen B)) := block_delta_meas S _
    have hP : Measurable[dynPast S (b * blockLen B)] Pt := by
      refine Measurable.ite (hD (blk_admA_meas p S.C)) ?_ measurable_const
      exact (block_wfg_cont f g S.C).measurable.comp hD
    exact block_entry_meas hP i j
  -- the identity
  have hid := eqn_app_dyn_block_identity p S f g b S'' SP FL hFL
  obtain ⟨-, -, -, hid4⟩ := hid
  have hAmeas : MeasurableSet[dynPast S (b * blockLen B)]
      {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C} :=
    (block_delta_meas S _) (blk_admA_meas p S.C)
  have hincr : (fun ω => Xfg f g S.C (dynDelta S (b * blockLen B + blockLen B) ω) -
      Xfg f g S.C (dynDelta S (b * blockLen B) ω)) = blockIncr p f g S b := by
    funext ω; simp only [blockIncr]; rw [Nat.succ_mul]
  rw [hincr] at hid4
  have hci := condExp_indicator (μ := P) (blk_incr_int S f g b) hAmeas
  -- abbreviations
  set Zq : Ω → ℝ := {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator
    (fun ω => 2 * frobIP (dynStatSum p S (b * blockLen B) ω) (wfg f g S.C (dynSumErr p S (b * blockLen B) ω)) +
      frobIP (dynSumErr p S (b * blockLen B) ω) (wfg f g S.C (dynSumErr p S (b * blockLen B) ω))) with hZq
  set Z1 : Ω → ℝ := fun ω => ∑ r ∈ Finset.range (prefixLen p.β B),
    frobIP (Pt ω) (dynUpd S (b * blockLen B + r) ω) with hZ1
  set avg : Ω → ℝ := fun ω => (1 / (blockLen B : ℝ)) *
    ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B), frobIP (Pt ω)
      (Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dynUpd S (b * blockLen B + r)) ω -
        dynVbar p S (b * blockLen B) (dynDelta S (b * blockLen B) ω)) with havg
  set G : Ω → ℝ := fun ω =>
    2 * p.h / B * |condExp (dynPast S (b * blockLen B)) P Z1 ω| +
      2 * p.h / B * (prefixLen p.β B : ℝ) * RA * CV +
      2 * p.h * blockLen B / B * |avg ω| +
      (p.h / B) ^ 2 * |condExp (dynPast S (b * blockLen B)) P Zq ω| +
      (p.h / B) ^ 2 * (blockLen B : ℝ) ^ 2 * CV ^ 2 +
      2 * (p.h / B) * (blockLen B : ℝ) * RA * e1 + p.h ^ 2 * blockLen B / B * e2 with hGdef
  have hsumq := blk_cE_sum S (b * blockLen B) Pt RA hPtm hPtb (Finset.range (prefixLen p.β B))
  have hpoint : ∀ᵐ ω ∂P, ω ∈ I → |blkLam S SP c f g b ω| ≤ G ω := by
    filter_upwards [hid4, hci, hsumq] with ω h1 h2 h3 hωI
    have hωA := hIA ω hωI
    have hωδ := hIδ ω hωI
    have hRpos : 0 < riskSigma S.C (dynDelta S (b * blockLen B) ω) := by
      have h := hωA
      simp only [admA, admSetOf, admBase, Set.mem_setOf_eq] at h
      linarith [h.1, p.hr0]
    have hωAm : ω ∈ {ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C} := hωA
    have h1' := h1
    rw [Set.indicator_of_mem hωAm] at h1'
    have h2' : condExp (dynPast S (b * blockLen B)) P
        ({ω | dynDelta S (b * blockLen B) ω ∈ admA p S.C}.indicator (blockIncr p f g S b)) ω =
        condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b) ω := by
      rw [h2, Set.indicator_of_mem hωAm]
    set D := dynDelta S (b * blockLen B) ω with hD
    set Vb := dynVbar p S (b * blockLen B) D with hVb'
    set cEr : ℕ → Mat m n := fun r =>
      Muon.Foundations.condExpMat (dynPast S (b * blockLen B)) P (dynUpd S (b * blockLen B + r)) ω with hcEr
    set Aω : ℝ := ∑ i, ∑ j, modeQ SP D i j * (tensorFG f g (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j))
      with hAω
    set Zω : ℝ := ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f g (SP.μ i, SP.lam j) with hZω
    set FLs : ℝ := (FL D).sum (fun x r => f x.1 * g x.2 * r) with hFLs
    set CQ : ℝ := condExp (dynPast S (b * blockLen B)) P Zq ω with hCQ
    set Wv : ℝ := frobIP Vb (wfg f g S.C Vb) with hWv
    have hBne : (B : ℝ) ≠ 0 := by exact_mod_cast hBpos.ne'
    have hLne : (blockLen B : ℝ) ≠ 0 := by exact_mod_cast hLpos.ne'
    have hlam : blkLam S SP c f g b ω =
        (-2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (prefixLen p.β B), frobIP (wfg f g S.C D) (cEr r - Vb)) +
        (-2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
          frobIP (wfg f g S.C D) (cEr r - Vb)) +
        (p.h / (B : ℝ)) ^ 2 * CQ + (p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) ^ 2 * Wv +
        (-2 * (p.h / (B : ℝ)) * (blockLen B : ℝ) *
          (frobIP (wfg f g S.C D) Vb - (Real.sqrt (riskSigma S.C D))⁻¹ * Aω)) +
        (p.h ^ 2 * (blockLen B : ℝ) / (B : ℝ) * (FLs - Zω)) := by
      unfold blkLam blkF
      show condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b) ω -
        (blockLen B : ℝ) / B * fieldOp p.h c.d c.ζ (specMeasure SP D) (tensorFG f g) = _
      rw [← h2', h1', blk_F_formula, if_pos hRpos]
      exact blk_lam_alg p.h (B : ℝ) (riskSigma S.C D) Aω Zω FLs CQ Wv (blockLen B)
        (prefixLen p.β B) hqL hBne (wfg f g S.C D) Vb cEr
    have hq0 : (0 : ℝ) ≤ (prefixLen p.β B : ℝ) := Nat.cast_nonneg _
    have ha : 0 ≤ p.h / (B : ℝ) := div_nonneg p.hh.le (Nat.cast_nonneg B)
    have hWd : wfg f g S.C D = Pt ω := by rw [hPtI ω hωI]; rfl
    have hVbn : fro Vb ≤ CV := hVb (b * blockLen B) D hωA hωδ
    have hPV : |frobIP (Pt ω) Vb| ≤ RA * CV :=
      (blk_frobIP_le _ _).trans (mul_le_mul (hPtf ω).1 hVbn (blk_fro_nn _) hRA0)
    have hlinq : ∀ (X : Mat m n) (r : ℕ), frobIP X (cEr r - Vb) = frobIP X (cEr r) - frobIP X Vb := by
      intro X r; unfold frobIP; simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.trace_sub]
    have h3' : ∑ r ∈ Finset.range (prefixLen p.β B), frobIP (Pt ω) (cEr r) =
        condExp (dynPast S (b * blockLen B)) P Z1 ω := h3
    have hsum1 : ∑ r ∈ Finset.range (prefixLen p.β B), frobIP (wfg f g S.C D) (cEr r - Vb) =
        condExp (dynPast S (b * blockLen B)) P Z1 ω - (prefixLen p.β B : ℝ) * frobIP (Pt ω) Vb := by
      rw [hWd]
      simp only [hlinq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rw [h3']
    have hU1 : |-2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.range (prefixLen p.β B),
        frobIP (wfg f g S.C D) (cEr r - Vb)| ≤
        2 * p.h / B * |condExp (dynPast S (b * blockLen B)) P Z1 ω| +
          2 * p.h / B * (prefixLen p.β B : ℝ) * RA * CV := by
      rw [hsum1]
      have := blk_U1_alg (p.h / (B : ℝ)) (prefixLen p.β B : ℝ)
        (condExp (dynPast S (b * blockLen B)) P Z1 ω) (frobIP (Pt ω) Vb) (RA * CV) ha hq0 hPV
      calc _ ≤ _ := this
        _ = _ := by ring
    have hU2 : |-2 * (p.h / (B : ℝ)) * ∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B),
        frobIP (wfg f g S.C D) (cEr r - Vb)| = 2 * p.h * blockLen B / B * |avg ω| := by
      rw [hWd]
      have := blk_U2_alg (p.h / (B : ℝ)) (blockLen B : ℝ)
        (∑ r ∈ Finset.Ico (prefixLen p.β B) (blockLen B), frobIP (Pt ω) (cEr r - Vb)) ha
        (by exact_mod_cast hLpos)
      rw [this]
      simp only [havg]
      ring
    have hU3 : |(p.h / (B : ℝ)) ^ 2 * CQ| = (p.h / B) ^ 2 * |CQ| := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hU4 : |(p.h / (B : ℝ)) ^ 2 * (blockLen B : ℝ) ^ 2 * Wv| ≤
        (p.h / B) ^ 2 * (blockLen B : ℝ) ^ 2 * CV ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (blk_frobIP_le _ _).trans ?_
      calc fro Vb * fro (wfg f g S.C Vb) ≤ fro Vb * fro Vb :=
            mul_le_mul_of_nonneg_left (blk_wfg_fro_le f g SP hf' hg' _) (blk_fro_nn _)
        _ ≤ CV * CV := mul_le_mul hVbn hVbn (blk_fro_nn _) hCV
        _ = CV ^ 2 := by ring
    have hU5 : |-2 * (p.h / (B : ℝ)) * (blockLen B : ℝ) *
        (frobIP (wfg f g S.C D) Vb - (Real.sqrt (riskSigma S.C D))⁻¹ * Aω)| ≤
        2 * (p.h / B) * (blockLen B : ℝ) * RA * e1 := by
      have hdr := hDR (b * blockLen B) D hωA hωδ
      have hfD : fro D * e1 ≤ RA * e1 := mul_le_mul_of_nonneg_right (hAfro D hωA) he1
      rw [abs_mul, show |-2 * (p.h / (B : ℝ)) * (blockLen B : ℝ)| =
        2 * (p.h / B) * (blockLen B : ℝ) by
          rw [abs_of_nonpos (by have : 0 ≤ p.h / (B : ℝ) * (blockLen B : ℝ) := by positivity
                                nlinarith)]
          ring]
      calc _ ≤ 2 * (p.h / B) * (blockLen B : ℝ) * (fro D * e1) :=
            mul_le_mul_of_nonneg_left hdr (by positivity)
        _ ≤ 2 * (p.h / B) * (blockLen B : ℝ) * (RA * e1) :=
            mul_le_mul_of_nonneg_left hfD (by positivity)
        _ = _ := by ring
    have hU6 : |p.h ^ 2 * (blockLen B : ℝ) / (B : ℝ) * (FLs - Zω)| ≤
        p.h ^ 2 * blockLen B / B * e2 := by
      have hfr := hFR D hωA hωδ
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_left hfr (by positivity)
    rw [hlam]
    refine (blk_tri6 _ _ _ _ _ _).trans ?_
    rw [hU2, hU3]
    simp only [hGdef]
    linarith [hU1, hU4, hU5, hU6]
  -- integrals of the three conditional-expectation pieces
  have hselfadj : ∀ X Y : Mat m n, frobIP (blkW f g S.C X) Y = frobIP X (blkW f g S.C Y) :=
    fun X Y => block_wfg_self_adjoint f g S.C X Y
  have hcontr : ∀ X : Mat m n, fro (blkW f g S.C X) ≤ fro X := fun X =>
    blk_wfg_fro_le f g SP hf' hg' X
  have hCE : ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Z1 ω| ∂P ≤
      |K1| * (prefixLen p.β B : ℝ) ^ 2 :=
    (hK1 Ω P m n B S (blkW f g S.C) (fun X => by rw [one_mul]; exact hcontr X) (b * blockLen B)
      hB1 hqt Pt I hI hIτ hIPt).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg _))
  have hCQ : ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Zq ω| ∂P ≤
      (blockLen B : ℝ) * B * K3 * Cb * blkRbar B :=
    hK3b Ω P m n B S (blkW f g S.C) hselfadj hcontr (b * blockLen B) hB3 hBpos I hI hIτ hIA
  obtain ⟨hAvgInt, hAvgBd⟩ := hK2 Ω P m n B S (b * blockLen B) Pt hB2 hqt hPtf hPtm
  set E : Set Ω := {ω | ((b * blockLen B : ℕ) : ℕ∞) < tauPlus p S ω ∧
    diffuseness S.C (dynDelta S (b * blockLen B) ω) ≤ δ B} with hEdef
  have hEm : MeasurableSet E := by
    refine (block_past_le S _ _ (blk_tauPlus_meas S _)).inter ?_
    exact measurableSet_le ((blk_diffuseness_meas S.C).comp
      ((block_delta_meas S _).mono (block_past_le S _) le_rfl)) measurable_const
  have hIE : ∀ ω ∈ I, ω ∈ E := fun ω hω => ⟨hIτ ω hω, hIδ ω hω⟩
  have hAvgE : IntegrableOn (fun ω => |avg ω|) E P := (integrable_indicator_iff hEm).1 hAvgInt
  have hAvgI : ∫ ω in I, |avg ω| ∂P ≤ responseRho p K2 RA δ B := by
    have h1 : ∫ ω in I, |avg ω| ∂P ≤ ∫ ω in E, |avg ω| ∂P :=
      setIntegral_mono_set hAvgE (Eventually.of_forall fun ω => abs_nonneg _)
        (Eventually.of_forall fun ω hω => hIE ω hω)
    refine h1.trans ?_
    rw [← integral_indicator hEm]
    exact hAvgBd
  -- assembly of the integral of `G` over `I`
  have hμI : P.real I ≤ 1 := measureReal_le_one
  have hμI0 : 0 ≤ P.real I := measureReal_nonneg
  have hBr : (0 : ℝ) < B := by exact_mod_cast hBpos
  have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hLpos
  set c1 : ℝ := 2 * p.h / B with hc1
  set c3 : ℝ := 2 * p.h * blockLen B / B with hc3
  set c4 : ℝ := (p.h / B) ^ 2 with hc4
  set K : ℝ := 2 * p.h / B * (prefixLen p.β B : ℝ) * RA * CV + (p.h / B) ^ 2 * (blockLen B : ℝ) ^ 2 * CV ^ 2 +
    2 * (p.h / B) * (blockLen B : ℝ) * RA * e1 + p.h ^ 2 * blockLen B / B * e2 with hK
  have hc1' : 0 ≤ c1 := by have := p.hh; positivity
  have hc3' : 0 ≤ c3 := by have := p.hh; positivity
  have hc4' : 0 ≤ c4 := by positivity
  have hK' : 0 ≤ K := by
    have := p.hh
    have hq0' : (0 : ℝ) ≤ (prefixLen p.β B : ℝ) := Nat.cast_nonneg _
    simp only [hK]; positivity
  have hGeq : G = fun ω => c1 * |condExp (dynPast S (b * blockLen B)) P Z1 ω| + c3 * |avg ω| +
      c4 * |condExp (dynPast S (b * blockLen B)) P Zq ω| + K := by
    funext ω; simp only [hGdef, hc1, hc3, hc4, hK]; ring
  have hIntA : Integrable (fun ω => |condExp (dynPast S (b * blockLen B)) P Z1 ω|) P :=
    integrable_condExp.abs
  have hIntC : Integrable (fun ω => |condExp (dynPast S (b * blockLen B)) P Zq ω|) P :=
    integrable_condExp.abs
  have i1 : IntegrableOn (fun ω => c1 * |condExp (dynPast S (b * blockLen B)) P Z1 ω|) I P :=
    (hIntA.integrableOn).const_mul _
  have i2 : IntegrableOn (fun ω => c3 * |avg ω|) I P :=
    (hAvgE.mono_set (fun ω hω => hIE ω hω)).const_mul _
  have i3 : IntegrableOn (fun ω => c4 * |condExp (dynPast S (b * blockLen B)) P Zq ω|) I P :=
    (hIntC.integrableOn).const_mul _
  have iK : IntegrableOn (fun _ : Ω => K) I P := integrableOn_const (by simp)
  have hGI : IntegrableOn G I P := by rw [hGeq]; exact ((i1.add i2).add i3).add iK
  have hGval : ∫ ω in I, G ω ∂P ≤ (blockLen B : ℝ) / B * (2 * p.h * |K1| * (prefixLen p.β B : ℝ) ^ 2 / (blockLen B : ℝ) +
              2 * p.h * (prefixLen p.β B : ℝ) * Real.sqrt (p.Estar + 1) * CV / (blockLen B : ℝ) +
              2 * p.h * responseRho p K2 (Real.sqrt (p.Estar + 1)) δ B +
              p.h ^ 2 * K3 * Cb * blkRbar B + p.h ^ 2 * (blockLen B : ℝ) * CV ^ 2 / B +
              2 * p.h * Real.sqrt (p.Estar + 1) * e1 + p.h ^ 2 * e2) := by
    rw [hGeq]
    have e : ∫ ω in I, (c1 * |condExp (dynPast S (b * blockLen B)) P Z1 ω| + c3 * |avg ω| +
        c4 * |condExp (dynPast S (b * blockLen B)) P Zq ω| + K) ∂P =
        c1 * ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Z1 ω| ∂P + c3 * ∫ ω in I, |avg ω| ∂P +
          c4 * ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Zq ω| ∂P + K * P.real I := by
      have i12 : IntegrableOn (fun ω => c1 * |condExp (dynPast S (b * blockLen B)) P Z1 ω| +
          c3 * |avg ω|) I P := i1.add i2
      have i123 : IntegrableOn (fun ω => c1 * |condExp (dynPast S (b * blockLen B)) P Z1 ω| +
          c3 * |avg ω| + c4 * |condExp (dynPast S (b * blockLen B)) P Zq ω|) I P := i12.add i3
      rw [integral_add i123 iK, integral_add i12 i3, integral_add i1 i2,
        integral_const_mul, integral_const_mul, integral_const_mul, setIntegral_const]
      simp only [smul_eq_mul]
      ring
    rw [e]
    have b1 : c1 * ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Z1 ω| ∂P ≤
        c1 * (|K1| * (prefixLen p.β B : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hCE hc1'
    have b3 : c3 * ∫ ω in I, |avg ω| ∂P ≤ c3 * responseRho p K2 RA δ B :=
      mul_le_mul_of_nonneg_left hAvgI hc3'
    have b4 : c4 * ∫ ω in I, |condExp (dynPast S (b * blockLen B)) P Zq ω| ∂P ≤
        c4 * ((blockLen B : ℝ) * B * K3 * Cb * blkRbar B) := mul_le_mul_of_nonneg_left hCQ hc4'
    have b5 : K * P.real I ≤ K := mul_le_of_le_one_right hK' hμI
    have key : c1 * (|K1| * (prefixLen p.β B : ℝ) ^ 2) + c3 * responseRho p K2 RA δ B +
        c4 * ((blockLen B : ℝ) * B * K3 * Cb * blkRbar B) + K =
        (blockLen B : ℝ) / B * (2 * p.h * |K1| * (prefixLen p.β B : ℝ) ^ 2 / (blockLen B : ℝ) +
              2 * p.h * (prefixLen p.β B : ℝ) * Real.sqrt (p.Estar + 1) * CV / (blockLen B : ℝ) +
              2 * p.h * responseRho p K2 (Real.sqrt (p.Estar + 1)) δ B +
              p.h ^ 2 * K3 * Cb * blkRbar B + p.h ^ 2 * (blockLen B : ℝ) * CV ^ 2 / B +
              2 * p.h * Real.sqrt (p.Estar + 1) * e1 + p.h ^ 2 * e2) := by
      simp only [hc1, hc3, hc4, hK, hRA]
      field_simp
      ring
    linarith
  have hLam_aesm : AEStronglyMeasurable (fun ω => blkLam S SP c f g b ω) P := by
    unfold blkLam
    have h1 : AEStronglyMeasurable (condExp (dynPast S (b * blockLen B)) P (blockIncr p f g S b)) P :=
      (stronglyMeasurable_condExp.mono (block_past_le S _)).aestronglyMeasurable
    have h2 : Measurable (fun ω => blkF p SP c f g (fun t => dynDelta S t ω) (b * blockLen B)) :=
      (blk_fieldOp_meas p SP c (tensorFG f g)).comp
        ((block_delta_meas S _).mono (block_past_le S _) le_rfl)
    exact h1.sub (h2.const_mul _).aestronglyMeasurable
  have hΦeq : (fun ω => (if b < bs ω then (1 : ℝ) else 0) * |blkLam S SP c f g b ω|) =
      I.indicator (fun ω => |blkLam S SP c f g b ω|) := by
    funext ω
    by_cases h : ω ∈ I
    · have h' : b < bs ω := h
      simp [Set.indicator_of_mem h, h']
    · have h' : ¬ b < bs ω := h
      simp [Set.indicator_of_notMem h, h']
  rw [hΦeq]
  have hIndG : Integrable (I.indicator G) P := (integrable_indicator_iff hIm).2 hGI
  have hAbs : AEStronglyMeasurable (fun ω => |blkLam S SP c f g b ω|) P :=
    continuous_abs.comp_aestronglyMeasurable hLam_aesm
  have hle : ∀ᵐ ω ∂P, I.indicator (fun ω => |blkLam S SP c f g b ω|) ω ≤ I.indicator G ω := by
    filter_upwards [hpoint] with ω hω
    by_cases h : ω ∈ I
    · simp only [Set.indicator_of_mem h]; exact hω h
    · simp [Set.indicator_of_notMem h]
  refine ⟨hIndG.mono' (hAbs.indicator hIm) ?_, ?_⟩
  · filter_upwards [hle] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Set.indicator_nonneg (fun _ _ => abs_nonneg _) _)]
    exact hω
  · calc ∫ ω, I.indicator (fun ω => |blkLam S SP c f g b ω|) ω ∂P ≤ ∫ ω, I.indicator G ω ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω =>
            Set.indicator_nonneg (fun _ _ => abs_nonneg _) _) hIndG hle
      _ = ∫ ω in I, G ω ∂P := integral_indicator hIm
      _ ≤ _ := hGval

/-- `V = B^{1/64}`. -/
private def blkV (B : ℕ) : ℝ := (B : ℝ) ^ ((1 : ℝ) / 64)

private lemma blkV_tendsto : Tendsto blkV atTop atTop := by
  unfold blkV
  exact (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

private lemma blkV_pos (B : ℕ) (hB : 0 < B) : 0 < blkV B := by
  unfold blkV; positivity

private lemma blkV_pow64 (B : ℕ) : blkV B ^ 64 = (B : ℝ) := by
  unfold blkV
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg B)]
  norm_num

private lemma blockLen_le_V (B : ℕ) : (blockLen B : ℝ) ≤ blkV B ^ 8 := by
  have h : blkV B ^ 8 = (B : ℝ) ^ ((1 : ℝ) / 8) := by
    unfold blkV
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg B)]
    norm_num
  rw [h]
  exact Nat.floor_le (by positivity)

private lemma V_pow8_le_blockLen_add_one (B : ℕ) : blkV B ^ 8 ≤ (blockLen B : ℝ) + 1 := by
  have h : blkV B ^ 8 = (B : ℝ) ^ ((1 : ℝ) / 8) := by
    unfold blkV
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg B)]
    norm_num
  rw [h]
  exact (Nat.lt_floor_add_one _).le

private lemma blockLen_tendsto : Tendsto (fun B : ℕ => (blockLen B : ℝ)) atTop atTop := by
  refine tendsto_atTop_mono (fun B => ?_)
    (tendsto_atTop_add_const_right atTop (-1 : ℝ) ((tendsto_pow_atTop (by norm_num : (8 : ℕ) ≠ 0)).comp blkV_tendsto))
  have := V_pow8_le_blockLen_add_one B
  simp only [Function.comp]
  linarith

private lemma log_le_V (B : ℕ) (hB : 1 ≤ B) : Real.log (2 * (B : ℝ)) ≤ 128 * blkV B := by
  have h := Real.log_le_rpow_div (x := 2 * (B : ℝ)) (ε := 1 / 64) (by positivity) (by norm_num)
  have h2 : (2 * (B : ℝ)) ^ ((1 : ℝ) / 64) = 2 ^ ((1 : ℝ) / 64) * blkV B := by
    rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg B)]; rfl
  have h3 : (2 : ℝ) ^ ((1 : ℝ) / 64) ≤ 2 := by
    calc (2 : ℝ) ^ ((1 : ℝ) / 64) ≤ 2 ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      _ = 2 := by simp
  rw [h2] at h
  have hV : 0 ≤ blkV B := by unfold blkV; positivity
  calc Real.log (2 * (B : ℝ)) ≤ 2 ^ ((1 : ℝ) / 64) * blkV B / (1 / 64) := h
    _ ≤ 2 * blkV B / (1 / 64) := by gcongr
    _ = 128 * blkV B := by ring


private lemma blkV_ge_one (B : ℕ) (hB : 1 ≤ B) : 1 ≤ blkV B := by
  unfold blkV
  exact Real.one_le_rpow (by exact_mod_cast hB) (by norm_num)

private lemma sqrt_B_eq (B : ℕ) : Real.sqrt (B : ℝ) = blkV B ^ 32 := by
  rw [← blkV_pow64 B, show blkV B ^ 64 = (blkV B ^ 32) ^ 2 by ring]
  exact Real.sqrt_sq (by have : 0 ≤ blkV B := by unfold blkV; positivity
                         positivity)

private lemma tendsto_zero_of_le_inv_pow (g : ℕ → ℝ) (c : ℝ) (k : ℕ) (hk : k ≠ 0)
    (hnn : ∀ B, 0 ≤ g B) (hle : ∀ᶠ B in atTop, g B ≤ c * (blkV B ^ k)⁻¹) :
    Tendsto g atTop (𝓝 0) := by
  have hlim : Tendsto (fun B : ℕ => c * (blkV B ^ k)⁻¹) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop hk).comp blkV_tendsto)
    simpa using (tendsto_inv_atTop_zero.comp this).const_mul c
  exact squeeze_zero' (Eventually.of_forall hnn) hle hlim


private lemma asy_nu (c : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun B : ℕ => c * (blockLen B : ℝ) / Real.sqrt (B : ℝ)) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ c 24 (by norm_num) (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hV := blkV_ge_one B hB
  have hL := blockLen_le_V B
  rw [sqrt_B_eq]
  have hV0 : 0 < blkV B := by linarith
  rw [mul_div_assoc, show blkV B ^ 24 = blkV B ^ 32 / blkV B ^ 8 by
    rw [eq_div_iff (by positivity)]; ring]
  rw [inv_div]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ blkV B ^ 32 := by positivity
  nlinarith

private lemma asy_LB : Tendsto (fun B : ℕ => (blockLen B : ℝ) / (B : ℝ)) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ 1 56 (by norm_num) (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hV := blkV_ge_one B hB
  have hL := blockLen_le_V B
  rw [← blkV_pow64 B, one_mul, show blkV B ^ 56 = blkV B ^ 64 / blkV B ^ 8 by
    rw [eq_div_iff (by positivity)]; ring, inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ blkV B ^ 64 := by positivity
  nlinarith

private lemma asy_Lpow_B (k : ℕ) (hk : 1 ≤ k) (hk8 : k ≤ 7) :
    Tendsto (fun B : ℕ => (blockLen B : ℝ) ^ k / (B : ℝ)) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ 1 (64 - 8 * k) (by omega) (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hV := blkV_ge_one B hB
  have hL := blockLen_le_V B
  have hL0 : (0 : ℝ) ≤ blockLen B := Nat.cast_nonneg _
  rw [← blkV_pow64 B, one_mul]
  have e : blkV B ^ (64 - 8 * k) = blkV B ^ 64 / (blkV B ^ 8) ^ k := by
    rw [eq_div_iff (by positivity), ← pow_mul, ← pow_add]
    congr 1; omega
  rw [e, inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ blkV B ^ 64 := by positivity
  have h2 : (blockLen B : ℝ) ^ k ≤ (blkV B ^ 8) ^ k := pow_le_pow_left₀ hL0 hL k
  nlinarith

private lemma asy_inv_sqrt : Tendsto (fun B : ℕ => 1 / Real.sqrt (B : ℝ)) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ 1 32 (by norm_num) (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  rw [sqrt_B_eq]; simp

private lemma asy_inv_L : Tendsto (fun B : ℕ => 1 / (blockLen B : ℝ)) atTop (𝓝 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp blockLen_tendsto

private lemma asy_L32 : Tendsto (fun B : ℕ => (blockLen B : ℝ) ^ ((3 : ℝ) / 2) / Real.sqrt (B : ℝ)) atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ 1 20 (by norm_num) (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hV := blkV_ge_one B hB
  have hL := blockLen_le_V B
  have hL0 : (0 : ℝ) ≤ blockLen B := Nat.cast_nonneg _
  rw [sqrt_B_eq, one_mul]
  have h1 : (blockLen B : ℝ) ^ ((3 : ℝ) / 2) ≤ blkV B ^ 12 := by
    calc (blockLen B : ℝ) ^ ((3 : ℝ) / 2) ≤ (blkV B ^ 8) ^ ((3 : ℝ) / 2) :=
          Real.rpow_le_rpow hL0 hL (by norm_num)
      _ = blkV B ^ 12 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
  rw [show blkV B ^ 20 = blkV B ^ 32 / blkV B ^ 12 by
    rw [eq_div_iff (by positivity)]; ring, inv_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 ≤ blkV B ^ 32 := by positivity
  nlinarith

private lemma asy_logterm : Tendsto (fun B : ℕ => (blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ))
    atTop (𝓝 0) := by
  refine tendsto_zero_of_le_inv_pow _ (128 ^ 2) 54 (by norm_num)
    (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1] with B hB
  have hV := blkV_ge_one B hB
  have hL := blockLen_le_V B
  have hL0 : (0 : ℝ) ≤ blockLen B := Nat.cast_nonneg _
  have hlog := log_le_V B hB
  have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith)
  have h2 : Real.log (2 * (B : ℝ)) ^ 2 ≤ (128 * blkV B) ^ 2 := pow_le_pow_left₀ hlog0 hlog 2
  have hB' : (B : ℝ) = blkV B ^ 64 := (blkV_pow64 B).symm
  have hVpos : 0 < blkV B := by linarith
  calc (blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ)
      ≤ (blkV B ^ 8 * (128 * blkV B) ^ 2) / (B : ℝ) := by
        gcongr
    _ = 128 ^ 2 * (blkV B ^ 54)⁻¹ := by
        rw [hB']; field_simp


private lemma C0_ge_one (β : ℝ) : 1 ≤ C0 β := by
  unfold C0
  split_ifs
  · exact le_rfl
  · exact le_max_left _ _

private lemma prefixLen_le_V (β : ℝ) (B : ℕ) (hB : 1 ≤ B) :
    (prefixLen β B : ℝ) ≤ 128 * C0 β * blkV B + 1 := by
  have hlog := log_le_V B hB
  have hC0 := C0_ge_one β
  have hlog0 : 0 ≤ Real.log (2 * (B : ℝ)) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB
    linarith)
  have h1 : (prefixLen β B : ℝ) < C0 β * Real.log (2 * (B : ℝ)) + 1 :=
    Nat.ceil_lt_add_one (by positivity)
  have h2 : C0 β * Real.log (2 * (B : ℝ)) ≤ C0 β * (128 * blkV B) :=
    mul_le_mul_of_nonneg_left hlog (by linarith)
  nlinarith

private lemma prefixLen_le_blockLen (β : ℝ) : ∀ᶠ B : ℕ in atTop, prefixLen β B ≤ blockLen B := by
  have hC0 := C0_ge_one β
  filter_upwards [blkV_tendsto.eventually_ge_atTop (128 * C0 β + 3), eventually_ge_atTop 1] with B hV hB
  have h1 := prefixLen_le_V β B hB
  have h2 := V_pow8_le_blockLen_add_one B
  have hV1 : 1 ≤ blkV B := by linarith
  have h3 : blkV B ^ 2 ≤ blkV B ^ 8 := pow_le_pow_right₀ hV1 (by norm_num)
  have h4 : (128 * C0 β + 3) * blkV B ≤ blkV B ^ 2 := by nlinarith
  have : (prefixLen β B : ℝ) ≤ blockLen B := by nlinarith
  exact_mod_cast this

private lemma asy_q_div_L (β : ℝ) :
    Tendsto (fun B : ℕ => (prefixLen β B : ℝ) / (blockLen B : ℝ)) atTop (𝓝 0) := by
  have hC0 := C0_ge_one β
  refine tendsto_zero_of_le_inv_pow _ (2 * (128 * C0 β + 1)) 7 (by norm_num)
    (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1, blkV_tendsto.eventually_ge_atTop 2] with B hB hV
  have h1 := prefixLen_le_V β B hB
  have h2 := V_pow8_le_blockLen_add_one B
  have hV1 : 1 ≤ blkV B := by linarith
  have h8 : 2 ≤ blkV B ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hV 8, pow_le_pow_right₀ hV1 (by norm_num : 1 ≤ 8)]
  have hL : blkV B ^ 8 / 2 ≤ (blockLen B : ℝ) := by linarith
  have hLpos : 0 < (blockLen B : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ prefixLen β B := Nat.cast_nonneg _
  rw [div_le_iff₀ hLpos]
  have : (prefixLen β B : ℝ) ≤ (128 * C0 β + 1) * blkV B := by nlinarith
  calc (prefixLen β B : ℝ) ≤ (128 * C0 β + 1) * blkV B := this
    _ = 2 * (128 * C0 β + 1) * (blkV B ^ 7)⁻¹ * (blkV B ^ 8 / 2) := by
        field_simp
    _ ≤ _ := by gcongr

private lemma asy_q2_div_L (β : ℝ) :
    Tendsto (fun B : ℕ => (prefixLen β B : ℝ) ^ 2 / (blockLen B : ℝ)) atTop (𝓝 0) := by
  have hC0 := C0_ge_one β
  refine tendsto_zero_of_le_inv_pow _ (2 * (128 * C0 β + 1) ^ 2) 6 (by norm_num)
    (fun B => by positivity) ?_
  filter_upwards [eventually_ge_atTop 1, blkV_tendsto.eventually_ge_atTop 2] with B hB hV
  have h1 := prefixLen_le_V β B hB
  have h2 := V_pow8_le_blockLen_add_one B
  have hV1 : 1 ≤ blkV B := by linarith
  have h8 : 2 ≤ blkV B ^ 8 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hV 8, pow_le_pow_right₀ hV1 (by norm_num : 1 ≤ 8)]
  have hL : blkV B ^ 8 / 2 ≤ (blockLen B : ℝ) := by linarith
  have hLpos : 0 < (blockLen B : ℝ) := by linarith
  have hq0 : (0 : ℝ) ≤ prefixLen β B := Nat.cast_nonneg _
  rw [div_le_iff₀ hLpos]
  have h3 : (prefixLen β B : ℝ) ≤ (128 * C0 β + 1) * blkV B := by nlinarith
  have h4 : (prefixLen β B : ℝ) ^ 2 ≤ ((128 * C0 β + 1) * blkV B) ^ 2 := pow_le_pow_left₀ hq0 h3 2
  calc (prefixLen β B : ℝ) ^ 2 ≤ ((128 * C0 β + 1) * blkV B) ^ 2 := h4
    _ = 2 * (128 * C0 β + 1) ^ 2 * (blkV B ^ 6)⁻¹ * (blkV B ^ 8 / 2) := by
        field_simp
    _ ≤ _ := by gcongr


private lemma asy_inv_B : Tendsto (fun B : ℕ => 1 / (B : ℝ)) atTop (𝓝 0) := by
  simp only [one_div]
  exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private lemma blockLen_tendsto_nat : Tendsto (fun B : ℕ => blockLen B) atTop atTop :=
  tendsto_natCast_atTop_iff.mp blockLen_tendsto

private lemma asy_TVL_aux (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Tendsto (fun B : ℕ => β ^ blockLen B / (1 - β) + β / ((blockLen B : ℝ) * (1 - β) ^ 2)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun B : ℕ => β ^ blockLen B) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).comp blockLen_tendsto_nat
  have h2 : Tendsto (fun B : ℕ => β ^ blockLen B / (1 - β)) atTop (𝓝 0) := by
    simpa using h1.div_const (1 - β)
  have h3 : Tendsto (fun B : ℕ => β / (1 - β) ^ 2 * (1 / (blockLen B : ℝ))) atTop (𝓝 0) := by
    simpa using asy_inv_L.const_mul (β / (1 - β) ^ 2)
  have h4 : (fun B : ℕ => β / ((blockLen B : ℝ) * (1 - β) ^ 2)) =
      fun B : ℕ => β / (1 - β) ^ 2 * (1 / (blockLen B : ℝ)) := by
    funext B
    by_cases h : (blockLen B : ℝ) = 0
    · simp [h]
    · field_simp
  have h5 := h2.add h3
  rw [add_zero] at h5
  refine h5.congr fun B => ?_
  rw [congrFun h4 B]

/-- Recast a setup to a covariance `C` equal to its own (so that `.C` is literally `C`). -/
private def blkRecast {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}
    (S : DynSetup p P m n B) (C : Covariances m n) (hC : S.C = C) : DynSetup p P m n B :=
  { S with C := C, size := hC ▸ S.size, W0_risk := hC ▸ S.W0_risk }

private lemma blkRecast_batch {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    {m n B : ℕ} (S : DynSetup p P m n B) (C : Covariances m n) (hC : S.C = C) (u : ℕ) :
    dynBatch (blkRecast S C hC) u = dynBatch S u := by
  funext ω
  simp only [dynBatch, blkRecast]
  rw [hC]

private lemma blk_finInt_add (a b : (ℝ × ℝ) →₀ ℝ) (φ : ℝ × ℝ → ℝ) :
    Muon.Volatility.finInt (a + b) φ = Muon.Volatility.finInt a φ + Muon.Volatility.finInt b φ := by
  unfold Muon.Volatility.finInt
  exact Finsupp.sum_add_index' (fun _ => by ring) (fun _ _ _ => by ring)

private lemma blk_finInt_single (x : ℝ × ℝ) (v : ℝ) (φ : ℝ × ℝ → ℝ) :
    Muon.Volatility.finInt (Finsupp.single x v) φ = v * φ x := by
  unfold Muon.Volatility.finInt
  exact Finsupp.sum_single_index (by ring)

private lemma blk_finInt_sum_single {m n : ℕ} (pts : Fin m → Fin n → ℝ × ℝ) (w : Fin m → Fin n → ℝ)
    (φ : ℝ × ℝ → ℝ) :
    Muon.Volatility.finInt (∑ i : Fin m, ∑ j : Fin n, Finsupp.single (pts i j) (w i j)) φ =
      ∑ i, ∑ j, w i j * φ (pts i j) := by
  have hzero : Muon.Volatility.finInt (0 : (ℝ × ℝ) →₀ ℝ) φ = 0 := by
    unfold Muon.Volatility.finInt; simp
  have hsum : ∀ (s : Finset (Fin n)) (g : Fin n → (ℝ × ℝ) →₀ ℝ),
      Muon.Volatility.finInt (∑ j ∈ s, g j) φ = ∑ j ∈ s, Muon.Volatility.finInt (g j) φ := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, blk_finInt_add, ih]
  have hsum' : ∀ (s : Finset (Fin m)) (g : Fin m → (ℝ × ℝ) →₀ ℝ),
      Muon.Volatility.finInt (∑ i ∈ s, g i) φ = ∑ i ∈ s, Muon.Volatility.finInt (g i) φ := by
    intro s g
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, blk_finInt_add, ih]
  rw [hsum']
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hsum]
  exact Finset.sum_congr rfl fun j _ => blk_finInt_single _ _ _

private lemma blk_Vbar_eq {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {p : DynParams} {m n B : ℕ} (S : DynSetup p P' m n B) (F : FrozenParams m n B)
    (hFC : F.C = S.C) (hFβ : F.β = p.β) (S0 : FrozenSamples P' m n B) (t : ℕ) (D : Mat m n)
    (hD : 0 < riskSigma S.C D) (hFA : F.A = Ahat S.C D) :
    dynVbar p S t D = Muon.mean P' (fun ω => frozenUpd F S0 p.ϱ 0 ω) := by
  have hch := (lem_app_dyn_chains_i (P := P') (P' := P') p S.C S.cs t D 0 hD F hFC hFA hFβ S0).2.2.2.2
  have hshift := block_upd_mean_shift F S0 p.ϱ p.hϱ.le (t : ℤ)
  have e : dynVbar p S t D = Muon.mean P' (fun ω => (def_app_dyn_chains p S.C S.cs t D 0 ω).statV 1) := rfl
  rw [e, hch]
  exact hshift

private lemma blk_frozen_ext {m n B : ℕ} (F1 F2 : FrozenParams m n B) (hC : F1.C = F2.C)
    (hA : F1.A = F2.A) (hβ : F1.β = F2.β) : F1 = F2 := by
  cases F1; cases F2
  simp only at hC hA hβ
  subst hC hA hβ
  rfl

/-- The forcing measure `𝔉_L(D)` at the normalized state `Â(D)`. -/
private def blkFL {m n B : ℕ → ℕ} (p : DynParams) (F : ∀ k, FrozenParams (m k) (n k) (B k))
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] {P' : ∀ k, Measure (Ω' k)}
    (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k)) (SD : ∀ k, SpectralData (F k).C) (k : ℕ)
    (D : Mat (m k) (n k)) : (ℝ × ℝ) →₀ ℝ :=
  if h : 0 < riskSigma (F k).C D then
    Muon.Volatility.finiteTimeMeasure (withState (F k) (Ahat (F k).C D) (block_Ahat_norm _ _ h))
      (S0 k) (SD k) (blockLen (B k)) p.ϱ
  else 0

private lemma blk_hFL {m n B : ℕ → ℕ} (p : DynParams) (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] {P' : ∀ k, Measure (Ω' k)}
    (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k)) (SD : ∀ k, SpectralData (F k).C) (k : ℕ) :
    ∀ (D : Mat (m k) (n k)) (Fz : FrozenParams (m k) (n k) (B k)) (hC : Fz.C = (F k).C),
      Fz.A = Ahat (F k).C D → 0 < riskSigma (F k).C D → Fz.β = p.β →
        blkFL p F S0 SD k D =
          Muon.Volatility.finiteTimeMeasure Fz (S0 k) (hC ▸ SD k) (blockLen (B k)) p.ϱ := by
  intro D Fz hC hA hR hb
  have hext : Fz = withState (F k) (Ahat (F k).C D) (block_Ahat_norm _ _ hR) :=
    blk_frozen_ext _ _ hC hA (hb.trans (hβ k).symm)
  subst hext
  unfold blkFL
  rw [dif_pos hR]

section blkstate

variable {p : DynParams} {m n B : ℕ → ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}

private lemma blk_normState_mem {m n : ℕ} {C : Covariances m n} {D : Mat m n} (hR : 0 < riskSigma C D) :
    Ahat C D ∈ NormStates C := ⟨D, hR, rfl⟩

private lemma blk_hVb_state (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (k0 : ℕ) (D : Mat (m k0) (n k0)) (hR : 0 < riskSigma (F k0).C D)
    (d η1 : ℝ) (hd : diffuseness (F k0).C D ≤ d)
    (he1 : ∀ A ∈ NormStates (F k0).C, opNorm A ≤ d → blkE1 p F S0 k0 A ≤ η1) :
    fro (Muon.mean (P' k0) (fun ω => frozenUpd (withState (F k0) (Ahat (F k0).C D)
      (block_Ahat_norm _ _ hR)) (S0 k0) p.ϱ 0 ω)) ≤ p.CSig / Real.sqrt p.ϱ + η1 := by
  have h := (blk_drift_state F hyp hβ P' S0 SD k0 D hR (fun _ => 0) (fun _ => 0)
    (fun x => by simp) (fun x => by simp)).2
  have h2 := he1 (Ahat (F k0).C D) (blk_normState_mem hR) hd
  linarith

private lemma blk_hDR_state (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (c : ∀ k, DynCoeff p (SD k) (B k)) (cert : Muon.External.GaussianOpNorm)
    (hc : ∀ k, IsActualCoeff cert (F k) (SD k) (c k))
    (k0 : ℕ) (D : Mat (m k0) (n k0)) (hR : 0 < riskSigma (F k0).C D)
    (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (d η1 : ℝ) (hd : diffuseness (F k0).C D ≤ d)
    (he1 : ∀ A ∈ NormStates (F k0).C, opNorm A ≤ d → blkE1 p F S0 k0 A ≤ η1) :
    |frobIP (wfg f g (F k0).C D) (Muon.mean (P' k0) (fun ω => frozenUpd (withState (F k0)
        (Ahat (F k0).C D) (block_Ahat_norm _ _ hR)) (S0 k0) p.ϱ 0 ω)) -
      (Real.sqrt (riskSigma (F k0).C D))⁻¹ * ∑ i, ∑ j, modeQ (SD k0) D i j *
        (tensorFG f g ((SD k0).μ i, (SD k0).lam j) * (c k0).d ((SD k0).μ i, (SD k0).lam j))| ≤
      fro D * η1 := by
  have h := (blk_drift_state F hyp hβ P' S0 SD k0 D hR f g hf hg).1
  have h2 := he1 (Ahat (F k0).C D) (blk_normState_mem hR) hd
  obtain ⟨hμ, hl⟩ := blk_spec_mem (SD k0) p.CSig (hyp.normBd k0).2 (hyp.normBd k0).1
  have hcd : ∀ i j, (c k0).d ((SD k0).μ i, (SD k0).lam j) =
      Muon.Drift.kernel (emaW p.β) (Muon.Drift.specOutFM (F k0)) (Muon.Drift.specInFM (F k0)) p.ϱ
        ((SD k0).μ i) ((SD k0).lam j) := fun i j => (hc k0).2.1 _ ⟨hμ i, hl j⟩
  simp only [hcd]
  refine h.trans ?_
  exact mul_le_mul_of_nonneg_left h2 (blk_fro_nn _)

private lemma blk_hFR_state (cert : Muon.External.GaussianOpNorm) (F : ∀ k, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C)) (hβ : ∀ k, (F k).β = p.β)
    {Ω' : ℕ → Type} [∀ k, MeasurableSpace (Ω' k)] (P' : ∀ k, Measure (Ω' k))
    [∀ k, IsProbabilityMeasure (P' k)] (S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k))
    (SD : ∀ k, SpectralData (F k).C) (c : ∀ k, DynCoeff p (SD k) (B k))
    (hc : ∀ k, IsActualCoeff cert (F k) (SD k) (c k))
    (k0 : ℕ) (D : Mat (m k0) (n k0)) (hR : 0 < riskSigma (F k0).C D)
    (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1) (hL : 1 ≤ blockLen (B k0))
    (hBpos : 0 < B k0)
    (d η2 : ℝ) (hd : diffuseness (F k0).C D ≤ d)
    (he2 : ∀ A ∈ NormStates (F k0).C, opNorm A ≤ d → blkE2 cert p F S0 SD f g k0 A ≤ η2) :
    |(blkFL p F S0 SD k0 D).sum (fun x r => f x.1 * g x.2 * r) -
      ∑ i, ∑ j, ((c k0).v i j / (B k0 : ℝ)) * tensorFG f g ((SD k0).μ i, (SD k0).lam j)| ≤
      blkTVL p (blockLen (B k0)) + η2 := by
  have h := blk_forcing_state cert F hyp hβ P' S0 SD k0 D hR f g hf hg hL
  have h2 := he2 (Ahat (F k0).C D) (blk_normState_mem hR) hd
  have hZ : Muon.Volatility.finInt (Muon.Volatility.measureZeta cert p.γstar p.CSig (F k0) (SD k0) p.ϱ)
      (fun q => f q.1 * g q.2) =
      ∑ i, ∑ j, ((c k0).v i j / (B k0 : ℝ)) * tensorFG f g ((SD k0).μ i, (SD k0).lam j) := by
    have hS : Muon.Volatility.SizeFin (F k0).C (B k0) p.γstar p.CSig :=
      ⟨hyp.dims k0, (hyp.normBd k0).2, (hyp.normBd k0).1⟩
    have hdis := (Muon.Volatility.prop_app_vol_disintegration_i cert p.γstar p.CSig (F k0) (SD k0) hS
      p.hC p.ϱ p.hϱ).2.2.2
    rw [hdis, blk_finInt_sum_single]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [(hc k0).2.2.1 i j]
    simp only [tensorFG]
    rw [inv_mul_eq_div]
  have hFL : blkFL p F S0 SD k0 D = Muon.Volatility.finiteTimeMeasure (withState (F k0)
      (Ahat (F k0).C D) (block_Ahat_norm _ _ hR)) (S0 k0) (SD k0) (blockLen (B k0)) p.ϱ := by
    unfold blkFL; rw [dif_pos hR]
  rw [hFL, ← hZ]
  linarith

end blkstate

section blkbad

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {p : DynParams} {m n B : ℕ}

private lemma blk_notGd_sub (S : DynSetup p P m n B) (T d : ℝ) (hT : 0 ≤ T) (hL : 0 < blockLen B)
    (ω : Ω) (h : ¬ blkGd S T d ω) :
    ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime S ω ∧ (t : ℝ) ≤ T * (B : ℝ) ∧
      d < diffuseness S.C (dynDelta S t ω) := by
  unfold blkGd at h
  push Not at h
  obtain ⟨b, hbJ, hbA, hbd⟩ := h
  refine ⟨b * blockLen B, ?_, ?_, hbd⟩
  · have hb : (b : ℕ∞) ≤ dynBlockIndexExit S ω := by
      unfold dynBlockIndexExit
      refine le_iInf₂ fun b'' hb'' => ?_
      by_contra hcon
      have : b'' ≤ b := by
        have : (b'' : ℕ∞) < b := not_le.1 hcon
        exact_mod_cast this.le
      exact hb'' (hbA b'' this)
    unfold dynBlockExitTime
    have : ((b * blockLen B : ℕ) : ℕ∞) = (blockLen B : ℕ∞) * (b : ℕ∞) := by
      push_cast; ring
    rw [this]
    gcongr
  · have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hL
    have hb' : (b : ℝ) ≤ T * B / blockLen B := by
      have : b ≤ ⌊T * (B : ℝ) / (blockLen B : ℝ)⌋₊ := by
        have := hbJ; simp only [blkJ] at this; omega
      exact (Nat.cast_le.2 this).trans (Nat.floor_le (by positivity))
    push_cast
    rw [le_div_iff₀ hLr] at hb'
    exact hb'

end blkbad

private lemma asy_rbar : Tendsto (fun B : ℕ => blkRbar B) atTop (𝓝 0) := by
  have h1 := asy_inv_L
  have h2 := asy_inv_sqrt
  have h3 := asy_Lpow_B 2 (by norm_num) (by norm_num)
  have h4 := asy_L32
  have h5 := asy_nu 1 zero_le_one
  have h6 := asy_Lpow_B 3 (by norm_num) (by norm_num)
  have h := ((((h1.add h2).add h3).add h4).add h5).add h6
  simp only [add_zero] at h
  refine h.congr fun B => ?_
  unfold blkRbar
  simp only [one_mul]

private lemma asy_TVL (p : DynParams) : Tendsto (fun B : ℕ => blkTVL p (blockLen B)) atTop (𝓝 0) := by
  have := (asy_TVL_aux p.β p.hβ.1 p.hβ.2).const_mul (2 * kStar p.CSig p.γstar p.ϱ)
  simpa [blkTVL] using this

private lemma asy_Theta (p : DynParams) (Kp Kq Cb Kr RA CS η1 η2 : ℝ) (δ : ℕ → ℝ)
    (hρ : Tendsto (responseRho p Kr RA δ) atTop (𝓝 0)) :
    Tendsto (fun B : ℕ =>
      2 * p.h * Kp * (prefixLen p.β B : ℝ) ^ 2 / (blockLen B : ℝ) +
        2 * p.h * (prefixLen p.β B : ℝ) * RA * (CS + η1) / (blockLen B : ℝ) +
        2 * p.h * responseRho p Kr RA δ B + p.h ^ 2 * Kq * Cb * blkRbar B +
        p.h ^ 2 * (blockLen B : ℝ) * (CS + η1) ^ 2 / (B : ℝ) + 2 * p.h * RA * η1 +
        p.h ^ 2 * (blkTVL p (blockLen B) + η2)) atTop (𝓝 (2 * p.h * RA * η1 + p.h ^ 2 * η2)) := by
  have t1 := (asy_q2_div_L p.β).const_mul (2 * p.h * Kp)
  have t2 := (asy_q_div_L p.β).const_mul (2 * p.h * RA * (CS + η1))
  have t3 := hρ.const_mul (2 * p.h)
  have t4 := asy_rbar.const_mul (p.h ^ 2 * Kq * Cb)
  have t5 := asy_LB.const_mul (p.h ^ 2 * (CS + η1) ^ 2)
  have t7 := (asy_TVL p).add_const η2 |>.const_mul (p.h ^ 2)
  have := ((((((t1.add t2).add t3).add t4).add t5).add (tendsto_const_nhds (x := 2 * p.h * RA * η1))).add t7)
  simp only [mul_zero, zero_add, add_zero] at this
  refine this.congr fun B => ?_
  by_cases hL : (blockLen B : ℝ) = 0
  · simp [hL]
  · field_simp

private lemma asy_Edet (p : DynParams) (T : ℝ) : Tendsto (fun B : ℕ => blkEdet p T B) atTop (𝓝 0) := by
  have h1 := (asy_nu (p.h * Real.sqrt p.γstar) (mul_nonneg p.hh.le (Real.sqrt_nonneg _))).const_mul
    ((4 + 2 * T * blkKF p) * blkRplus p)
  have h2 := (asy_LB.const_mul 2).add asy_inv_B
  have h3 := h2.const_mul (blkCEp p)
  have := h1.add h3
  simp only [mul_zero, add_zero] at this
  refine this.congr fun B => ?_
  unfold blkEdet blkNu
  by_cases hB : (B : ℝ) = 0
  · simp [hB]
  · field_simp

private lemma asy_Em (K : ℝ) : Tendsto (fun B : ℕ => K *
    ((blockLen B : ℝ) * Real.log (2 * (B : ℝ)) ^ 2 / (B : ℝ) + (blockLen B : ℝ) ^ 3 / (B : ℝ) +
      1 / (blockLen B : ℝ))) atTop (𝓝 0) := by
  have h := (asy_logterm.add (asy_Lpow_B 3 (by norm_num) (by norm_num))).add asy_inv_L
  simpa using h.const_mul K

private lemma blk_TVL_nn (p : DynParams) (L : ℕ) : 0 ≤ blkTVL p L := by
  unfold blkTVL
  have hk : 0 ≤ kStar p.CSig p.γstar p.ϱ := by
    unfold kStar
    have : 0 ≤ p.CSig := le_trans zero_le_one p.hC
    exact mul_nonneg this (Real.sqrt_nonneg _)
  obtain ⟨hb0, hb1⟩ := p.hβ
  have hb2 : 0 < 1 - p.β := by linarith
  positivity

private lemma blk_L_le_B (B : ℕ) (hB : 1 ≤ B) : (blockLen B : ℝ) ≤ B := by
  have hV := blkV_ge_one B hB
  have h1 := blockLen_le_V B
  have h2 : blkV B ^ 8 ≤ blkV B ^ 64 := pow_le_pow_right₀ hV (by norm_num)
  rw [blkV_pow64] at h2
  linarith

private lemma blk_J_lamB (T : ℝ) (hT : 0 ≤ T) (B : ℕ) (hB : 1 ≤ B) (hL : 0 < blockLen B) (Θ : ℝ) :
    (blkJ T B : ℝ) * max 0 ((blockLen B : ℝ) / B * Θ) ≤ (T + 1) * max 0 Θ := by
  have hLr : (0 : ℝ) < blockLen B := by exact_mod_cast hL
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hLB : (blockLen B : ℝ) ≤ B := blk_L_le_B B hB
  have hJ : (blkJ T B : ℝ) ≤ T * B / blockLen B + 1 := by
    unfold blkJ
    push_cast
    have := Nat.floor_le (a := T * (B : ℝ) / (blockLen B : ℝ)) (by positivity)
    linarith
  have hm : max 0 ((blockLen B : ℝ) / B * Θ) = (blockLen B : ℝ) / B * max 0 Θ := by
    rw [mul_max_of_nonneg _ _ (by positivity), mul_zero]
  rw [hm]
  have hM : 0 ≤ max 0 Θ := le_max_left _ _
  have h1 : (blkJ T B : ℝ) * ((blockLen B : ℝ) / B) ≤ T + 1 := by
    calc (blkJ T B : ℝ) * ((blockLen B : ℝ) / B) ≤ (T * B / blockLen B + 1) * ((blockLen B : ℝ) / B) :=
          mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = T + (blockLen B : ℝ) / B := by field_simp
      _ ≤ T + 1 := by
          have : (blockLen B : ℝ) / B ≤ 1 := by rw [div_le_one hBr]; exact hLB
          linarith
  calc (blkJ T B : ℝ) * ((blockLen B : ℝ) / B * max 0 Θ)
      = ((blkJ T B : ℝ) * ((blockLen B : ℝ) / B)) * max 0 Θ := by ring
    _ ≤ (T + 1) * max 0 Θ := mul_le_mul_of_nonneg_right h1 hM

private lemma blk_psi_nonneg {m n B : ℕ} {C : Covariances m n} (p : DynParams) (SP : SpectralData C)
    (c : DynCoeff p SP B) (f g : ℝ → ℝ) (L : ℕ) (T : ℝ) (ψ : ℕ → Mat m n) :
    0 ≤ blkPsi p SP c f g L T ψ := by
  classical
  unfold blkPsi
  have h := Finset.le_sup' (f := fun N' =>
    if ∀ b ∈ Finset.range N', b * L < N' → ψ (b * L) ∈ admA p C then
      |blkU p SP c f g ψ N'| + |blkF p SP c f g ψ N'| / (B : ℝ) else 0)
    (Finset.mem_range.2 (Nat.succ_pos ⌊T * (B : ℝ)⌋₊) : 0 ∈ Finset.range (⌊T * (B : ℝ)⌋₊ + 1))
  refine le_trans ?_ h
  split_ifs <;> positivity

private lemma blk_psi_scale {m n B : ℕ} {C : Covariances m n} (p : DynParams) (SP : SpectralData C)
    (c : DynCoeff p SP B) (f g f' g' : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ i, f (SP.μ i) = M * f' (SP.μ i)) (hg : ∀ j, g (SP.lam j) = M * g' (SP.lam j))
    (L : ℕ) (T : ℝ) (ψ : ℕ → Mat m n) :
    blkPsi p SP c f g L T ψ ≤ M ^ 2 * blkPsi p SP c f' g' L T ψ := by
  classical
  have hX : ∀ Δ : Mat m n, Xfg f g C Δ = M ^ 2 * Xfg f' g' C Δ := by
    intro Δ
    rw [blk_Xfg_eq f g SP Δ, blk_Xfg_eq f' g' SP Δ, (blk_spec_integral SP Δ _).2, (blk_spec_integral SP Δ _).2,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [tensorFG]
    rw [hf i, hg j]; ring
  have hF : ∀ Δ : Mat m n, fieldOp p.h c.d c.ζ (specMeasure SP Δ) (tensorFG f g) =
      M ^ 2 * fieldOp p.h c.d c.ζ (specMeasure SP Δ) (tensorFG f' g') := by
    intro Δ
    rw [blk_F_formula, blk_F_formula]
    split_ifs with h
    · have hq : ∀ i j, tensorFG f g (SP.μ i, SP.lam j) = M ^ 2 * tensorFG f' g' (SP.μ i, SP.lam j) := by
        intro i j; simp only [tensorFG]; rw [hf i, hg j]; ring
      simp only [hq]
      have e1 : ∑ i, ∑ j, modeQ SP Δ i j * (M ^ 2 * tensorFG f' g' (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)) =
          M ^ 2 * ∑ i, ∑ j, modeQ SP Δ i j * (tensorFG f' g' (SP.μ i, SP.lam j) * c.d (SP.μ i, SP.lam j)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have e2 : ∑ i, ∑ j, (c.v i j / (B : ℝ)) * (M ^ 2 * tensorFG f' g' (SP.μ i, SP.lam j)) =
          M ^ 2 * ∑ i, ∑ j, (c.v i j / (B : ℝ)) * tensorFG f' g' (SP.μ i, SP.lam j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      rw [e1, e2]; ring
    · simp
  unfold blkPsi
  refine Finset.sup'_le _ _ fun N hN => ?_
  have hle := Finset.le_sup' (f := fun N' =>
    if ∀ b ∈ Finset.range N', b * L < N' → ψ (b * L) ∈ admA p C then
      |blkU p SP c f' g' ψ N'| + |blkF p SP c f' g' ψ N'| / (B : ℝ) else 0) hN
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg _
  by_cases hcond : ∀ b ∈ Finset.range N, b * L < N → ψ (b * L) ∈ admA p C
  · rw [if_pos hcond] at hle
    rw [if_pos hcond]
    have hU : blkU p SP c f g ψ N = M ^ 2 * blkU p SP c f' g' ψ N := by
      unfold blkU
      rw [hX, hX]
      have : ∀ u, blkF p SP c f g ψ u = M ^ 2 * blkF p SP c f' g' ψ u := fun u => hF _
      simp only [this, ← Finset.mul_sum]
      ring
    have hFF : blkF p SP c f g ψ N = M ^ 2 * blkF p SP c f' g' ψ N := hF _
    rw [hU, hFF, abs_mul, abs_mul, abs_of_nonneg hM2]
    calc M ^ 2 * |blkU p SP c f' g' ψ N| + M ^ 2 * |blkF p SP c f' g' ψ N| / (B : ℝ)
        = M ^ 2 * (|blkU p SP c f' g' ψ N| + |blkF p SP c f' g' ψ N| / (B : ℝ)) := by ring
      _ ≤ M ^ 2 * _ := mul_le_mul_of_nonneg_left hle hM2
  · rw [if_neg hcond]
    exact mul_nonneg hM2 (blk_psi_nonneg p SP c f' g' L T ψ)

set_option maxHeartbeats 4000000 in
private theorem blk_seq_main (cert : Muon.External.GaussianOpNorm)
    (certOp : Muon.External.GaussianOpNormL6) (certP : Muon.External.GaussianPoincare)
    (certQ : Muon.External.GaussianQuadFormLp)
    {m n B : ℕ → ℕ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {p : DynParams}
    (F : ∀ k, FrozenParams (m k) (n k) (B k)) (hyp : DynHyp p P m n B (fun k => (F k).C))
    (SD : ∀ k, SpectralData (F k).C) (c : ∀ k, DynCoeff p (SD k) (B k))
    (hc : ∀ k, IsActualCoeff cert (F k) (SD k) (c k))
    (T : ℝ) (hT : 0 < T) (f g : ℝ → ℝ) (hf : ∀ x, |f x| ≤ 1) (hg : ∀ x, |g x| ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun k : ℕ => P {ω | ε < blkPsi p (SD k) (c k) f g (blockLen (B k)) T
      (fun t => errPath hyp k t ω)}) atTop (𝓝 0) := by
  classical
  have hβ : ∀ k, (F k).β = p.β := fun k => (hc k).1
  haveI hPprob : IsProbabilityMeasure P := blk_prob_hyp hyp
  choose Ω' inst P' pi S' hpi hC hAlg hW hM hX using fun k => hyp.exists_dynSetup k
  letI : ∀ k, MeasurableSpace (Ω' k) := inst
  haveI hP'prob : ∀ k, IsProbabilityMeasure (P' k) := fun k => ⟨by
    have := (hpi k).measure_preimage (MeasurableSet.univ.nullMeasurableSet)
    rw [Set.preimage_univ] at this
    rw [this]; exact measure_univ⟩
  set S'' : ∀ k, DynSetup p (P' k) (m k) (n k) (B k) := fun k => blkRecast (S' k) (F k).C (hC k)
    with hS''
  set S0 : ∀ k, FrozenSamples (P' k) (m k) (n k) (B k) := fun k => blkFrozen (S'' k).cs with hS0
  -- transfer of probabilities
  have htransfer : ∀ k, P {ω | ε < blkPsi p (SD k) (c k) f g (blockLen (B k)) T
      (fun t => errPath hyp k t ω)} =
      P' k {ω' | ε < blkPsi p (SD k) (c k) f g (blockLen (B k)) T
        (fun t => dynDelta (S'' k) t ω')} := by
    intro k
    refine blk_transfer (pi k) (hpi k) (fun t ω => errPath hyp k t ω)
      (fun t => blk_errPath_aem hyp k t)
      (fun t ω' => dynDelta (S'' k) t ω') ?_
      (blkPsi p (SD k) (c k) f g (blockLen (B k)) T) (blk_psi_meas p (SD k) (c k) f g _ T) ε
    exact blk_paths_ae hyp k (pi k) (S'' k) rfl (hAlg k) (hW k) (hM k)
      (fun u => by rw [show dynBatch (S'' k) u = dynBatch (S' k) u from blkRecast_batch _ _ _ u]; exact hX k u)
  simp_rw [htransfer]
  -- the diffuseness threshold
  have hW0 : Tendsto (fun k => opNorm (Ahat (S'' k).C ((S'' k).W0 - (S'' k).alg.Wstar))) atTop (𝓝 0) := by
    refine hyp.W0_hat.congr (fun k => ?_)
    show opNorm (Ahat (F k).C (hyp.W0 k - (hyp.alg k).Wstar)) =
      opNorm (Ahat (F k).C ((S' k).W0 - (S' k).alg.Wstar))
    rw [hW k, hAlg k]
  have hdiff : ∀ ε' : ℝ, 0 < ε' → Tendsto (fun k => P' k {ω | ∃ t : ℕ,
      (t : ℕ∞) ≤ dynBlockExitTime (S'' k) ω ∧ (t : ℝ) ≤ T * (B k : ℝ) ∧
        ε' < diffuseness (S'' k).C (dynDelta (S'' k) t ω)}) atTop (𝓝 0) :=
    fun ε' hε' => lem_app_dyn_diffuse certOp p P' m n B S'' hyp.regime hW0 T hT ε' hε'
  obtain ⟨δ, hδanti, hδpos, hδ0, hδbad⟩ := blk_diag_delta
    (fun k ε' => P' k {ω | ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime (S'' k) ω ∧
      (t : ℝ) ≤ T * (B k : ℝ) ∧ ε' < diffuseness (S'' k).C (dynDelta (S'' k) t ω)}) B hdiff
    hyp.regime.B_top
  have hδ' : Tendsto (fun k => δ (B k)) atTop (𝓝 0) := hδ0.comp hyp.regime.B_top
  -- constants of the upstream results
  obtain ⟨Bw, hBw⟩ := blk_window p
  obtain ⟨Bm, Km, hKm⟩ := blk_mart_hyp certP certOp p
  obtain ⟨B0, Kp, Kr, Kq, Cb, hKp, hKq, hCb, hlam⟩ := blk_lam_bound certQ certOp certP p δ hδanti hδ0
  have he1 := blk_drift_uniform F hyp hβ P' S0 (fun k => δ (B k)) hδ'
  have he2 := blk_forcing_uniform cert F hyp hβ P' S0 SD f g hf hg (fun k => δ (B k)) hδ'
  have hρ := prop_app_dyn_response_ii certQ certOp certP p (Real.sqrt (p.Estar + 1)) δ hδanti hδ0 Kr
  set RA : ℝ := Real.sqrt (p.Estar + 1) with hRA
  set CS : ℝ := p.CSig / Real.sqrt p.ϱ with hCS
  have hCS0 : 0 ≤ CS := by
    have := le_trans zero_le_one p.hC
    simp only [hCS]; positivity
  have hfI : ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ 1 := fun x _ => hf x
  have hgI : ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ 1 := fun x _ => hg x
  set Θf : ℝ → ℝ → ℕ → ℝ := fun η1 η2 B' =>
    2 * p.h * Kp * (prefixLen p.β B' : ℝ) ^ 2 / (blockLen B' : ℝ) +
      2 * p.h * (prefixLen p.β B' : ℝ) * RA * (CS + η1) / (blockLen B' : ℝ) +
      2 * p.h * responseRho p Kr RA δ B' + p.h ^ 2 * Kq * Cb * blkRbar B' +
      p.h ^ 2 * (blockLen B' : ℝ) * (CS + η1) ^ 2 / (B' : ℝ) + 2 * p.h * RA * η1 +
      p.h ^ 2 * (blkTVL p (blockLen B') + η2) with hΘf
  set Emf : ℕ → ℝ := fun B' => Km * (T + 1) * ((blockLen B' : ℝ) * Real.log (2 * (B' : ℝ)) ^ 2 / (B' : ℝ) +
    (blockLen B' : ℝ) ^ 3 / (B' : ℝ) + 1 / (blockLen B' : ℝ)) with hEmf
  have hper : ∀ η1 η2 : ℝ, 0 < η1 → η1 ≤ 1 → 0 < η2 → ∀ᶠ k in atTop,
      P' k {ω' | ε < blkPsi p (SD k) (c k) f g (blockLen (B k)) T (fun t => dynDelta (S'' k) t ω')} ≤
        P' k {ω | ∃ t : ℕ, (t : ℕ∞) ≤ dynBlockExitTime (S'' k) ω ∧ (t : ℝ) ≤ T * (B k : ℝ) ∧
          δ (B k) < diffuseness (S'' k).C (dynDelta (S'' k) t ω)} +
        ENNReal.ofReal (36 * Emf (B k) / ε ^ 2) +
        ENNReal.ofReal (3 * ((T + 1) * max 0 (Θf η1 η2 (B k))) / ε) := by
    intro η1 η2 hη1 hη1' hη2
    have hev1 : ∀ᶠ k in atTop, max (max Bw Bm) (max B0 1) ≤ B k :=
      hyp.regime.B_top.eventually (eventually_ge_atTop _)
    have hev2 : ∀ᶠ k in atTop, prefixLen p.β (B k) ≤ blockLen (B k) :=
      hyp.regime.B_top.eventually (prefixLen_le_blockLen p.β)
    have hev3 : ∀ᶠ k in atTop, 1 ≤ blockLen (B k) :=
      hyp.regime.B_top.eventually (blockLen_tendsto_nat.eventually_ge_atTop 1)
    have hev4 : ∀ᶠ k in atTop, blkEdet p T (B k) ≤ ε / 3 :=
      (asy_Edet p T).comp hyp.regime.B_top |>.eventually (ge_mem_nhds (by linarith))
    filter_upwards [hev1, hev2, hev3, hev4, he1 η1 hη1, he2 η2 hη2] with k hk1 hk2 hk3 hk4 hk5 hk6
    have hBw' : Bw ≤ B k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk1
    have hBm' : Bm ≤ B k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk1
    have hB0' : B0 ≤ B k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk1
    have hB1 : 1 ≤ B k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk1
    have hBpos : 0 < B k := hB1
    have hLpos : 0 < blockLen (B k) := hk3
    have hRpos : ∀ D : Mat (m k) (n k), D ∈ admA p (F k).C → 0 < riskSigma (F k).C D := by
      intro D hD
      have h := hD
      simp only [admA, admSetOf, admBase, Set.mem_setOf_eq] at h
      linarith [h.1, p.hr0]
    have hVb : ∀ (t : ℕ) (D : Mat (m k) (n k)), D ∈ admA p (S'' k).C →
        diffuseness (S'' k).C D ≤ δ (B k) → fro (dynVbar p (S'' k) t D) ≤ CS + η1 := by
      intro t D hD hdD
      have hR := hRpos D hD
      rw [blk_Vbar_eq (S'' k) (withState (F k) (Ahat (F k).C D) (block_Ahat_norm _ _ hR)) rfl (hβ k)
        (S0 k) t D hR rfl]
      exact blk_hVb_state F hyp hβ P' S0 SD k D hR (δ (B k)) η1 hdD hk5
    have hDR : ∀ (t : ℕ) (D : Mat (m k) (n k)), D ∈ admA p (S'' k).C →
        diffuseness (S'' k).C D ≤ δ (B k) →
        |frobIP (wfg f g (S'' k).C D) (dynVbar p (S'' k) t D) -
          (Real.sqrt (riskSigma (S'' k).C D))⁻¹ * ∑ i, ∑ j, modeQ (SD k) D i j *
            (tensorFG f g ((SD k).μ i, (SD k).lam j) * (c k).d ((SD k).μ i, (SD k).lam j))| ≤
          fro D * η1 := by
      intro t D hD hdD
      have hR := hRpos D hD
      rw [blk_Vbar_eq (S'' k) (withState (F k) (Ahat (F k).C D) (block_Ahat_norm _ _ hR)) rfl (hβ k)
        (S0 k) t D hR rfl]
      exact blk_hDR_state F hyp hβ P' S0 SD c cert hc k D hR f g hf hg (δ (B k)) η1 hdD hk5
    have hFR : ∀ D : Mat (m k) (n k), D ∈ admA p (S'' k).C → diffuseness (S'' k).C D ≤ δ (B k) →
        |(blkFL p F S0 SD k D).sum (fun x r => f x.1 * g x.2 * r) -
          ∑ i, ∑ j, ((c k).v i j / (B k : ℝ)) * tensorFG f g ((SD k).μ i, (SD k).lam j)| ≤
          blkTVL p (blockLen (B k)) + η2 := by
      intro D hD hdD
      exact blk_hFR_state cert F hyp hβ P' S0 SD c hc k D (hRpos D hD) f g hf hg hk3 hBpos (δ (B k)) η2
        hdD hk6
    have hLam1 := hlam (Ω' k) (P' k) (m k) (n k) (B k) (S'' k) (SD k) (c k) f g hf hg T hT.le
      (Ω' k) (P' k) (S0 k) (blkFL p F S0 SD k) (blk_hFL p F hβ S0 SD k) (CS + η1) η1
      (blkTVL p (blockLen (B k)) + η2) (by linarith) hη1.le
      (by have := blk_TVL_nn p (blockLen (B k)); linarith) hVb hDR hFR hB0' hBpos hk2
    have hLam' : ∀ b ∈ Finset.Ico 1 (blkJ T (B k)),
        Integrable (fun ω => (if b < blkBstar (S'' k) (δ (B k)) (blkJ T (B k)) ω then (1 : ℝ) else 0) *
          |blkLam (S'' k) (SD k) (c k) f g b ω|) (P' k) ∧
        ∫ ω, (if b < blkBstar (S'' k) (δ (B k)) (blkJ T (B k)) ω then (1 : ℝ) else 0) *
          |blkLam (S'' k) (SD k) (c k) f g b ω| ∂(P' k) ≤
          max 0 ((blockLen (B k) : ℝ) / (B k) * Θf η1 η2 (B k)) :=
      fun b hb => ⟨(hLam1 b hb).1, (hLam1 b hb).2.trans (le_max_right _ _)⟩
    have hm := blk_master (S'' k) (SD k) (c k) f g hfI hgI hBpos T hT.le (δ (B k)) (blk_h0 (S'' k))
      (fun ω b hb u h1 h2 => hBw (Ω' k) (P' k) (m k) (n k) (B k) (S'' k) hBw' ω b hb u h1 h2)
      (Emf (B k)) (max 0 ((blockLen (B k) : ℝ) / (B k) * Θf η1 η2 (B k)))
      (hKm (Ω' k) (P' k) (m k) (n k) (B k) (S'' k) f g hfI hgI hBm' (δ (B k)) T hT) hLam'
      (le_max_left _ _) ε hε hk4
    refine hm.trans ?_
    refine add_le_add (add_le_add (measure_mono fun ω hω =>
      blk_notGd_sub (S'' k) T (δ (B k)) hT.le hLpos ω hω) le_rfl) ?_
    apply ENNReal.ofReal_le_ofReal
    have hJ := blk_J_lamB T hT.le (B k) hB1 hLpos (Θf η1 η2 (B k))
    have hεp : 0 < ε := hε
    have := mul_le_mul_of_nonneg_left hJ (by norm_num : (0 : ℝ) ≤ 3)
    rw [div_le_div_iff_of_pos_right hεp]
    linarith
  -- the final epsilon-argument
  rw [ENNReal.tendsto_nhds_zero]
  intro θ hθ
  by_cases hθtop : θ = ⊤
  · exact Eventually.of_forall fun _ => by rw [hθtop]; exact le_top
  have hθr : 0 < θ.toReal := ENNReal.toReal_pos hθ.ne' hθtop
  set θr : ℝ := θ.toReal with hθrdef
  have hRA0 : 0 ≤ RA := Real.sqrt_nonneg _
  set c0 : ℝ := 3 * (T + 1) * (2 * p.h * RA + p.h ^ 2) / ε with hc0def
  have hc0 : 0 ≤ c0 := by
    have := p.hh
    simp only [hc0def]; positivity
  set η : ℝ := min 1 (θr / (4 * (c0 + 1))) with hηdef
  have hη : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hcη : c0 * η ≤ θr / 4 := by
    have h1 : η ≤ θr / (4 * (c0 + 1)) := min_le_right _ _
    calc c0 * η ≤ c0 * (θr / (4 * (c0 + 1))) := mul_le_mul_of_nonneg_left h1 hc0
      _ = θr / 4 * (c0 / (c0 + 1)) := by field_simp
      _ ≤ θr / 4 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [div_le_one (by positivity)]; linarith
      _ = θr / 4 := mul_one _
  have hτ : 0 < θr / 8 := by positivity
  have hA := ENNReal.tendsto_nhds_zero.1 hδbad (ENNReal.ofReal (θr / 8)) (ENNReal.ofReal_pos.2 hτ)
  have hEm : Tendsto (fun k => ENNReal.ofReal (36 * Emf (B k) / ε ^ 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun k => 36 * Emf (B k) / ε ^ 2) atTop (𝓝 0) := by
      have := ((asy_Em Km).const_mul (T + 1)).comp hyp.regime.B_top |>.const_mul 36 |>.div_const (ε ^ 2)
      simpa [hEmf, mul_assoc, mul_left_comm] using this
    simpa using ENNReal.tendsto_ofReal h1
  have hEm' := ENNReal.tendsto_nhds_zero.1 hEm (ENNReal.ofReal (θr / 8)) (ENNReal.ofReal_pos.2 hτ)
  have hΘlim : Tendsto (fun k => Θf η η (B k)) atTop (𝓝 (2 * p.h * RA * η + p.h ^ 2 * η)) :=
    (asy_Theta p Kp Kq Cb Kr RA CS η η δ hρ).comp hyp.regime.B_top
  have hLinf : 0 ≤ 2 * p.h * RA * η + p.h ^ 2 * η := by have := p.hh; positivity
  have hxlim : Tendsto (fun k => 3 * ((T + 1) * max 0 (Θf η η (B k))) / ε) atTop
      (𝓝 (3 * ((T + 1) * max 0 (2 * p.h * RA * η + p.h ^ 2 * η)) / ε)) :=
    ((tendsto_const_nhds.max hΘlim).const_mul (T + 1)).const_mul 3 |>.div_const ε
  have hxval : 3 * ((T + 1) * max 0 (2 * p.h * RA * η + p.h ^ 2 * η)) / ε = c0 * η := by
    rw [max_eq_right hLinf]; simp only [hc0def]; ring
  rw [hxval] at hxlim
  have hx := hxlim.eventually (ge_mem_nhds (show c0 * η < θr / 2 by linarith))
  filter_upwards [hper η η hη hη1 hη, hA, hEm', hx] with k hk hkA hkE hkx
  refine hk.trans ?_
  have h3 : ENNReal.ofReal (3 * ((T + 1) * max 0 (Θf η η (B k))) / ε) ≤ ENNReal.ofReal (θr / 2) :=
    ENNReal.ofReal_le_ofReal hkx
  calc _ ≤ ENNReal.ofReal (θr / 8) + ENNReal.ofReal (θr / 8) + ENNReal.ofReal (θr / 2) :=
        add_le_add (add_le_add hkA hkE) h3
    _ = ENNReal.ofReal (θr / 8 + θr / 8 + θr / 2) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal θr := ENNReal.ofReal_le_ofReal (by linarith)
    _ = θ := ENNReal.ofReal_toReal hθtop

/-- `lem:app-dyn-block`, snapshot `cr-2026-10-23`. Block residual. Source, `section.tex` ll. 2156–2165, verbatim:
```latex
\begin{lemma}[Block residual]\label{lem:app-dyn-block}
Let $b_c$ be as in \cref{lem:app-dyn-diffuse} and $\macrotime_c\defeq t_{b_c}/B$.
For every $T>0$ and all bounded $f,g$ on $[0,C_\Sigma]$,
\[
\sup_{\macrotime\le T}\Big|\int f\tensor g\,\dif\chi^{\mathrm{act}}(\macrotime\wedge\macrotime_c)-\int f\tensor g\,\dif\chi^{\mathrm{act}}(0)
-\int_0^{\macrotime\wedge\macrotime_c}\!\!\int f\tensor g\,\dif\mathsf F_B\big(\chi^{\mathrm{act}}(\sigma)\big)\,\dif\sigma\Big|\longrightarrow0
\]
in probability. The process and the integral are stopped at the same
time.
\end{lemma}
```
Encoding: for every `T > 0` and bounded `f, g` on `[0, C_Σ]` the supremum over `τ ∈ [0, T]` of `blockResidual` tends
to zero in probability (`the statement is the source display with the stopping of both sides at `τ ∧ τ_c``). Part (i) is the integrability of the test integrals against `χ^act` (needed for the
Bochner integrals), part (ii) that of the stopped field integrand; part (iii) is the convergence. -/
theorem lem_app_dyn_block
    -- certificates of the cited results used by the proof (`Muon.External`)
    (cert : Muon.External.GaussianOpNorm) (certOp : Muon.External.GaussianOpNormL6)
    (certP : Muon.External.GaussianPoincare) (certQ : Muon.External.GaussianQuadFormLp)
    -- (H1)–(H4) and the frozen parameters of the model at each dimension
    (F : ∀ k : ℕ, FrozenParams (m k) (n k) (B k))
    (hyp : DynHyp p P m n B (fun k => (F k).C))
    (S : ∀ k : ℕ, SpectralData (F k).C)
    -- the coefficients `𝔡`, `ζ = ζ_ϱ` of C and D (`hc`, `eqn:app-dyn-coefficient-bounds`)
    (c : ∀ k : ℕ, DynCoeff p (S k) (B k))
    (hc : ∀ k : ℕ, IsActualCoeff cert (F k) (S k) (c k))
    -- `T > 0` and the bounded test functions `f, g` on `[0, C_Σ]`
    (T : ℝ) (hT : 0 < T) (f g : ℝ → ℝ)
    (hf : ∃ M : ℝ, ∀ x ∈ Icc (0 : ℝ) p.CSig, |f x| ≤ M)
    (hg : ∃ M : ℝ, ∀ x ∈ Icc (0 : ℝ) p.CSig, |g x| ≤ M) :
    -- (i) the test integrals against the actual spectral measures are integrable
    (∀ k : ℕ, ∀ ω : Ω, ∀ s : ℝ, Integrable (tensorFG f g) (actMeas hyp S k ω s)) ∧
    -- (ii) the stopped field integrand is interval integrable
    (∀ k : ℕ, ∀ ω : Ω, ∀ τ ∈ Icc (0 : ℝ) T,
      IntervalIntegrable
        (fun σ => fieldOp p.h (c k).d (c k).ζ (actMeas hyp S k ω σ) (tensorFG f g)) volume 0
        (stopMacro (blockLen (B k)) (B k) (blockExitIdx hyp k ω) τ)) ∧
    -- (iii) `sup_{τ ≤ T} |residual| → 0` in probability
    (∀ ε : ℝ, 0 < ε →
      Tendsto (fun k : ℕ => P {ω | ENNReal.ofReal ε <
        ⨆ τ ∈ Icc (0 : ℝ) T, ENNReal.ofReal (blockResidual hyp S c f g k ω τ)}) atTop (𝓝 0)) := by
  classical
  have hβ : ∀ k, (F k).β = p.β := fun k => (hc k).1
  haveI : IsProbabilityMeasure P := blk_prob_hyp hyp
  refine ⟨?_, ?_, ?_⟩
  · intro k ω s
    exact (blk_spec_integral (S k) _ (tensorFG f g)).1
  · intro k ω τ _
    exact blk_stepfun_ii (blkF p (S k) (c k) f g (fun t => errPath hyp k t ω)) (B k) 0 _
  · intro ε hε
    obtain ⟨Mf, hMf⟩ := hf
    obtain ⟨Mg, hMg⟩ := hg
    set M : ℝ := max (max Mf Mg) 1 with hMdef
    have hM1 : 1 ≤ M := le_max_right _ _
    have hM0 : 0 < M := by linarith
    set f' : ℝ → ℝ := fun x => (if x ∈ Icc (0 : ℝ) p.CSig then f x else 0) / M with hf'def
    set g' : ℝ → ℝ := fun x => (if x ∈ Icc (0 : ℝ) p.CSig then g x else 0) / M with hg'def
    have hf'b : ∀ x, |f' x| ≤ 1 := by
      intro x
      simp only [hf'def]
      by_cases hx : x ∈ Icc (0 : ℝ) p.CSig
      · rw [if_pos hx, abs_div, abs_of_pos hM0, div_le_one hM0]
        exact (hMf x hx).trans ((le_max_left _ _).trans (le_max_left _ _))
      · rw [if_neg hx]; simp
    have hg'b : ∀ x, |g' x| ≤ 1 := by
      intro x
      simp only [hg'def]
      by_cases hx : x ∈ Icc (0 : ℝ) p.CSig
      · rw [if_pos hx, abs_div, abs_of_pos hM0, div_le_one hM0]
        exact (hMg x hx).trans ((le_max_right _ _).trans (le_max_left _ _))
      · rw [if_neg hx]; simp
    have hmain := blk_seq_main cert certOp certP certQ F hyp S c hc T hT f' g' hf'b hg'b (ε / M ^ 2)
      (by positivity)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain
      (Eventually.of_forall fun k => zero_le) ?_
    filter_upwards [hyp.regime.B_top.eventually (eventually_ge_atTop 1)] with k hk
    refine measure_mono fun ω hω => ?_
    have hω' : ENNReal.ofReal ε < ⨆ τ ∈ Icc (0 : ℝ) T, ENNReal.ofReal (blockResidual hyp S c f g k ω τ) := hω
    obtain ⟨τ, hτ'⟩ := lt_iSup_iff.1 hω'
    obtain ⟨hτ, hlt⟩ := lt_iSup_iff.1 hτ'
    have hεlt : ε < blockResidual hyp S c f g k ω τ := (ENNReal.ofReal_lt_ofReal_iff'.1 hlt).1
    obtain ⟨hμ, hl⟩ := blk_spec_mem (S k) p.CSig (hyp.normBd k).2 (hyp.normBd k).1
    have hfa : ∀ i, f ((S k).μ i) = M * f' ((S k).μ i) := by
      intro i
      simp only [hf'def, if_pos (hμ i)]
      field_simp
    have hga : ∀ j, g ((S k).lam j) = M * g' ((S k).lam j) := by
      intro j
      simp only [hg'def, if_pos (hl j)]
      field_simp
    have hres : blockResidual hyp S c f g k ω τ ≤ blkPsi p (S k) (c k) f g (blockLen (B k)) T
        (fun t => errPath hyp k t ω) :=
      blk_res_le_psi p (S k) (c k) f g (blockLen (B k)) T (fun t => errPath hyp k t ω)
        (by omega) τ hτ
    have hsc := blk_psi_scale p (S k) (c k) f g f' g' M hM0.le hfa hga (blockLen (B k)) T
      (fun t => errPath hyp k t ω)
    show ε / M ^ 2 < blkPsi p (S k) (c k) f' g' (blockLen (B k)) T (fun t => errPath hyp k t ω)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith

-- BLK-INSERT-POINT

end Muon.Dynamics

end
