import Muon.Drift.Defs
import Muon.DetEquiv.Gaussian
import Muon.Foundations.Freezing
import Muon.Drift.Column

/-!
# Muon.Drift: conditional moments of the deletion coefficients (work package L-C.5)

Interface of `lem:app-drift-coeffmoments`, `lem:app-drift-multiplier`, `lem:app-drift-rank`,
with the two helpers `eqn:app-drift-bessel-frob` (`bessel_frob_uu/_vv/_uv`) and
`eqn:app-drift-delta-alpha` (`delta_alpha`), snapshot `cr-2026-10-23`
(`sections/03-drift/section.tex` l.281–294, 330–344, 355–361, 404–411, 453–456).

Model data. Every statement is over the frozen-state model `FrozenParams m n B` and
`FrozenSamples P m n B` (`Muon.Setup.Frozen`, reused). The source's σ-field `𝒢_{ja}` is
`sigmaOthers F S t j` (`Muon.Drift.Defs`); the sample `(j,a)` is the age-`j` sample in slot `1`,
so `(d,u,v) = (ageD, ageU, ageV)` (`Muon.DetEquiv.Concentration`). The deleted buffer `M_0`
enters as a general `𝒢`-measurable matrix field `M0`, as in the source ("let `M_0` be a function
of the samples other than `(j,a)`"); `M := M0 + (ϖ d) u⊗v` is the matrix of the setting of
`lem:app-de-deletion`.

Constants. Each `∃ C` is placed before the quantifier over all model data (`m n B`, the
probability space, the samples, `M0`, `ϖ`, `h`, `D`), and depends only on the listed parameters
(`p, s₀, C_Σ, γ⋆`). The finite-dimensional hypotheses `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ` and
`max(N_out,N_in) ≤ γ⋆ B` are those of the source's constants (card §6.3); `‖Â‖_F = 1` is the
field `F.hA`.

Conditional norms. The source's `‖ξ‖_{p,𝒢} = (E_𝒢|ξ|^p)^{1/p}` is stated in the equivalent
form `E_𝒢|ξ|^p ≤ (·)^p` (both sides nonnegative, `p` a natural number); the `Integrable` conjunct
(the unconditional `p`-th moment is finite) is stated because `condExp` of a non-integrable
function is `0`, so the bound would otherwise be vacuous (card §6.11).

Junk values. `condExp`, `∫` and `tsum` return junk outside their domain. Every conditional
bound carries the matching `Integrable` claim; `φ_ϖ(K)` is an integral over `freshMeas`, and its
integrability is stated separately (`phiFresh_integrable`).
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Drift

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-! ## Sample-indexed coefficients (`eqn:app-drift-coeffmoments`, `eqn:app-drift-multiplier`)

For the age-`j` sample `(d, u, v) = (ageD, ageU, ageV)`, a deleted buffer `M0 : Ω → Mat m n` and a
multiplier `ϖ`, the source's `(𝗁, 𝗎, 𝗏) = (ϖ d, u_ja, v_ja)` and `M = M_0 + 𝗁 𝗎⊗𝗏`. -/

/-- `M = M_0 + (ϖ d) u⊗v` for the age-`j` sample (`lem:app-de-deletion` setting). -/
def ageBuf {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ : ℝ) (ω : Ω) : Mat m n :=
  M0 ω + (ϖ * ageD F S t j ω) • Muon.outer (ageU F S t j ω) (ageV F S t j ω)

/-- `α₁ = 𝗁(1+𝗁𝖢)/Λ` at `(M_0, 𝗁, 𝗎, 𝗏) = (M_0, ϖ d, u_ja, v_ja)` (`eqn:app-de-coefficients`). -/
def ageAlpha1 {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ s : ℝ) (ω : Ω) : ℝ :=
  Muon.DetEquiv.alpha1 (M0 ω) (ϖ * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-- `α₂ = 𝗁²𝖴/Λ` at `(M_0, ϖ d, u_ja, v_ja)` (`eqn:app-de-coefficients`). -/
def ageAlpha2 {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ s : ℝ) (ω : Ω) : ℝ :=
  Muon.DetEquiv.alpha2 (M0 ω) (ϖ * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-- `α₃ = -s𝗁²𝖵/Λ` at `(M_0, ϖ d, u_ja, v_ja)` (`eqn:app-de-coefficients`). -/
def ageAlpha3 {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ s : ℝ) (ω : Ω) : ℝ :=
  Muon.DetEquiv.alpha3 (M0 ω) (ϖ * ageD F S t j ω) (ageU F S t j ω) (ageV F S t j ω) s

/-! ## Private helpers for `bessel_frob_uu/_vv/_uv` (proved; not statements) -/

open scoped MatrixOrder

private lemma bf_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

private lemma bf_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma bf_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

open scoped Matrix.Norms.L2Operator in
private lemma bf_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ opNorm M * fro N := by
  have hcol : ∀ j : Fin r, ∑ i, (M * N) i j ^ 2 ≤ opNorm M ^ 2 * ∑ k, N k j ^ 2 := by
    intro j
    obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin q), ∀ k, v.ofLp k = N k j :=
      ⟨(EuclideanSpace.equiv (Fin q) ℝ).symm (fun k => N k j), fun k => rfl⟩
    have h1 : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)‖ ≤ opNorm M * ‖v‖ := by
      rw [opNorm_eq_norm]
      exact Matrix.l2_opNorm_mulVec M v
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
    have e1 : ∀ i, ((EuclideanSpace.equiv (Fin p) ℝ).symm (M *ᵥ v)).ofLp i = (M * N) i j := by
      intro i
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, hv]
    have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, N k j ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [hv]
    simp only [e1, e2] at h2
    exact h2
  have hfro : fro (M * N) ^ 2 ≤ (opNorm M * fro N) ^ 2 := by
    rw [bf_fro_sq, mul_pow, bf_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (bf_fro_nonneg _) (mul_nonneg (bf_opNorm_nonneg M)
    (bf_fro_nonneg N)) two_ne_zero).mp hfro

open scoped Matrix.Norms.L2Operator in
private lemma bf_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma bf_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private lemma bf_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := bf_fro_mul_le_left Nᵀ Mᵀ
  rw [← Matrix.transpose_mul, bf_fro_transpose, bf_opNorm_transpose, bf_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

open scoped Matrix.Norms.L2Operator in
private lemma bf_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
/-- `‖r_out‖² = ‖Σ_out‖` for the regularized square root `r_out`. -/
private lemma bf_opNorm_rOut_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rOut C) * opNorm (rOut C) = opNorm C.Sout := by
  have hh : (rOut C)ᴴ = rOut C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
  have hsq : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rOut C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

open scoped Matrix.Norms.L2Operator in
/-- The `r_in` analogue of `bf_opNorm_rOut_mul_self`. -/
private lemma bf_opNorm_rIn_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

private lemma bf_fro_one {m : ℕ} : fro (1 : Mat m m) = Real.sqrt m := by
  unfold fro
  simp [Matrix.one_apply]

/-- `‖S‖_F ≤ √m ‖S‖` for `S` square of size `m` (the factor `√m` of the Id term). -/
private lemma bf_fro_le_sqrt_mul_opNorm {m : ℕ} (S : Mat m m) :
    fro S ≤ Real.sqrt m * opNorm S := by
  have h := bf_fro_mul_le_left S (1 : Mat m m)
  rw [Matrix.mul_one, bf_fro_one] at h
  linarith [mul_comm (opNorm S) (Real.sqrt m)]

/-- Conditional Jensen for the square: `(E_𝒢 e)² ≤ E_𝒢 e²` a.e. -/
private lemma bf_jensen_sq (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (e : Ω → ℝ) (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P, condExp G P e ζ ^ 2 ≤ condExp G P (fun ω => e ω ^ 2) ζ := by
  have hcvx : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) := (Even.convexOn_pow (by decide))
  have hcont : LowerSemicontinuousOn (fun x : ℝ => x ^ 2) Set.univ :=
    (by fun_prop : Continuous fun x : ℝ => x ^ 2).continuousOn.lowerSemicontinuousOn
  have h := ConvexOn.map_condExp_le (μ := P) (m := G) (mα := mΩ) hG hcvx hcont
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) isClosed_univ
    (he2.integrable one_le_two) (he2.integrable_sq)
  filter_upwards [h] with ζ hζ
  simpa [Function.comp_def] using hζ

/-! ## Private integrability helpers (copies of private lemmas of `Muon.DetEquiv.Gaussian`) -/

section BfCopies
open Muon.Foundations

private lemma bf_gmono {n k : ℕ} (c : Fin k → Fin n) :
    Integrable (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r)) (stdGaussianPi n) := by
  have hprod : (fun z : Fin n → ℝ => ∏ r : Fin k, z (c r))
      = fun z : Fin n → ℝ => ∏ i : Fin n, (fun (x : ℝ) => x ^ Fintype.card {r // c r = i}) (z i) := by
    funext z
    rw [← Fintype.prod_fiberwise c (fun r => z (c r))]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Finset.prod_congr rfl (fun (r : {r // c r = i}) _ => by rw [r.2]), Finset.prod_const,
      Finset.card_univ]
  rw [hprod]
  unfold stdGaussianPi
  exact Integrable.fintype_prod (fun i => gaussian_integrable_pow _)

private lemma bf_gtwo {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := bf_gmono (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma bf_gfour {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := bf_gmono (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

private lemma bf_gfam1_memLp (m n : ℕ) (a : Fin m × Fin n) :
    MemLp (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) 2 (gaussPair m n) := by
  have hm : Measurable (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h := Integrable.mul_prod (bf_gtwo a.1 a.1) (bf_gtwo a.2 a.2)
  unfold gaussPair
  convert h using 2 with x
  ring

private lemma bf_gsq_memLp (d : ℕ) (a : Fin d × Fin d) :
    MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (stdGaussianPi d) := by
  have hm : Measurable (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) := by
    fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  set c : ℝ := (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2
  have e : (fun z : Vec d => (z a.1 * z a.2 - c) ^ 2)
      = fun z => z a.1 * z a.2 * z a.1 * z a.2 - (2 * c) * (z a.1 * z a.2) + c ^ 2 := by
    funext z; ring
  rw [e]
  exact ((bf_gfour _ _ _ _).sub ((bf_gtwo _ _).const_mul _)).add (integrable_const _)

private lemma bf_aem {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) : AEMeasurable X P := by
  by_contra hne
  have h0 := Measure.map_of_not_aemeasurable_of_ne_zero hne (IsProbabilityMeasure.ne_zero P)
  have hd := hX.symm.trans h0
  obtain ⟨x0, hd⟩ : ∃ x0 : Vec m × Vec n, gaussPair m n = Measure.dirac x0 := ⟨_, hd⟩
  have key : ∀ c : Vec m × Vec n → ℝ, Measurable c →
      (gaussPair m n).map c = gaussianReal 0 1 → False := by
    intro c hc hmap
    have h1 : (gaussPair m n).map c {c x0} = 1 := by
      rw [Measure.map_apply hc (measurableSet_singleton _), hd, Measure.dirac_apply' _
        (hc (measurableSet_singleton _))]
      simp
    rw [hmap] at h1
    have := noAtoms_gaussianReal (μ := 0) (v := 1) one_ne_zero
    rw [measure_singleton] at h1
    exact zero_ne_one h1
  have hfst : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  have hsnd : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  rcases Nat.eq_zero_or_pos m with hm | hm
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hm; subst hn
      exact hne (measurable_of_subsingleton_codomain X).aemeasurable
    · refine key (fun x => x.2 ⟨0, hn⟩) ((measurable_pi_apply _).comp measurable_snd) ?_
      have := Muon.Foundations.stdGaussianPi_map_coord n ⟨0, hn⟩
      rw [← this, ← hsnd, Measure.map_map (measurable_pi_apply _) measurable_snd]
      rfl
  · refine key (fun x => x.1 ⟨0, hm⟩) ((measurable_pi_apply _).comp measurable_fst) ?_
    have := Muon.Foundations.stdGaussianPi_map_coord m ⟨0, hm⟩
    rw [← this, ← hfst, Measure.map_map (measurable_pi_apply _) measurable_fst]
    rfl

private lemma bf_sq_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d) (a : Fin d × Fin d) :
    MemLp (fun w => (π (X w)) a.1 * (π (X w)) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 P := by
  have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (Measure.map π (gaussPair m n)) := by rw [hmap]; exact bf_gsq_memLp d a
  have h2 := h1.comp_of_map hπ.aemeasurable
  have hg : MemLp (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact h2
  exact hg.comp_of_map (bf_aem P X hX)

end BfCopies

/-- Conditional expectation of a finite weighted sum of integrable functions. -/
private lemma bf_condExp_sum {ι : Type*} [Fintype ι] (P : Measure Ω) (G : MeasurableSpace Ω)
    (g : ι → Ω → ℝ) (hg : ∀ i, Integrable (g i) P) (c : ι → ℝ) :
    condExp G P (fun ω => ∑ i, c i * g i ω) =ᵐ[P] fun ζ => ∑ i, c i * condExp G P (g i) ζ := by
  have h1 : (fun ω => ∑ i, c i * g i ω) = ∑ i, c i • g i := by
    funext ω; simp [Finset.sum_apply]
  rw [h1]
  refine (condExp_finsetSum (fun i _ => (hg i).smul (c i)) G).trans ?_
  have hall : ∀ᵐ ζ ∂P, ∀ i, condExp G P (c i • g i) ζ = (c i • condExp G P (g i)) ζ :=
    ae_all_iff.2 fun i => condExp_smul (c i) (g i) G
  filter_upwards [hall] with ζ hζ
  simp [Finset.sum_apply, hζ]

private lemma bf_memLp_sq_fst {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin m) :
    MemLp (fun ω => (X ω).1 a * (X ω).1 b - (1 : Mat m m) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  exact bf_sq_memLp P X hX Prod.fst measurable_fst hmap (a, b)

private lemma bf_memLp_sq_snd {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin n) :
    MemLp (fun ω => (X ω).2 a * (X ω).2 b - (1 : Mat n n) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  exact bf_sq_memLp P X hX Prod.snd measurable_snd hmap (a, b)

private lemma bf_memLp_cross {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => (X ω).1 a * (X ω).2 b) 2 P := by
  have hg : MemLp (fun x : Vec m × Vec n => x.1 a * x.2 b) 2
      (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact bf_gfam1_memLp m n (a, b)
  exact hg.comp_of_map (bf_aem P X hX)

private lemma bf_integrable_mul {f g : Ω → ℝ} {P : Measure Ω} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

open scoped Matrix.Norms.Frobenius in
private lemma bf_fro_add {k l : ℕ} (A B' : Mat k l) : fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

open scoped Matrix.Norms.Frobenius in
private lemma bf_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma bf_pt_sym {d : ℕ} (s : ℝ) (R : Mat d d) (ξ u : Vec d) (hu : u = s • R *ᵥ ξ) (e : ℝ)
    (i k : Fin d) :
    (e • Muon.outer u u) i k =
      (∑ p : Fin d × Fin d, (s ^ 2 * R i p.1 * R k p.2) *
          ((ξ p.1 * ξ p.2 - (1 : Mat d d) p.1 p.2) * e)) + (s ^ 2 * ∑ a, R i a * R k a) * e := by
  subst hu
  simp only [Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  have h1 : ∀ a b : Fin d, s ^ 2 * R i a * R k b * ((ξ a * ξ b - (1 : Mat d d) a b) * e)
      = s ^ 2 * R i a * R k b * (ξ a * ξ b * e) - (if a = b then s ^ 2 * R i a * R k b * e else 0) := by
    intro a b
    by_cases h : a = b <;> simp [Matrix.one_apply, h] <;> ring
  simp only [h1, Finset.sum_sub_distrib]
  have h2 : ∑ a, ∑ b, (if a = b then s ^ 2 * R i a * R k b * e else 0) = ∑ a, s ^ 2 * R i a * R k a * e := by
    refine Finset.sum_congr rfl fun a _ => ?_
    simp
  have h4 : (s ^ 2 * ∑ a, R i a * R k a) * e = ∑ a, s ^ 2 * R i a * R k a * e := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h5 : e * ((s * ∑ a, R i a * ξ a) * (s * ∑ b, R k b * ξ b))
      = ∑ a, ∑ b, s ^ 2 * R i a * R k b * (ξ a * ξ b * e) := by
    rw [mul_mul_mul_comm, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h2, h4, h5, sub_add_cancel]

private lemma bf_pt_cross {d1 d2 : ℕ} (s : ℝ) (R : Mat d1 d1) (S : Mat d2 d2) (ξ : Vec d1)
    (η : Vec d2) (u : Vec d1) (v : Vec d2) (hu : u = s • R *ᵥ ξ) (hv : v = s • S *ᵥ η) (e : ℝ)
    (i : Fin d1) (l : Fin d2) :
    (e • Muon.outer u v) i l =
      ∑ p : Fin d1 × Fin d2, (s ^ 2 * R i p.1 * S l p.2) * ((ξ p.1 * η p.2) * e) := by
  subst hu hv
  simp only [Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply,
    Matrix.mulVec, dotProduct, Fintype.sum_prod_type]
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

private lemma bf_sym (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) {d B : ℕ} (hB : 0 < B) (R : Mat d d) (CS γ : ℝ)
    (hR : opNorm R * opNorm R ≤ CS) (hdim : (d : ℝ) ≤ γ * B)
    (ξ u : Ω → Vec d) (hu : ∀ ω, u ω = (Real.sqrt B)⁻¹ • R *ᵥ ξ ω)
    (e : Ω → ℝ) (he2 : MemLp e 2 P)
    (hint : ∀ a b, Integrable (fun ω => (ξ ω a * ξ ω b - (1 : Mat d d) a b) * e ω) P)
    (hbes : ∀ᵐ ζ ∂P, Real.sqrt (∑ a, ∑ b, ‖condExp G P
        (fun ω => (ξ ω a * ξ ω b - (1 : Mat d d) a b) * e ω) ζ‖ ^ 2) ≤
        Real.sqrt 2 * Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ)) :
    ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P
        (fun ω => e ω • Muon.outer (u ω) (u ω)) ζ) ≤
      CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) := by
  set s : ℝ := (Real.sqrt B)⁻¹ with hs
  have hs2 : s ^ 2 = 1 / B := by
    rw [hs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  have heI : Integrable e P := he2.integrable one_le_two
  set g : Fin d × Fin d → Ω → ℝ := fun p ω => (ξ ω p.1 * ξ ω p.2 - (1 : Mat d d) p.1 p.2) * e ω
    with hg_def
  have hg : ∀ p, Integrable (g p) P := fun p => hint p.1 p.2
  set K : Fin d → Fin d → ℝ := fun i k => s ^ 2 * ∑ a, R i a * R k a with hK
  have hent : ∀ i k, ∀ᵐ ζ ∂P, condExp G P (fun ω => (e ω • Muon.outer (u ω) (u ω)) i k) ζ =
      (∑ p, (s ^ 2 * R i p.1 * R k p.2) * condExp G P (g p) ζ) + K i k * condExp G P e ζ := by
    intro i k
    have hfun : (fun ω => (e ω • Muon.outer (u ω) (u ω)) i k) =
        (fun ω => ∑ p, (s ^ 2 * R i p.1 * R k p.2) * g p ω) + (fun ω => K i k * e ω) := by
      funext ω
      simp only [Pi.add_apply]
      exact bf_pt_sym s R (ξ ω) (u ω) (hu ω) (e ω) i k
    have h1 := bf_condExp_sum (mΩ := mΩ) P G g hg (fun p => s ^ 2 * R i p.1 * R k p.2)
    have hI1 : Integrable (fun ω => ∑ p, (s ^ 2 * R i p.1 * R k p.2) * g p ω) P :=
      integrable_finsetSum _ fun p _ => (hg p).const_mul _
    have hI2 : Integrable (fun ω => K i k * e ω) P := heI.const_mul _
    have h2 := condExp_add hI1 hI2 G
    have h3 : condExp G P (K i k • e) =ᵐ[P] K i k • condExp G P e := condExp_smul (K i k) e G
    rw [hfun]
    filter_upwards [h1, h2, h3] with ζ a1 a2 a3
    rw [a2]
    simp only [Pi.add_apply]
    rw [a1]
    simp only [Pi.smul_apply, smul_eq_mul] at a3
    rw [show condExp G P (fun ω => K i k * e ω) ζ = K i k * condExp G P e ζ from a3]
  have hall := ae_all_iff.2 fun i => ae_all_iff.2 fun k => hent i k
  filter_upwards [hall, hbes, bf_jensen_sq (mΩ := mΩ) P G hG e he2] with ζ hζ hb hj
  set T : Mat d d := Matrix.of fun a b => condExp G P (g (a, b)) ζ with hT
  set c := condExp G P e ζ with hc
  have hmat : Muon.Foundations.condExpMat G P (fun ω => e ω • Muon.outer (u ω) (u ω)) ζ =
      s ^ 2 • (R * T * Rᵀ) + (s ^ 2 * c) • (R * Rᵀ) := by
    ext i k
    rw [Muon.Foundations.condExpMat_apply, hζ i k]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, hK, hT, Matrix.of_apply, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    congr 1
    · exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
    · exact Finset.sum_congr rfl fun a _ => by ring
  rw [hmat]
  have hCS : 0 ≤ CS := le_trans (mul_self_nonneg _) hR
  have hq0 : 0 ≤ Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) := Real.sqrt_nonneg _
  set q := Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) with hq
  have hTb : fro T ≤ Real.sqrt 2 * q := by
    simp only [Real.norm_eq_abs, sq_abs] at hb
    unfold fro
    simpa only [Real.norm_eq_abs, sq_abs, hT, Matrix.of_apply] using hb
  have hcq : |c| ≤ q := Real.abs_le_sqrt hj
  have ho : 0 ≤ opNorm R := bf_opNorm_nonneg R
  have hR1 : fro (R * T * Rᵀ) ≤ opNorm R * fro T * opNorm R := by
    calc fro (R * T * Rᵀ) ≤ fro (R * T) * opNorm Rᵀ := bf_fro_mul_le_right _ _
      _ ≤ (opNorm R * fro T) * opNorm R := by
        rw [bf_opNorm_transpose]
        exact mul_le_mul_of_nonneg_right (bf_fro_mul_le_left _ _) ho
  have hR2 : fro (R * Rᵀ) ≤ Real.sqrt d * (opNorm R * opNorm R) := by
    calc fro (R * Rᵀ) ≤ Real.sqrt d * opNorm (R * Rᵀ) := bf_fro_le_sqrt_mul_opNorm _
      _ ≤ Real.sqrt d * (opNorm R * opNorm Rᵀ) :=
        mul_le_mul_of_nonneg_left (bf_opNorm_mul_le _ _) (Real.sqrt_nonneg _)
      _ = _ := by rw [bf_opNorm_transpose]
  have hsd : Real.sqrt d ≤ Real.sqrt (γ * B) := Real.sqrt_le_sqrt hdim
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg _
  have hfT : 0 ≤ fro T := bf_fro_nonneg _
  have hRR : 0 ≤ opNorm R * opNorm R := mul_self_nonneg _
  calc fro (s ^ 2 • (R * T * Rᵀ) + (s ^ 2 * c) • (R * Rᵀ))
      ≤ fro (s ^ 2 • (R * T * Rᵀ)) + fro ((s ^ 2 * c) • (R * Rᵀ)) := bf_fro_add _ _
    _ = s ^ 2 * fro (R * T * Rᵀ) + s ^ 2 * |c| * fro (R * Rᵀ) := by
        rw [bf_fro_smul, bf_fro_smul, abs_of_nonneg hs0, abs_mul, abs_of_nonneg hs0]
    _ ≤ s ^ 2 * (opNorm R * fro T * opNorm R) +
          s ^ 2 * |c| * (Real.sqrt d * (opNorm R * opNorm R)) := by
        gcongr
    _ ≤ s ^ 2 * (CS * (Real.sqrt 2 * q)) + s ^ 2 * q * (Real.sqrt (γ * B) * CS) := by
        have h1 : opNorm R * fro T * opNorm R = (opNorm R * opNorm R) * fro T := by ring
        have h2 : (opNorm R * opNorm R) * fro T ≤ CS * (Real.sqrt 2 * q) :=
          mul_le_mul hR hTb hfT hCS
        have h3 : |c| * (Real.sqrt d * (opNorm R * opNorm R)) ≤ q * (Real.sqrt (γ * B) * CS) :=
          mul_le_mul hcq (mul_le_mul hsd hR hRR (Real.sqrt_nonneg _)) (by positivity) hq0
        rw [h1]
        nlinarith [mul_le_mul_of_nonneg_left h2 hs0, mul_le_mul_of_nonneg_left h3 hs0]
    _ = CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * q := by
        rw [hs2]; field_simp

private lemma bf_cross (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) {d1 d2 B : ℕ} (hB : 0 < B) (R : Mat d1 d1) (S : Mat d2 d2) (CS : ℝ)
    (hRS : opNorm R * opNorm S ≤ CS)
    (ξ u : Ω → Vec d1) (η v : Ω → Vec d2)
    (hu : ∀ ω, u ω = (Real.sqrt B)⁻¹ • R *ᵥ ξ ω) (hv : ∀ ω, v ω = (Real.sqrt B)⁻¹ • S *ᵥ η ω)
    (e : Ω → ℝ)
    (hint : ∀ a b, Integrable (fun ω => (ξ ω a * η ω b) * e ω) P)
    (hbes : ∀ᵐ ζ ∂P, Real.sqrt (∑ a, ∑ b, ‖condExp G P
        (fun ω => (ξ ω a * η ω b) * e ω) ζ‖ ^ 2) ≤
        Real.sqrt (condExp G P (fun ω => ‖e ω‖ ^ 2) ζ)) :
    ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P
        (fun ω => e ω • Muon.outer (u ω) (v ω)) ζ) ≤
      CS / B * Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) := by
  set s : ℝ := (Real.sqrt B)⁻¹ with hs
  have hs2 : s ^ 2 = 1 / B := by
    rw [hs, inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  set g : Fin d1 × Fin d2 → Ω → ℝ := fun p ω => (ξ ω p.1 * η ω p.2) * e ω with hg_def
  have hg : ∀ p, Integrable (g p) P := fun p => hint p.1 p.2
  have hent : ∀ i l, ∀ᵐ ζ ∂P, condExp G P (fun ω => (e ω • Muon.outer (u ω) (v ω)) i l) ζ =
      ∑ p, (s ^ 2 * R i p.1 * S l p.2) * condExp G P (g p) ζ := by
    intro i l
    have hfun : (fun ω => (e ω • Muon.outer (u ω) (v ω)) i l) =
        (fun ω => ∑ p, (s ^ 2 * R i p.1 * S l p.2) * g p ω) := by
      funext ω
      exact bf_pt_cross s R S (ξ ω) (η ω) (u ω) (v ω) (hu ω) (hv ω) (e ω) i l
    rw [hfun]
    exact bf_condExp_sum (mΩ := mΩ) P G g hg (fun p => s ^ 2 * R i p.1 * S l p.2)
  have hall := ae_all_iff.2 fun i => ae_all_iff.2 fun l => hent i l
  filter_upwards [hall, hbes] with ζ hζ hb
  set T : Mat d1 d2 := Matrix.of fun a b => condExp G P (g (a, b)) ζ with hT
  have hmat : Muon.Foundations.condExpMat G P (fun ω => e ω • Muon.outer (u ω) (v ω)) ζ =
      s ^ 2 • (R * T * Sᵀ) := by
    ext i l
    rw [Muon.Foundations.condExpMat_apply, hζ i l]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, hT, Matrix.of_apply, Fintype.sum_prod_type, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  rw [hmat]
  have hCS : 0 ≤ CS := le_trans (mul_nonneg (bf_opNorm_nonneg R) (bf_opNorm_nonneg S)) hRS
  have hq0 : 0 ≤ Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) := Real.sqrt_nonneg _
  set q := Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) with hq
  have hTb : fro T ≤ q := by
    simp only [Real.norm_eq_abs, sq_abs] at hb
    unfold fro
    simpa only [Real.norm_eq_abs, sq_abs, hT, Matrix.of_apply] using hb
  have hfT : 0 ≤ fro T := bf_fro_nonneg _
  have hs0 : 0 ≤ s ^ 2 := sq_nonneg _
  have hR1 : fro (R * T * Sᵀ) ≤ opNorm R * fro T * opNorm S := by
    calc fro (R * T * Sᵀ) ≤ fro (R * T) * opNorm Sᵀ := bf_fro_mul_le_right _ _
      _ ≤ (opNorm R * fro T) * opNorm S := by
        rw [bf_opNorm_transpose]
        exact mul_le_mul_of_nonneg_right (bf_fro_mul_le_left _ _) (bf_opNorm_nonneg S)
  calc fro (s ^ 2 • (R * T * Sᵀ)) = s ^ 2 * fro (R * T * Sᵀ) := by
        rw [bf_fro_smul, abs_of_nonneg hs0]
    _ ≤ s ^ 2 * (opNorm R * fro T * opNorm S) := mul_le_mul_of_nonneg_left hR1 hs0
    _ ≤ s ^ 2 * (CS * q) := by
        refine mul_le_mul_of_nonneg_left ?_ hs0
        have h1 : opNorm R * fro T * opNorm S = (opNorm R * opNorm S) * fro T := by ring
        rw [h1]
        exact mul_le_mul hRS hTb hfT hCS
    _ = CS / B * q := by rw [hs2]; field_simp

/-! ## Helper: conditional Bessel bounds for rank-one tensors (`eqn:app-drift-bessel-frob`)

The three displayed bounds of `eqn:app-drift-bessel-frob`, for a scalar `e` that is measurable
with respect to `σ(X) ⊔ 𝒢` and square integrable. `X = (z, w)` is the Gaussian pair, `u = momU`,
`v = momV`, and `‖e‖_{2,𝒢} = (E_𝒢 e²)^{1/2}` is written `Real.sqrt (condExp 𝒢 P (e²) ζ)`. -/

/-- `eqn:app-drift-bessel-frob`, first bound. Snapshot `cr-2026-10-23`. LaTeX (`section.tex`
l.355–361, verbatim):
\begin{equation}\label{eqn:app-drift-bessel-frob}
\begin{gathered}
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma(\sqrt2+\sqrt{\gamma_\star B})}{B}\norm e_{2,\mathcal G}\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\\
\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf v)e]\big\|_\F\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\qquad
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf v)e]\big\|_\F=\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma\norm e_{2,\mathcal G}}{B}.
\end{gathered}
\end{equation}
-/
theorem bessel_frob_uu {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (CS γ : ℝ) (hB : 0 < B) (hS : opNorm C.Sout ≤ CS) (hdim : (m : ℝ) ≤ γ * B)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → ℝ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      fro (Muon.Foundations.condExpMat G P (fun ω' => e ω' • Muon.outer (momU C B (X ω')) (momU C B (X ω'))) ζ) ≤
        CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * Real.sqrt (condExp G P (fun ω' => e ω' ^ 2) ζ) := by
  have hR : opNorm (rOut C) * opNorm (rOut C) ≤ CS := (bf_opNorm_rOut_mul_self C).le.trans hS
  refine bf_sym (mΩ := mΩ) P G hG hB (rOut C) CS γ hR hdim (fun ω => (X ω).1) (fun ω => momU C B (X ω))
    (fun ω => rfl) e he2 (fun a b => bf_integrable_mul (mΩ := mΩ) (bf_memLp_sq_fst (mΩ := mΩ) P X hX a b) he2) ?_
  filter_upwards [lem_app_de_bessel_ii (𝕜 := ℝ) (mΩ := mΩ) P X hX G hG hind e he he2] with ζ hζ
  simpa using hζ

/-- `eqn:app-drift-bessel-frob`, second bound (input side, `v⊗v`). Snapshot `cr-2026-10-23`.
LaTeX (`section.tex` l.355–361, verbatim):
\begin{equation}\label{eqn:app-drift-bessel-frob}
\begin{gathered}
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma(\sqrt2+\sqrt{\gamma_\star B})}{B}\norm e_{2,\mathcal G}\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\\
\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf v)e]\big\|_\F\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\qquad
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf v)e]\big\|_\F=\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma\norm e_{2,\mathcal G}}{B}.
\end{gathered}
\end{equation}
-/
theorem bessel_frob_vv {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (CS γ : ℝ) (hB : 0 < B) (hS : opNorm C.Sin ≤ CS) (hdim : (n : ℝ) ≤ γ * B)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → ℝ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      fro (Muon.Foundations.condExpMat G P (fun ω' => e ω' • Muon.outer (momV C B (X ω')) (momV C B (X ω'))) ζ) ≤
        CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * Real.sqrt (condExp G P (fun ω' => e ω' ^ 2) ζ) := by
  have hR : opNorm (rIn C) * opNorm (rIn C) ≤ CS := (bf_opNorm_rIn_mul_self C).le.trans hS
  refine bf_sym (mΩ := mΩ) P G hG hB (rIn C) CS γ hR hdim (fun ω => (X ω).2) (fun ω => momV C B (X ω))
    (fun ω => rfl) e he2 (fun a b => bf_integrable_mul (mΩ := mΩ) (bf_memLp_sq_snd (mΩ := mΩ) P X hX a b) he2) ?_
  filter_upwards [lem_app_de_bessel_iii (𝕜 := ℝ) (mΩ := mΩ) P X hX G hG hind e he he2] with ζ hζ
  simpa using hζ

/-- `eqn:app-drift-bessel-frob`, third bound (cross term `u⊗v`, equal to `v⊗u` after transposition).
Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.355–361, verbatim):
\begin{equation}\label{eqn:app-drift-bessel-frob}
\begin{gathered}
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma(\sqrt2+\sqrt{\gamma_\star B})}{B}\norm e_{2,\mathcal G}\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\\
\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf v)e]\big\|_\F\le\frac{C\norm e_{2,\mathcal G}}{\sqrt B},\qquad
\big\|\EE_{\mathcal G}[(\mathsf u\tensor\mathsf v)e]\big\|_\F=\big\|\EE_{\mathcal G}[(\mathsf v\tensor\mathsf u)e]\big\|_\F\le\frac{C_\Sigma\norm e_{2,\mathcal G}}{B}.
\end{gathered}
\end{equation}
-/
theorem bessel_frob_uv {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (CS : ℝ) (hB : 0 < B) (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (e : Ω → ℝ) (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e)
    (he2 : MemLp e 2 P) :
    ∀ᵐ ζ ∂P,
      fro (Muon.Foundations.condExpMat G P (fun ω' => e ω' • Muon.outer (momU C B (X ω')) (momV C B (X ω'))) ζ) ≤
        CS / B * Real.sqrt (condExp G P (fun ω' => e ω' ^ 2) ζ) ∧
      fro (Muon.Foundations.condExpMat G P (fun ω' => e ω' • Muon.outer (momV C B (X ω')) (momU C B (X ω'))) ζ) ≤
        CS / B * Real.sqrt (condExp G P (fun ω' => e ω' ^ 2) ζ) := by
  have h1 := bf_opNorm_rOut_mul_self C
  have h2 := bf_opNorm_rIn_mul_self C
  have ho1 := bf_opNorm_nonneg (rOut C)
  have ho2 := bf_opNorm_nonneg (rIn C)
  have hR : opNorm (rOut C) * opNorm (rIn C) ≤ CS := by
    nlinarith [sq_nonneg (opNorm (rOut C) - opNorm (rIn C))]
  have hR' : opNorm (rIn C) * opNorm (rOut C) ≤ CS := by rw [mul_comm]; exact hR
  have hbes := lem_app_de_bessel_i (𝕜 := ℝ) (mΩ := mΩ) P X hX G hG hind e he he2
  have hint : ∀ a b, Integrable (fun ω => ((X ω).1 a * (X ω).2 b) * e ω) P := fun a b =>
    bf_integrable_mul (mΩ := mΩ) (bf_memLp_cross (mΩ := mΩ) P X hX a b) he2
  refine ?_
  have hA := bf_cross (mΩ := mΩ) P G hB (rOut C) (rIn C) CS hR (fun ω => (X ω).1) (fun ω => momU C B (X ω))
    (fun ω => (X ω).2) (fun ω => momV C B (X ω)) (fun ω => rfl) (fun ω => rfl) e hint
    (by filter_upwards [hbes] with ζ hζ; simpa using hζ)
  have hB' := bf_cross (mΩ := mΩ) P G hB (rIn C) (rOut C) CS hR' (fun ω => (X ω).2)
    (fun ω => momV C B (X ω)) (fun ω => (X ω).1) (fun ω => momU C B (X ω)) (fun ω => rfl)
    (fun ω => rfl) e
    (fun b a => by
      have := hint a b
      simpa only [mul_comm ((X _).2 b)] using this)
    (by
      filter_upwards [hbes] with ζ hζ
      have e1 : ∀ b a, (fun ω => ((X ω).2 b * (X ω).1 a) * e ω) =
          fun ω => ((X ω).1 a * (X ω).2 b) * e ω := fun b a => by funext ω; ring
      simp only [e1]
      rw [Finset.sum_comm]
      simpa using hζ)
  filter_upwards [hA, hB'] with ζ h1 h2
  exact ⟨h1, h2⟩

/-! ## Helper: the coefficient difference (`eqn:app-drift-delta-alpha`)

Pure algebra over `ℝ`: the difference of `α₂` for two deleted matrices with the same sample, and
the difference of the Gram denominators `Λ`. `s > 0` makes `Λ > 0` (`lem_app_de_deletion`), so the
divisions are the genuine ones. -/

/-- `eqn:app-drift-delta-alpha`. Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.453–456,
verbatim):
\begin{equation}\label{eqn:app-drift-delta-alpha}
\alpha_2-\alpha_2'=\mathsf h^2\Big[\frac{\delta\mathsf U}{\Lambda}-\frac{\mathsf U'\,(\Lambda-\Lambda')}{\Lambda\Lambda'}\Big],\qquad
\Lambda-\Lambda'=\mathsf h\,\delta\mathsf C\,\big(2+\mathsf h(\mathsf C+\mathsf C')\big)+s\mathsf h^2\big(\mathsf V\,\delta\mathsf U+\mathsf U'\,\delta\mathsf V\big).
\end{equation}
-/
theorem delta_alpha {m n : ℕ} (K K' : Mat m n) (h s : ℝ) (u : Vec m) (v : Vec n) (hs : 0 < s) :
    Muon.DetEquiv.alpha2 K h u v s - Muon.DetEquiv.alpha2 K' h u v s =
        h ^ 2 * ((Muon.DetEquiv.delU K u s - Muon.DetEquiv.delU K' u s) /
            Muon.DetEquiv.delLambda K h u v s
          - Muon.DetEquiv.delU K' u s *
              (Muon.DetEquiv.delLambda K h u v s - Muon.DetEquiv.delLambda K' h u v s) /
            (Muon.DetEquiv.delLambda K h u v s * Muon.DetEquiv.delLambda K' h u v s)) ∧
      Muon.DetEquiv.delLambda K h u v s - Muon.DetEquiv.delLambda K' h u v s =
        h * (Muon.DetEquiv.delC K u v s - Muon.DetEquiv.delC K' u v s) *
            (2 + h * (Muon.DetEquiv.delC K u v s + Muon.DetEquiv.delC K' u v s)) +
          s * h ^ 2 * (Muon.DetEquiv.delV K v s * (Muon.DetEquiv.delU K u s - Muon.DetEquiv.delU K' u s) +
            Muon.DetEquiv.delU K' u s * (Muon.DetEquiv.delV K v s - Muon.DetEquiv.delV K' v s)) := by
  have hL : 0 < Muon.DetEquiv.delLambda K h u v s :=
    (Muon.DetEquiv.lem_app_de_deletion K h u v (K + h • Muon.outer u v) s rfl hs).1
  have hL' : 0 < Muon.DetEquiv.delLambda K' h u v s :=
    (Muon.DetEquiv.lem_app_de_deletion K' h u v (K' + h • Muon.outer u v) s rfl hs).1
  refine ⟨?_, ?_⟩
  · unfold Muon.DetEquiv.alpha2
    field_simp [hL.ne', hL'.ne']
    ring
  · unfold Muon.DetEquiv.delLambda
    ring

/-! ## Helpers for `phiFresh_integrable` (proved; not statements) -/

private lemma pf_sqNorm_nonneg {k : ℕ} (x : Vec k) : 0 ≤ sqNorm x := by
  unfold sqNorm; exact Finset.sum_nonneg fun i _ => sq_nonneg _

private lemma pf_eucNorm_sq {k : ℕ} (z : Vec k) : eucNorm z ^ 2 = sqNorm z := by
  unfold eucNorm sqNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

open scoped Matrix.Norms.L2Operator in
private lemma pf_mulVec_sq_le {m : ℕ} (R : Mat m m) (u : Vec m) :
    sqNorm (R *ᵥ u) ≤ opNorm R ^ 2 * sqNorm u := by
  unfold sqNorm
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin m), ∀ k, v.ofLp k = u k :=
    ⟨(EuclideanSpace.equiv (Fin m) ℝ).symm u, fun k => rfl⟩
  have h1 : ‖(EuclideanSpace.equiv (Fin m) ℝ).symm (R *ᵥ v)‖ ≤ opNorm R * ‖v‖ := by
    rw [opNorm_eq_norm]
    exact Matrix.l2_opNorm_mulVec R v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
  have e1 : ∀ i, ((EuclideanSpace.equiv (Fin m) ℝ).symm (R *ᵥ v)).ofLp i = (R *ᵥ u) i := by
    intro i
    simp [Matrix.mulVec, dotProduct, hv]
  have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, u k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [hv]
  simp only [e1, e2] at h2
  exact h2

open scoped Matrix.Norms.L2Operator in
private lemma pf_quad_le {m : ℕ} (R : Mat m m) (u : Vec m) :
    |dotProduct u (R *ᵥ u)| ≤ opNorm R * sqNorm u := by
  have hcs : (dotProduct u (R *ᵥ u)) ^ 2 ≤ sqNorm u * sqNorm (R *ᵥ u) := by
    unfold dotProduct sqNorm
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hw := pf_mulVec_sq_le R u
  have hon : 0 ≤ opNorm R := by unfold opNorm; exact norm_nonneg _
  have hsn := pf_sqNorm_nonneg u
  have key : (dotProduct u (R *ᵥ u)) ^ 2 ≤ (opNorm R * sqNorm u) ^ 2 := by
    calc _ ≤ sqNorm u * sqNorm (R *ᵥ u) := hcs
      _ ≤ sqNorm u * (opNorm R ^ 2 * sqNorm u) := mul_le_mul_of_nonneg_left hw hsn
      _ = (opNorm R * sqNorm u) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg hon hsn) two_ne_zero).mp
    (by rw [sq_abs]; exact key)

private lemma pf_alpha2_bound {m n : ℕ} (K : Mat m n) (h s : ℝ) (u : Vec m) (v : Vec n)
    (hs : 0 < s) :
    |Muon.DetEquiv.alpha2 K h u v s| ≤
      h ^ 2 * (sqNorm u / s) * (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm u + sqNorm v)) ^ 2 := by
  obtain ⟨hpos, -, -, -, hinv⟩ :=
    Muon.DetEquiv.lem_app_de_deletion K h u v (K + h • Muon.outer u v) s rfl hs
  have hUb : |Muon.DetEquiv.delU K u s| ≤ sqNorm u / s := by
    have hq := pf_quad_le (Muon.DetEquiv.Rs K s) u
    have hop := (Muon.DetEquiv.lem_app_de_resolvent K s hs).1
    have hq' : |Muon.DetEquiv.delU K u s| ≤ opNorm (Muon.DetEquiv.Rs K s) * sqNorm u := hq
    calc _ ≤ _ := hq'
      _ ≤ (1 / s) * sqNorm u := mul_le_mul_of_nonneg_right hop (pf_sqNorm_nonneg u)
      _ = sqNorm u / s := by ring
  unfold Muon.DetEquiv.alpha2
  calc |h ^ 2 * Muon.DetEquiv.delU K u s / Muon.DetEquiv.delLambda K h u v s|
      = (h ^ 2 * |Muon.DetEquiv.delU K u s|) * (Muon.DetEquiv.delLambda K h u v s)⁻¹ := by
        rw [abs_div, abs_of_pos hpos, abs_mul, abs_of_nonneg (sq_nonneg h), div_eq_mul_inv]
    _ ≤ (h ^ 2 * (sqNorm u / s)) *
          (1 + 3 / (4 * Real.sqrt s) * |h| * (sqNorm u + sqNorm v)) ^ 2 :=
        mul_le_mul (mul_le_mul_of_nonneg_left hUb (sq_nonneg h)) hinv (inv_nonneg.2 hpos.le)
          (mul_nonneg (sq_nonneg h) (div_nonneg (pf_sqNorm_nonneg u) hs.le))

private lemma pf_scal (h S T s c : ℝ) (hs : 0 < s) (_hc : 0 ≤ c) (hS : 0 ≤ S) (_hT : 0 ≤ T)
    (hTS : T ≤ S) :
    h ^ 2 * (T / s) * (1 + c * |h| * S) ^ 2 ≤ ((h ^ 4 + S ^ 2) + c ^ 2 * (h ^ 8 + S ^ 6)) / s := by
  have hy : (c * |h| * S) ^ 2 = c ^ 2 * h ^ 2 * S ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
  have h1 : (1 + c * |h| * S) ^ 2 ≤ 2 + 2 * c ^ 2 * h ^ 2 * S ^ 2 := by
    nlinarith [sq_nonneg (1 - c * |h| * S), hy]
  have h2 : h ^ 2 * (T / s) ≤ h ^ 2 * (S / s) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hTS hs.le) (sq_nonneg h)
  have h3 : h ^ 2 * (T / s) * (1 + c * |h| * S) ^ 2 ≤
      h ^ 2 * (S / s) * (2 + 2 * c ^ 2 * h ^ 2 * S ^ 2) :=
    mul_le_mul h2 h1 (sq_nonneg _) (mul_nonneg (sq_nonneg h) (div_nonneg hS hs.le))
  have h4 : h ^ 2 * (S / s) * (2 + 2 * c ^ 2 * h ^ 2 * S ^ 2) =
      (2 * h ^ 2 * S + 2 * c ^ 2 * h ^ 4 * S ^ 3) / s := by
    field_simp
  have h5 : 2 * h ^ 2 * S + 2 * c ^ 2 * h ^ 4 * S ^ 3 ≤ (h ^ 4 + S ^ 2) + c ^ 2 * (h ^ 8 + S ^ 6) := by
    nlinarith [sq_nonneg (h ^ 2 - S), mul_nonneg (sq_nonneg c) (sq_nonneg (h ^ 4 - S ^ 3))]
  calc _ ≤ _ := h3
    _ = _ := h4
    _ ≤ _ := div_le_div_of_nonneg_right h5 hs.le

private lemma pf_alpha2_cont {m n : ℕ} (K : Mat m n) (s : ℝ) (hs : 0 < s) :
    Continuous (fun p : ℝ × Vec m × Vec n => Muon.DetEquiv.alpha2 K p.1 p.2.1 p.2.2 s) := by
  have hLc : Continuous (fun p : ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delLambda K p.1 p.2.1 p.2.2 s) := by
    simp only [Muon.DetEquiv.delLambda, Muon.DetEquiv.delC, Muon.DetEquiv.delU,
      Muon.DetEquiv.delV, dotProduct]
    fun_prop
  have hUc : Continuous (fun p : ℝ × Vec m × Vec n => Muon.DetEquiv.delU K p.2.1 s) := by
    simp only [Muon.DetEquiv.delU, dotProduct]
    fun_prop
  have hne : ∀ p : ℝ × Vec m × Vec n, Muon.DetEquiv.delLambda K p.1 p.2.1 p.2.2 s ≠ 0 :=
    fun p => (Muon.DetEquiv.lem_app_de_deletion K p.1 p.2.1 p.2.2
      (K + p.1 • Muon.outer p.2.1 p.2.2) s rfl hs).1.ne'
  exact ((continuous_fst.pow 2).mul hUc).div hLc hne

private lemma pf_even_pow_int {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {k : ℕ} (hk : Even k) (hk0 : k ≠ 0) (hf : MemLp f (k : ℝ≥0∞) μ) :
    Integrable (fun x => f x ^ k) μ :=
  (hf.integrable_norm_pow hk0).congr (Filter.Eventually.of_forall fun x => by
    dsimp only; rw [Real.norm_eq_abs]; exact hk.pow_abs (f x))

private lemma pf_memLp {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℝ}
    {p : ℝ≥0∞} (h : eLpNorm f p μ < ⊤) : MemLp f p μ :=
  h

/-! ## Integrability of the fresh-sample expectation (presupposed by `φ_ϖ`, `eqn:app-drift-phi`)

`φ_ϖ(K) = 𝔼 α₂` is written as a Bochner integral. This claim makes it a genuine integral (no
junk). It holds for every deterministic `K`, since `Λ > 0` and `0 ≤ 𝖴 ≤ ‖u‖²/s`. -/

/-- Integrability of the fresh-sample integrand of `φ_ϖ(K)` (`eqn:app-drift-phi`). -/
theorem phiFresh_integrable {m n B : ℕ} (F : FrozenParams m n B) (K : Mat m n) (ϖ s : ℝ)
    (hs : 0 < s) :
    Integrable (fun x : Vec m × Vec n =>
      Muon.DetEquiv.alpha2 K (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2)) (momU F.C B x)
        (momV F.C B x) s) (freshMeas m n) := by
  rw [show freshMeas m n = gaussPair m n from rfl]
  have hBr : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hDc : Continuous (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    fun_prop
  have hUc : Continuous (momU F.C B) := by unfold momU; fun_prop
  have hVc : Continuous (momV F.C B) := by unfold momV; fun_prop
  have hcont : Continuous (fun x : Vec m × Vec n =>
      Muon.DetEquiv.alpha2 K (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2))
        (momU F.C B x) (momV F.C B x) s) :=
    (pf_alpha2_cont K s hs).comp ((continuous_const.mul hDc).prodMk (hUc.prodMk hVc))
  have hSN : ∀ x : Vec m × Vec n,
      sqNorm (momU F.C B x) + sqNorm (momV F.C B x) = momN F.C B x := by
    intro x
    simp only [momN, pf_eucNorm_sq]
  have hmomN_cont : Continuous (fun x : Vec m × Vec n => momN F.C B x) := by
    have e : (fun x : Vec m × Vec n => momN F.C B x) =
        fun x => sqNorm (momU F.C B x) + sqNorm (momV F.C B x) :=
      funext fun x => (hSN x).symm
    rw [e]
    unfold sqNorm momU momV
    fun_prop
  obtain ⟨γ, hγ⟩ : ∃ γ : ℝ, γ = ((m : ℝ) + n) / B := ⟨_, rfl⟩
  have hdim : (m : ℝ) ≤ γ * B ∧ (n : ℝ) ≤ γ * B := by
    rw [hγ, div_mul_cancel₀ _ hBr.ne']
    exact ⟨by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)],
      by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]⟩
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact div_nonneg (by positivity) hBr.le
  have hmom := lem_app_de_moments_i F.C B γ
    (opNorm F.C.Sout + opNorm F.C.Sin) hdim
    ⟨by linarith [bf_opNorm_nonneg F.C.Sin], by linarith [bf_opNorm_nonneg F.C.Sout]⟩
  have hD4 : Integrable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2) ^ 4)
      (gaussPair m n) :=
    pf_even_pow_int (f := fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2))
      (by decide) (by norm_num)
      (pf_memLp (lt_of_le_of_lt (lem_app_de_moments_ii F.A F.hA 2 (by norm_num))
        ENNReal.ofReal_lt_top))
  have hD8 : Integrable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2) ^ 8)
      (gaussPair m n) :=
    pf_even_pow_int (f := fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2))
      (by decide) (by norm_num)
      (pf_memLp (lt_of_le_of_lt (lem_app_de_moments_ii F.A F.hA 4 (by norm_num))
        ENNReal.ofReal_lt_top))
  have hS2 : Integrable (fun x : Vec m × Vec n => momN F.C B x ^ 2) (gaussPair m n) :=
    pf_even_pow_int (f := fun x : Vec m × Vec n => momN F.C B x) (by decide) (by norm_num)
      (pf_memLp (lt_of_le_of_lt (hmom 2 (by norm_num))
        ENNReal.ofReal_lt_top))
  have hS6 : Integrable (fun x : Vec m × Vec n => momN F.C B x ^ 6) (gaussPair m n) :=
    pf_even_pow_int (f := fun x : Vec m × Vec n => momN F.C B x) (by decide) (by norm_num)
      (pf_memLp (lt_of_le_of_lt (hmom 6 (by norm_num))
        ENNReal.ofReal_lt_top))
  have h4 : Integrable (fun x : Vec m × Vec n => (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2)) ^ 4)
      (gaussPair m n) :=
    (hD4.const_mul (ϖ ^ 4)).congr (Filter.Eventually.of_forall fun x => by dsimp only; ring)
  have h8 : Integrable (fun x : Vec m × Vec n => (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2)) ^ 8)
      (gaussPair m n) :=
    (hD8.const_mul (ϖ ^ 8)).congr (Filter.Eventually.of_forall fun x => by dsimp only; ring)
  have hg := ((h4.add hS2).add ((h8.add hS6).const_mul ((3 / (4 * Real.sqrt s)) ^ 2))).div_const s
  refine Integrable.mono' hg hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  have hb := pf_alpha2_bound K (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2)) s
    (momU F.C B x) (momV F.C B x) hs
  have hsc := pf_scal (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2))
    (sqNorm (momU F.C B x) + sqNorm (momV F.C B x)) (sqNorm (momU F.C B x)) s
    (3 / (4 * Real.sqrt s)) hs (by positivity)
    (by linarith [pf_sqNorm_nonneg (momU F.C B x), pf_sqNorm_nonneg (momV F.C B x)])
    (pf_sqNorm_nonneg _)
    (by linarith [pf_sqNorm_nonneg (momV F.C B x)])
  rw [hSN x] at hb hsc
  exact le_trans hb hsc

/-! ## Helpers for `lem_app_drift_coeffmoments` (proved; not statements) -/

private lemma cm_cond {Ω' E : Type*} {G : MeasurableSpace Ω'} [mΩ' : MeasurableSpace Ω'] [MeasurableSpace E]
    {P : Measure Ω'} [IsProbabilityMeasure P] (hG : G ≤ mΩ')
    (X : Ω' → E) (hX : Measurable X)
    (hind : Indep G (MeasurableSpace.comap X inferInstance) P)
    (H : E → ℝ) (hH : Measurable H) (hHint : Integrable (fun ω => H (X ω)) P)
    (f : Ω' → ℝ) (hf : Measurable f) (c : ℝ) (hc : 0 ≤ c)
    (hf0 : ∀ ω, 0 ≤ f ω) (hfle : ∀ ω, f ω ≤ c * H (X ω)) :
    Integrable f P ∧ ∀ᵐ ω ∂P, condExp G P f ω ≤ c * ∫ ω', H (X ω') ∂P := by
  have hcH : Integrable (fun ω => c * H (X ω)) P := hHint.const_mul c
  have hfi : Integrable f P := by
    refine Integrable.mono' hcH hf.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ω)]
    exact hfle ω
  refine ⟨hfi, ?_⟩
  have h1 : condExp G P f ≤ᵐ[P] condExp G P (fun ω => c * H (X ω)) :=
    condExp_mono hfi hcH (Filter.Eventually.of_forall hfle)
  have h2 : condExp G P (fun ω => c * H (X ω)) =ᵐ[P] fun ω => c * condExp G P (fun ω' => H (X ω')) ω :=
    condExp_smul c (fun ω => H (X ω)) G
  have hmeas : StronglyMeasurable[MeasurableSpace.comap X inferInstance] (fun ω => H (X ω)) :=
    (hH.comp (comap_measurable X)).stronglyMeasurable
  have h3 : condExp G P (fun ω => H (X ω)) =ᵐ[P] fun _ => ∫ ω', H (X ω') ∂P :=
    condExp_indep_eq (hX.comap_le) hG hmeas hind.symm
  filter_upwards [h1, h2, h3] with ω a b d
  have d' : condExp G P (fun ω => H (X ω)) ω = ∫ ω', H (X ω') ∂P := d
  have b' : condExp G P (fun ω => c * H (X ω)) ω = c * condExp G P (fun ω => H (X ω)) ω := b
  calc condExp G P f ω ≤ condExp G P (fun ω => c * H (X ω)) ω := a
    _ = _ := by rw [b', d']

private lemma cm_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rs M s) := by
  rw [continuous_iff_continuousAt]
  intro M
  have hA : ∀ M : Mat m n, IsUnit (M * Mᵀ + s • (1 : Mat m m)).det := by
    intro M
    have h6 := (lem_app_de_resolvent M s hs).2.2.2.2.2.1
    have : Rs M s * (M * Mᵀ + s • (1 : Mat m m)) = 1 := by
      rw [Matrix.mul_add, h6, Matrix.mul_smul, Matrix.mul_one]
      abel
    exact Matrix.isUnit_det_of_left_inverse this
  have hcont : ContinuousAt (fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) M := by
    fun_prop
  have hdet : (M * Mᵀ + s • (1 : Mat m m)).det ≠ 0 := (hA M).ne_zero
  have hinv : ContinuousAt (Inv.inv : Mat m m → Mat m m) (M * Mᵀ + s • (1 : Mat m m)) := by
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  show ContinuousAt (fun M : Mat m n => (M * Mᵀ + s • (1 : Mat m m))⁻¹) M
  exact ContinuousAt.comp (g := fun A : Mat m m => A⁻¹)
    (f := fun M : Mat m n => M * Mᵀ + s • (1 : Mat m m)) hinv hcont

private lemma cm_Rts_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rts M s) := by
  have e : (fun M : Mat m n => Rts M s) = fun M => Rs Mᵀ s := by
    funext M; simp [Rts, Rs]
  rw [e]
  exact (cm_Rs_continuous s hs).comp continuous_id.matrix_transpose

private lemma cm_alpha_cont {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha1 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha2 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha3 q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
  have hR := cm_Rs_continuous (m := m) (n := n) s hs
  have hRt := cm_Rts_continuous (m := m) (n := n) s hs
  have hX : Continuous (fun M : Mat m n => Muon.DetEquiv.Xs M s) := by
    unfold Muon.DetEquiv.Xs; exact hR.matrix_mul continuous_id
  have hU : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delU q.1 q.2.2.1 s) := by
    simp only [Muon.DetEquiv.delU, dotProduct]
    fun_prop
  have hV : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delV q.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delV, dotProduct]
    fun_prop
  have hC : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delC q.1 q.2.2.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delC, dotProduct]
    fun_prop
  have hL : Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.delLambda q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
    simp only [Muon.DetEquiv.delLambda]
    fun_prop
  have hne : ∀ q : Mat m n × ℝ × Vec m × Vec n,
      Muon.DetEquiv.delLambda q.1 q.2.1 q.2.2.1 q.2.2.2 s ≠ 0 :=
    fun q => (Muon.DetEquiv.lem_app_de_deletion q.1 q.2.1 q.2.2.1 q.2.2.2
      (q.1 + q.2.1 • Muon.outer q.2.2.1 q.2.2.2) s rfl hs).1.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [Muon.DetEquiv.alpha1]
    exact (continuous_fst.comp continuous_snd |>.mul
      (continuous_const.add ((continuous_fst.comp continuous_snd).mul hC))).div hL hne
  · simp only [Muon.DetEquiv.alpha2]
    exact (((continuous_fst.comp continuous_snd).pow 2).mul hU).div hL hne
  · simp only [Muon.DetEquiv.alpha3]
    exact ((continuous_const.mul ((continuous_fst.comp continuous_snd).pow 2)).mul hV).neg.div hL hne

private lemma cm_delU_nonneg {m n : ℕ} (M : Mat m n) (u : Vec m) (s : ℝ) (hs : 0 < s) :
    0 ≤ Muon.DetEquiv.delU M u s := by
  have hpsd : (Rs M s).PosSemidef := by
    unfold Rs
    refine Matrix.PosSemidef.inv ?_
    have h1 : (M * Mᵀ).PosSemidef := by
      have := Matrix.posSemidef_self_mul_conjTranspose M
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
    have h2 : (s • (1 : Mat m m)).PosSemidef := Matrix.PosSemidef.one.smul hs.le
    exact h1.add h2
  have := hpsd.dotProduct_mulVec_nonneg u
  simpa [Muon.DetEquiv.delU] using this

private lemma cm_lint_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
    (hf : Measurable f) (p : ℕ) (hp : 1 ≤ p) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (p : ENNReal) μ ≤ ENNReal.ofReal K) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) ∂μ ≤ ENNReal.ofReal (K ^ p) := by
  have hp0 : ((p : ℕ) : ENNReal) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 (ENNReal.natCast_ne_top _)
    hf.aestronglyMeasurable, ENNReal.toReal_natCast] at h
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have h2 := ENNReal.rpow_le_rpow h hpr.le
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpr.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg hK hpr.le, Real.rpow_natCast] at h2
  refine le_trans (le_of_eq ?_) h2
  refine lintegral_congr fun x => ?_
  rw [← ofReal_norm, Real.norm_eq_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hpr.le,
    Real.rpow_natCast]

private lemma cm_one_add_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) : (1 + a) ^ p ≤ 2 ^ p * (1 + a ^ p) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + a ^ p) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ha p])
  · calc (1 + a) ^ p ≤ (2 * a) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * a ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + a ^ p) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma cm_pow_moment {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (f : α → ℝ) (hf : Measurable f) (k : ℕ) (hk : 1 ≤ k) (K : ℝ) (hK : 0 ≤ K)
    (h : eLpNorm f (k : ENNReal) μ ≤ ENNReal.ofReal K) :
    Integrable (fun x => |f x| ^ k) μ ∧ ∫ x, |f x| ^ k ∂μ ≤ K ^ k := by
  have hl := cm_lint_pow μ f hf k hk K hK h
  have hm : Measurable (fun x => |f x| ^ k) := by fun_prop
  have hnn : 0 ≤ᵐ[μ] (fun x => |f x| ^ k) := Filter.Eventually.of_forall fun x => by positivity
  have hint : Integrable (fun x => |f x| ^ k) μ := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hnn]
    exact lt_of_le_of_lt hl ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hl

private lemma cm_W_moment (p : ℕ) (hp : 1 ≤ p) (CS γ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m n B : ℕ) (C : Covariances m n)
      (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
      (hC : opNorm C.Sout ≤ CS ∧ opNorm C.Sin ≤ CS) (Ah : Mat m n) (hA : fro Ah = 1),
      Integrable (fun x : Vec m × Vec n =>
        ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) (gaussPair m n) ∧
      ∫ x, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p ∂(gaussPair m n) ≤ K := by
  obtain ⟨Kd, hKd0, hKd⟩ : ∃ Kd : ℝ, 0 ≤ Kd ∧ ∀ (m n : ℕ) (Ah : Mat m n), fro Ah = 1 →
      eLpNorm (fun x => resid Ah x) ((8 * p : ℕ) : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal Kd := by
    refine ⟨((Nat.doubleFactorial (8 * p - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / ((4 * p : ℕ) : ℝ)),
      by positivity, fun m n Ah hA => ?_⟩
    have := lem_app_de_moments_ii Ah hA (4 * p) (by omega)
    have e : 2 * (4 * p) = 8 * p := by ring
    rw [e] at this
    exact this
  obtain ⟨KN, hKN0, hKN⟩ : ∃ KN : ℝ, 0 ≤ KN ∧ ∀ (m n B : ℕ) (C : Covariances m n)
      (hdim : (m : ℝ) ≤ (max γ 0) * (B : ℝ) ∧ (n : ℝ) ≤ (max γ 0) * (B : ℝ))
      (hC : opNorm C.Sout ≤ max CS 0 ∧ opNorm C.Sin ≤ max CS 0),
      eLpNorm (momN C B) ((6 * p : ℕ) : ℝ≥0∞) (gaussPair m n) ≤ ENNReal.ofReal KN := by
    refine ⟨2 * max CS 0 * max γ 0 *
      ((Nat.doubleFactorial (2 * (6 * p) - 1) : ℕ) : ℝ) ^ ((1 : ℝ) / ((6 * p : ℕ) : ℝ)),
      by positivity, fun m n B C hdim hC => ?_⟩
    exact lem_app_de_moments_i C B (max γ 0) (max CS 0) hdim hC (6 * p) (by omega)
  refine ⟨2 ^ (8 * p) * (1 + Kd ^ (8 * p)) + 2 ^ (6 * p) * (1 + KN ^ (6 * p)), by positivity,
    fun m n B C hdim hγ hC Ah hA => ?_⟩
  have hdim' : (m : ℝ) ≤ (max γ 0) * (B : ℝ) ∧ (n : ℝ) ≤ (max γ 0) * (B : ℝ) := by
    rw [max_eq_left hγ]; exact hdim
  have hC' : opNorm C.Sout ≤ max CS 0 ∧ opNorm C.Sin ≤ max CS 0 :=
    ⟨hC.1.trans (le_max_left _ _), hC.2.trans (le_max_left _ _)⟩
  have hNm : Measurable (momN C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hNnn : ∀ x, 0 ≤ momN C B x := fun x => by unfold momN; positivity
  have hdm : Measurable (fun x : Vec m × Vec n => resid Ah x) := by unfold resid; fun_prop
  obtain ⟨hdI, hdB⟩ := cm_pow_moment (gaussPair m n) (fun x => resid Ah x) hdm (8 * p)
    (by omega) Kd hKd0 (hKd m n Ah hA)
  obtain ⟨hNI, hNB⟩ := cm_pow_moment (gaussPair m n) (momN C B) hNm (6 * p)
    (by omega) KN hKN0 (hKN m n B C hdim' hC')
  have habsN : ∀ x : Vec m × Vec n, |momN C B x| = momN C B x := fun x => abs_of_nonneg (hNnn x)
  simp_rw [habsN] at hNI hNB
  have hpt : ∀ x : Vec m × Vec n, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p
      ≤ (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p) := by
    intro x
    have ha := cm_one_add_pow _ (abs_nonneg (resid Ah x)) (8 * p)
    have hb := cm_one_add_pow _ (hNnn x) (6 * p)
    have h1 : ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p
        = (1 + |resid Ah x|) ^ (4 * p) * (1 + momN C B x) ^ (3 * p) := by
      rw [mul_pow, ← pow_mul, ← pow_mul]
    have h2 : (1 + |resid Ah x|) ^ (4 * p) * (1 + momN C B x) ^ (3 * p)
        ≤ (1 + |resid Ah x|) ^ (8 * p) + (1 + momN C B x) ^ (6 * p) := by
      have e1 : (1 + |resid Ah x|) ^ (8 * p) = ((1 + |resid Ah x|) ^ (4 * p)) ^ 2 := by
        rw [← pow_mul]; ring_nf
      have e2 : (1 + momN C B x) ^ (6 * p) = ((1 + momN C B x) ^ (3 * p)) ^ 2 := by
        rw [← pow_mul]; ring_nf
      rw [e1, e2]
      nlinarith [sq_nonneg ((1 + |resid Ah x|) ^ (4 * p) - (1 + momN C B x) ^ (3 * p)),
        pow_nonneg (by linarith [abs_nonneg (resid Ah x)] : (0 : ℝ) ≤ 1 + |resid Ah x|) (4 * p),
        pow_nonneg (by linarith [hNnn x] : (0 : ℝ) ≤ 1 + momN C B x) (3 * p)]
    rw [h1]
    nlinarith [h2, ha, hb]
  have hg : Integrable (fun x : Vec m × Vec n =>
      (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p)) (gaussPair m n) :=
    ((integrable_const _).add (hdI.const_mul _)).add (hNI.const_mul _)
  have hWm : Measurable (fun x : Vec m × Vec n =>
      ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) := by
    have : Measurable (fun x : Vec m × Vec n => resid Ah x) := hdm
    fun_prop
  have hWI : Integrable (fun x : Vec m × Vec n =>
      ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p) (gaussPair m n) := by
    refine Integrable.mono' hg hWm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by have := hNnn x; positivity)]
    exact hpt x
  refine ⟨hWI, ?_⟩
  calc ∫ x, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ p ∂(gaussPair m n)
      ≤ ∫ x, ((2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p)
        + 2 ^ (6 * p) * momN C B x ^ (6 * p)) ∂(gaussPair m n) :=
        integral_mono hWI hg hpt
    _ = (2 ^ (8 * p) + 2 ^ (6 * p)) + 2 ^ (8 * p) * ∫ x, |resid Ah x| ^ (8 * p) ∂(gaussPair m n)
        + 2 ^ (6 * p) * ∫ x, momN C B x ^ (6 * p) ∂(gaussPair m n) := by
        have h1 : Integrable (fun x : Vec m × Vec n =>
            (2 ^ (8 * p) + 2 ^ (6 * p) : ℝ) + 2 ^ (8 * p) * |resid Ah x| ^ (8 * p))
            (gaussPair m n) := (integrable_const _).add (hdI.const_mul _)
        rw [integral_add h1 (hNI.const_mul _), integral_add (integrable_const _) (hdI.const_mul _),
          integral_const_mul, integral_const_mul]
        simp
    _ ≤ 2 ^ (8 * p) * (1 + Kd ^ (8 * p)) + 2 ^ (6 * p) * (1 + KN ^ (6 * p)) := by
        have := mul_le_mul_of_nonneg_left hdB (by positivity : (0 : ℝ) ≤ 2 ^ (8 * p))
        have := mul_le_mul_of_nonneg_left hNB (by positivity : (0 : ℝ) ≤ 2 ^ (6 * p))
        nlinarith

private lemma cm_pt {m n : ℕ} (K : Mat m n) (u : Vec m) (v : Vec n) (d ϖ s s0 : ℝ)
    (hs0 : 0 < s0) (hs : s0 ≤ s) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) :
    |Muon.DetEquiv.alpha1 K (ϖ * d) u v s| ≤
        (max 1 s0⁻¹ * (1 + 3 / (4 * Real.sqrt s0)) ^ 3) * ϖ *
          ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
    |Muon.DetEquiv.alpha3 K (ϖ * d) u v s| ≤
        (max 1 s0⁻¹ * (1 + 3 / (4 * Real.sqrt s0)) ^ 3) * ϖ ^ 2 *
          ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ∧
    |Muon.DetEquiv.alpha2 K (ϖ * d) u v s| ≤
        (1 + 3 / (4 * Real.sqrt s0)) ^ 2 * ϖ ^ 2 *
          ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) / s := by
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hI : IsCompact (Set.Icc s0 s) := isCompact_Icc
  have hIpos : Set.Icc s0 s ⊆ Set.Ioi 0 := fun x hx => lt_of_lt_of_le hs0 hx.1
  have hcoef := Muon.DetEquiv.lem_app_de_coeff hI hIpos K u v (K + (ϖ * d) • Muon.outer u v) d ϖ
    rfl hϖ0 hϖ1 s ⟨hs, le_rfl⟩
  have hcc : Muon.DetEquiv.coeffConst (Set.Icc s0 s) =
      max 1 s0⁻¹ * (1 + 3 / (4 * Real.sqrt s0)) ^ 3 := by
    unfold Muon.DetEquiv.coeffConst; rw [csInf_Icc hs]
  rw [hcc] at hcoef
  obtain ⟨h1, h23, -⟩ := hcoef
  have h2nn := abs_nonneg (Muon.DetEquiv.alpha2 K (ϖ * d) u v s)
  have h3nn := abs_nonneg (Muon.DetEquiv.alpha3 K (ϖ * d) u v s)
  refine ⟨h1.trans_eq (by ring), by linarith [h23, h2nn], ?_⟩
  -- the alpha2 bound with the factor 1/s
  have hb := pf_alpha2_bound K (ϖ * d) s u v hspos
  set N : ℝ := sqNorm u + sqNorm v with hN
  have hNu := pf_sqNorm_nonneg u
  have hNv := pf_sqNorm_nonneg v
  have hN0 : 0 ≤ N := by rw [hN]; linarith
  set c0 : ℝ := 3 / (4 * Real.sqrt s0) with hc0d
  have hc0 : 0 ≤ c0 := by rw [hc0d]; positivity
  have hcs : 3 / (4 * Real.sqrt s) ≤ c0 := by
    rw [hc0d]
    have hσ : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by have := Real.sqrt_le_sqrt hs; linarith)
  have hcs0 : 0 ≤ 3 / (4 * Real.sqrt s) := by positivity
  have hab : |ϖ * d| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg hϖ0]; exact mul_le_of_le_one_left (abs_nonneg d) hϖ1
  set a : ℝ := |d| with ha
  have ha0 : 0 ≤ a := abs_nonneg d
  have hin : 1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * (sqNorm u + sqNorm v) ≤
      (1 + c0) * (1 + a) * (1 + N) := by
    have h1 : 3 / (4 * Real.sqrt s) * |ϖ * d| * N ≤ c0 * a * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcs hab (abs_nonneg _) hc0) hN0
    have e : (1 + c0) * (1 + a) * (1 + N) =
        1 + c0 * a * N + (c0 + a + c0 * a + N + c0 * N + a * N) := by ring
    have hr : 0 ≤ c0 + a + c0 * a + N + c0 * N + a * N := by positivity
    rw [e]
    linarith
  have hin0 : 0 ≤ 1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * (sqNorm u + sqNorm v) := by
    have := abs_nonneg (ϖ * d); positivity
  have hsq : (1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * (sqNorm u + sqNorm v)) ^ 2 ≤
      ((1 + c0) * (1 + a) * (1 + N)) ^ 2 := pow_le_pow_left₀ hin0 hin 2
  have hNuN : sqNorm u ≤ 1 + N := by rw [hN]; linarith
  have hh : (ϖ * d) ^ 2 = ϖ ^ 2 * a ^ 2 := by rw [mul_pow, ha, sq_abs]
  have hstep : (ϖ * d) ^ 2 * (sqNorm u / s) *
      (1 + 3 / (4 * Real.sqrt s) * |ϖ * d| * (sqNorm u + sqNorm v)) ^ 2 ≤
      (ϖ ^ 2 * a ^ 2) * ((1 + N) / s) * ((1 + c0) * (1 + a) * (1 + N)) ^ 2 := by
    rw [hh]
    refine mul_le_mul (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hNuN hspos.le)
      (by positivity)) hsq (sq_nonneg _) (by positivity)
  refine hb.trans (hstep.trans ?_)
  have ha1 : a ^ 2 ≤ (1 + a) ^ 2 := pow_le_pow_left₀ ha0 (by linarith) 2
  have e : (1 + c0) ^ 2 * ϖ ^ 2 * ((1 + a) ^ 4 * (1 + N) ^ 3) / s =
      (ϖ ^ 2 * (1 + a) ^ 2) * ((1 + N) / s) * ((1 + c0) * (1 + a) * (1 + N)) ^ 2 := by
    field_simp
  rw [e]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left ha1 (sq_nonneg _)) (by positivity)) (sq_nonneg _)

private lemma cm_sq_eq {m n B : ℕ} (F : FrozenParams m n B) (x : Vec m × Vec n) :
    sqNorm (momU F.C B x) + sqNorm (momV F.C B x) = momN F.C B x := by
  simp only [momN, pf_eucNorm_sq]

set_option maxHeartbeats 1000000 in
private theorem cm_main (p : ℕ) (hp : 1 ≤ p) (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ : ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      ∀ s : ℝ, s0 ≤ s →
        (∀ ω, 0 ≤ ageAlpha2 F S t j M0 ϖ s ω) ∧
        (Integrable (fun ω => |ageAlpha1 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha1 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ) ^ p) ∧
        (Integrable (fun ω => |ageAlpha3 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha3 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ ^ 2) ^ p) ∧
        (Integrable (fun ω => |ageAlpha2 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha2 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ ^ 2 / s) ^ p) := by
  obtain ⟨K0, hK00, hK0⟩ := cm_W_moment p hp CS γ
  obtain ⟨c0, hc0d⟩ : ∃ c0 : ℝ, c0 = 3 / (4 * Real.sqrt s0) := ⟨_, rfl⟩
  have hc0 : 0 ≤ c0 := by rw [hc0d]; positivity
  obtain ⟨Kc, hKc⟩ : ∃ Kc : ℝ, Kc = max 1 s0⁻¹ * (1 + c0) ^ 3 := ⟨_, rfl⟩
  have hKc2 : (1 + c0) ^ 2 ≤ Kc := by
    rw [hKc]
    have h1 : (1 : ℝ) ≤ max 1 s0⁻¹ := le_max_left _ _
    have h2 : (1 + c0) ^ 2 ≤ (1 + c0) ^ 3 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    calc (1 + c0) ^ 2 ≤ (1 + c0) ^ 3 := h2
      _ = 1 * (1 + c0) ^ 3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (by positivity)
  have hKc0 : 0 ≤ Kc := le_trans (by positivity) hKc2
  obtain ⟨Mom, hMom⟩ : ∃ Mom : ℝ, Mom = max 1 K0 := ⟨_, rfl⟩
  have hMom1 : 1 ≤ Mom := by rw [hMom]; exact le_max_left _ _
  have hK0Mom : K0 ≤ Mom ^ p := by
    calc K0 ≤ Mom := by rw [hMom]; exact le_max_right _ _
      _ ≤ Mom ^ p := le_self_pow₀ hMom1 (by omega)
  refine ⟨Kc * Mom, ?_⟩
  intro Ω inst m n B P _ F S t j M0 ϖ hCo hCi hm hn hϖ0 hϖ1 hM0 s hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM0m : Measurable M0 := hM0.mono hG le_rfl
  -- independence of the others σ-field from the fresh slot
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  -- the model-uniform moment of the majorant
  have hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ) := ⟨hm, hn⟩
  obtain ⟨hWI, hWB⟩ := hK0 m n B F.C hdim hγ ⟨hCo, hCi⟩ F.A F.hA
  set Wb : Vec m × Vec n → ℝ := fun x => (1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3 with hWbdef
  set W : Vec m × Vec n → ℝ := fun x => Wb x ^ p with hWdef
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hNm : Measurable (momN F.C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hWm : Measurable W := by
    simp only [hWdef, hWbdef]
    fun_prop
  have hWnn : ∀ x, 0 ≤ Wb x := fun x => by
    have : 0 ≤ momN F.C B x := by unfold momN; positivity
    simp only [hWbdef]; positivity
  have hHint : Integrable (fun ω => W (X ω)) P := by
    have : Integrable W (P.map X) := by rw [hlaw]; exact hWI
    exact (integrable_map_measure hWm.aestronglyMeasurable hX.aemeasurable).mp this
  have hHval : ∫ ω, W (X ω) ∂P ≤ Mom ^ p := by
    have : ∫ y, W y ∂(P.map X) = ∫ ω, W (X ω) ∂P :=
      integral_map hX.aemeasurable hWm.aestronglyMeasurable
    rw [← this, hlaw]
    exact hWB.trans hK0Mom
  have hHnn : 0 ≤ ∫ ω, W (X ω) ∂P :=
    integral_nonneg fun ω => pow_nonneg (hWnn _) p
  -- generic conditional step
  have key : ∀ (A : Ω → ℝ) (k : ℝ), Measurable A → 0 ≤ k → (∀ ω, |A ω| ≤ k * Wb (X ω)) →
      Integrable (fun ω => |A ω| ^ p) P ∧
        ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P (fun ω' => |A ω'| ^ p) ω ≤ (k * Mom) ^ p := by
    intro A k hA hk hle
    obtain ⟨hi, hc⟩ := cm_cond hG X hX hind W hWm hHint (fun ω => |A ω| ^ p)
      (by have := hA; fun_prop) (k ^ p) (by positivity) (fun ω => by positivity)
      (fun ω => by
        calc |A ω| ^ p ≤ (k * Wb (X ω)) ^ p := pow_le_pow_left₀ (abs_nonneg _) (hle ω) p
          _ = k ^ p * W (X ω) := by simp only [hWdef]; rw [mul_pow])
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hHval (by positivity)
  -- measurability of the coefficients
  obtain ⟨c1, c2, c3⟩ := cm_alpha_cont (m := m) (n := n) s hspos
  have hUm : Measurable (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hX
  have hVm : Measurable (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hX
  have hDm : Measurable (fun ω => ϖ * resid F.A (X ω)) := (hdm.comp hX).const_mul ϖ
  have hq : Measurable (fun ω => (M0 ω, ϖ * resid F.A (X ω), momU F.C B (X ω), momV F.C B (X ω))) :=
    hM0m.prodMk (hDm.prodMk (hUm.prodMk hVm))
  have hA1 : Measurable (ageAlpha1 F S t j M0 ϖ s) := c1.measurable.comp hq
  have hA2 : Measurable (ageAlpha2 F S t j M0 ϖ s) := c2.measurable.comp hq
  have hA3 : Measurable (ageAlpha3 F S t j M0 ϖ s) := c3.measurable.comp hq
  -- pointwise bounds
  have hpt : ∀ ω, |ageAlpha1 F S t j M0 ϖ s ω| ≤ (Kc * ϖ) * Wb (X ω) ∧
      |ageAlpha3 F S t j M0 ϖ s ω| ≤ (Kc * ϖ ^ 2) * Wb (X ω) ∧
      |ageAlpha2 F S t j M0 ϖ s ω| ≤ ((1 + c0) ^ 2 * ϖ ^ 2 / s) * Wb (X ω) := by
    intro ω
    have h := cm_pt (M0 ω) (momU F.C B (X ω)) (momV F.C B (X ω)) (resid F.A (X ω)) ϖ s s0
      hs0 hs hϖ0 hϖ1
    rw [cm_sq_eq F (X ω), ← hc0d, ← hKc] at h
    obtain ⟨h1, h3, h2⟩ := h
    refine ⟨h1, h3, ?_⟩
    refine h2.trans_eq ?_
    simp only [hWbdef]
    ring
  refine ⟨fun ω => ?_, ?_, ?_, ?_⟩
  · have hΛ := (Muon.DetEquiv.lem_app_de_deletion (M0 ω) (ϖ * ageD F S t j ω)
      (ageU F S t j ω) (ageV F S t j ω) (ageBuf F S t j M0 ϖ ω) s rfl hspos).1
    exact div_nonneg (mul_nonneg (sq_nonneg _) (cm_delU_nonneg _ _ s hspos)) hΛ.le
  · obtain ⟨hi, hc⟩ := key _ (Kc * ϖ) hA1 (by positivity) (fun ω => (hpt ω).1)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans_eq ?_
    ring
  · obtain ⟨hi, hc⟩ := key _ (Kc * ϖ ^ 2) hA3 (by positivity) (fun ω => (hpt ω).2.1)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans_eq ?_
    ring
  · obtain ⟨hi, hc⟩ := key _ ((1 + c0) ^ 2 * ϖ ^ 2 / s) hA2 (by positivity)
      (fun ω => (hpt ω).2.2)
    refine ⟨hi, ?_⟩
    filter_upwards [hc] with ω hω
    refine hω.trans ?_
    refine pow_le_pow_left₀ (by positivity) ?_ p
    have : (1 + c0) ^ 2 * ϖ ^ 2 / s * Mom ≤ Kc * Mom * ϖ ^ 2 / s := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hspos]
      nlinarith [mul_le_mul_of_nonneg_right hKc2 (by positivity : 0 ≤ ϖ ^ 2 * Mom)]
    exact this



/-! ## Conditional moments of the coefficients (`lem:app-drift-coeffmoments`) -/

/-- lem:app-drift-coeffmoments. Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.281–294, verbatim).

Conditional moments: `‖α₁‖_{p,𝒢} ≤ Cϖ`, `‖α₃‖_{p,𝒢} ≤ Cϖ²`, `‖α₂‖_{p,𝒢} ≤ Cϖ²/s` with
`𝒢 = 𝒢_{ja} = sigmaOthers F S t j`; stated as `E_𝒢|α|^p ≤ (bound)^p` a.s. (see module doc).
Also `α₂ ≥ 0`. The constant `C` depends only on `(p, s₀, C_Σ, γ⋆)`.

\begin{lemma}[Conditional moments of the coefficients]\label{lem:app-drift-coeffmoments}
Let $s_\circ>0$ and $p\ge1$ be an integer. In the setting of
\cref{lem:app-de-deletion}, let $M_0$ be a function of the samples other than
$(j,a)$, let $(\mathsf h,\mathsf u,\mathsf v)=(\varpi d,\mathsf u_{ja},\mathsf v_{ja})$
with $0\le\varpi\le1$ and $d=d_{ja}$, and let $\mathcal G=\mathcal G_{ja}$. Then
for every $s\ge s_\circ$,
\begin{equation}\label{eqn:app-drift-coeffmoments}
\norm{\alpha_1}_{p,\mathcal G}\le C\varpi,\qquad
\norm{\alpha_3}_{p,\mathcal G}\le C\varpi^2,\qquad
\norm{\alpha_2}_{p,\mathcal G}\le\frac{C\varpi^2}{s},
\end{equation}
with $C$ depending only on $(p,s_\circ,C_\Sigma,\gamma_\star)$, and
$\alpha_2\ge0$.
\end{lemma}
-/
theorem lem_app_drift_coeffmoments (p : ℕ) (hp : 1 ≤ p) (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ : ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      ∀ s : ℝ, s0 ≤ s →
        (∀ ω, 0 ≤ ageAlpha2 F S t j M0 ϖ s ω) ∧
        (Integrable (fun ω => |ageAlpha1 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha1 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ) ^ p) ∧
        (Integrable (fun ω => |ageAlpha3 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha3 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ ^ 2) ^ p) ∧
        (Integrable (fun ω => |ageAlpha2 F S t j M0 ϖ s ω| ^ p) P ∧
          ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
            (fun ω' => |ageAlpha2 F S t j M0 ϖ s ω'| ^ p) ω ≤ (C * ϖ ^ 2 / s) ^ p) := by
  exact cm_main p hp s0 hs0 CS γ hγ


/-- Matrix product entry as a sum over the index pairs of the middle factor. -/
private lemma cm_mul3_apply {p q r t : ℕ} (A : Mat p q) (B : Mat q r) (C : Mat r t) (i : Fin p)
    (j : Fin t) :
    (A * B * C) i j = ∑ x : Fin q × Fin r, (A i x.1 * C x.2 j) * B x.1 x.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Entrywise pull-out of bounded `𝒢`-measurable matrix factors from `condExpMat`. -/
private lemma cm_condExpMat_pull {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (L : Ω → Mat p q) (R : Ω → Mat r t)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) :
    ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ = L ζ * Muon.Foundations.condExpMat G P F ζ * R ζ := by
  have hint : ∀ i j (x : Fin q × Fin r),
      Integrable (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) P := by
    intro i j x
    refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
      (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun ω => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (abs_nonneg _) hcL
  have hterm : ∀ i j (x : Fin q × Fin r), ∀ᵐ ζ ∂P,
      condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
        (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ := by
    intro i j x
    have hfm : Measurable[G] (fun ω => L ω i x.1 * R ω x.2 j) := (hL i x.1).mul (hR x.2 j)
    have := condExp_mul_of_stronglyMeasurable_left (m := G) (μ := P)
      (f := fun ω => L ω i x.1 * R ω x.2 j) (g := fun ω => F ω x.1 x.2)
      hfm.stronglyMeasurable (hint i j x) (hF x.1 x.2)
    filter_upwards [this] with ζ hζ
    exact hζ
  have hentry : ∀ i j, ∀ᵐ ζ ∂P,
      Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ i j = (L ζ * Muon.Foundations.condExpMat G P F ζ * R ζ) i j := by
    intro i j
    have h1 : condExp G P (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2)
        =ᵐ[P] ∑ x : Fin q × Fin r,
          condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
      have e : (fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) =
          ∑ x : Fin q × Fin r, (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) := by
        funext ω; simp [Finset.sum_apply]
      rw [e]
      exact condExp_finsetSum (fun x _ => hint i j x) G
    have h2 : ∀ᵐ ζ ∂P, ∀ x : Fin q × Fin r,
        condExp G P (fun ω => (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2) ζ =
          (L ζ i x.1 * R ζ x.2 j) * condExp G P (fun ω => F ω x.1 x.2) ζ :=
      ae_all_iff.2 fun x => hterm i j x
    filter_upwards [h1, h2] with ζ h1ζ h2ζ
    have e2 : (fun ω => (L ω * F ω * R ω) i j) =
        fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
      funext fun ω => cm_mul3_apply _ _ _ _ _
    rw [Muon.Foundations.condExpMat_apply, e2, h1ζ, Finset.sum_apply, cm_mul3_apply]
    exact Finset.sum_congr rfl fun x _ => h2ζ x
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Operator-norm bound on matrix entries (copy of the trace-file helper). -/
private lemma cm_abs_entry_le {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
    |K i j| ≤ opNorm K := by
  have h1 := Matrix.l2_opNorm_mulVec K (EuclideanSpace.single j (1 : ℝ))
  have h2 := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin p) ℝ).symm
    (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i
  have h3 : ((EuclideanSpace.equiv (Fin p) ℝ).symm
      (K *ᵥ ⇑(EuclideanSpace.single j (1 : ℝ)))) i = K i j := by
    simp [Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  simp only [EuclideanSpace.norm_single, norm_one, mul_one] at h1
  rw [h3, Real.norm_eq_abs] at h2
  rw [opNorm_eq_norm]
  linarith

/-- Vector-form integrability: `e (u_a v_b)` is integrable when `u = c R x`, `v = c' S y`. -/
private lemma cm_int_outer {d d' : ℕ} (P : Measure Ω) (x : Ω → Vec d) (y : Ω → Vec d')
    (R : Mat d d) (S : Mat d' d') (c c' : ℝ) (u : Ω → Vec d) (v : Ω → Vec d') (e : Ω → ℝ)
    (hu : ∀ ω, u ω = c • (R *ᵥ x ω)) (hv : ∀ ω, v ω = c' • (S *ᵥ y ω))
    (hxy : ∀ p q, Integrable (fun ω => x ω p * y ω q * e ω) P) (a : Fin d) (b : Fin d') :
    Integrable (fun ω => e ω * (u ω a * v ω b)) P := by
  have h : (fun ω => e ω * (u ω a * v ω b)) = fun ω =>
      ∑ p : Fin d, ∑ q : Fin d', (c * c' * (R a p * S b q)) * (x ω p * y ω q * e ω) := by
    funext ω
    rw [hu, hv]
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  rw [h]
  exact integrable_finset_sum _ fun p _ =>
    integrable_finset_sum _ fun q _ => (hxy p q).const_mul _

/-- Entries of `L * F * R` are integrable under bounded `𝒢`-measurable factors. -/
private lemma cm_int_LFR {p q r t : ℕ} (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (L : Ω → Mat p q) (R : Ω → Mat r t) (cL cR : ℝ) (hcL : 0 ≤ cL)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) (i : Fin p) (j : Fin t) :
    Integrable (fun ω => (L ω * F ω * R ω) i j) P := by
  have e : (fun ω => (L ω * F ω * R ω) i j) =
      fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
    funext fun ω => cm_mul3_apply _ _ _ _ _
  rw [e]
  refine integrable_finset_sum _ fun x _ => ?_
  refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
    (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (abs_nonneg _) hcL

/-- Entrywise additivity of `condExpMat`. -/
private lemma cm_condExpMat_add {p q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (A B : Ω → Mat p q)
    (hA : ∀ i j, Integrable (fun ω => A ω i j) P) (hB : ∀ i j, Integrable (fun ω => B ω i j) P) :
    ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => A ω + B ω) ζ =
      Muon.Foundations.condExpMat G P A ζ + Muon.Foundations.condExpMat G P B ζ := by
  have hent : ∀ i j, ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P (fun ω => A ω + B ω) ζ i j =
      (Muon.Foundations.condExpMat G P A ζ + Muon.Foundations.condExpMat G P B ζ) i j := by
    intro i j
    have h := condExp_add (hA i j) (hB i j) G
    filter_upwards [h] with ζ hζ
    rw [Matrix.add_apply, Muon.Foundations.condExpMat_apply, Muon.Foundations.condExpMat_apply,
      Muon.Foundations.condExpMat_apply]
    exact hζ
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hent i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Operator-norm sandwich for the Frobenius norm. -/
private lemma cm_fro_sandwich {p q r t : ℕ} (L : Mat p q) (K : Mat q r) (R : Mat r t) :
    fro (L * K * R) ≤ opNorm L * fro K * opNorm R :=
  (bf_fro_mul_le_right _ _).trans
    (mul_le_mul_of_nonneg_right (bf_fro_mul_le_left _ _) (bf_opNorm_nonneg _))

/-- Frobenius bound for a pulled-out sandwich `L (condExp F) R` under a Bessel bound on `F`. -/
private lemma cm_term {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (G : MeasurableSpace Ω) (hG : G ≤ mΩ) (L : Ω → Mat p q) (R : Ω → Mat r t)
    (cL cR : ℝ) (hcL : 0 ≤ cL) (hcR : 0 ≤ cR)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P)
    (aL aR K : ℝ) (haL0 : 0 ≤ aL) (haR0 : 0 ≤ aR) (hK0 : 0 ≤ K)
    (haL : ∀ ζ, opNorm (L ζ) ≤ aL) (haR : ∀ ζ, opNorm (R ζ) ≤ aR)
    (hK : ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P F ζ) ≤ K) :
    ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P (fun ω => L ω * F ω * R ω) ζ) ≤ aL * K * aR := by
  filter_upwards [cm_condExpMat_pull (mΩ := mΩ) P G hG L R cL cR hcL hcR hL hR hLb hRb F hF, hK]
    with ζ h1 h2
  rw [h1]
  refine (cm_fro_sandwich _ _ _).trans ?_
  exact mul_le_mul (mul_le_mul (haL ζ) h2 (bf_fro_nonneg _) haL0) (haR ζ) (bf_opNorm_nonneg _)
    (mul_nonneg haL0 hK0)

/-- Conditional second moment of `e` from a pointwise bound `|e| ≤ D |a|`. -/
private lemma cm_cond_sq (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (e a : Ω → ℝ) (D K : ℝ) (hD : 0 ≤ D) (hK0 : 0 ≤ K) (he : Measurable[mΩ] e)
    (hea : ∀ ω, |e ω| ≤ D * |a ω|) (ha2 : Integrable (fun ω => |a ω| ^ 2) P)
    (hK : ∀ᵐ ω ∂P, condExp G P (fun ω' => |a ω'| ^ 2) ω ≤ K ^ 2) :
    ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ D * K := by
  have hle : ∀ ω, e ω ^ 2 ≤ D ^ 2 * |a ω| ^ 2 := fun ω => by
    rw [← sq_abs (e ω)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hea ω) 2
    linarith [this, show (D * |a ω|) ^ 2 = D ^ 2 * |a ω| ^ 2 by ring]
  have hg : Integrable (fun ω => D ^ 2 * |a ω| ^ 2) P := ha2.const_mul (D ^ 2)
  have hI : Integrable (fun ω => e ω ^ 2) P := by
    refine Integrable.mono' hg (he.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hle ω
  have hc := condExp_mono (m := G) hI hg (Filter.Eventually.of_forall hle)
  have hsc : condExp G P (fun ω => D ^ 2 * |a ω| ^ 2) =ᵐ[P]
      fun ζ => D ^ 2 * condExp G P (fun ω => |a ω| ^ 2) ζ := by
    have := condExp_smul (μ := P) (D ^ 2) (fun ω => |a ω| ^ 2) G
    simpa [Pi.smul_def, smul_eq_mul] using this
  filter_upwards [hc, hsc, hK] with ζ h1 h2 h3
  have h4 : condExp G P (fun ω => e ω ^ 2) ζ ≤ D ^ 2 * K ^ 2 := by
    have h2' : condExp G P (fun ω => D ^ 2 * |a ω| ^ 2) ζ =
        D ^ 2 * condExp G P (fun ω => |a ω| ^ 2) ζ := h2
    rw [h2'] at h1
    exact h1.trans (mul_le_mul_of_nonneg_left h3 (sq_nonneg _))
  calc Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ Real.sqrt (D ^ 2 * K ^ 2) :=
        Real.sqrt_le_sqrt h4
    _ = D * K := by
        rw [show D ^ 2 * K ^ 2 = (D * K) ^ 2 by ring, Real.sqrt_sq (mul_nonneg hD hK0)]


/-- Four-term conditional Frobenius bound (assembly of the Bessel bounds with pulled-out factors). -/
private lemma cm_four {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (CS γ : ℝ) (hB : 0 < B) (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P)
    (R0 : Ω → Mat m m) (Rt0 : Ω → Mat n n) (X0 : Ω → Mat m n) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hR0m : ∀ i j, Measurable[G] (fun ω => R0 ω i j))
    (hRt0m : ∀ i j, Measurable[G] (fun ω => Rt0 ω i j))
    (hX0m : ∀ i j, Measurable[G] (fun ω => X0 ω i j))
    (hR0 : ∀ ω, opNorm (R0 ω) ≤ a) (hRt0 : ∀ ω, opNorm (Rt0 ω) ≤ a)
    (hX00 : ∀ ω, opNorm (X0 ω) ≤ b)
    (e1 e2 e3 e4 : Ω → ℝ)
    (he1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e1)
    (he2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e2)
    (he3 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e3)
    (he4 : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e4)
    (hl1 : MemLp e1 2 P) (hl2 : MemLp e2 2 P) (hl3 : MemLp e3 2 P) (hl4 : MemLp e4 2 P)
    (κ1 κ2 κ3 κ4 : ℝ) (hκ1 : 0 ≤ κ1) (hκ2 : 0 ≤ κ2) (hκ3 : 0 ≤ κ3) (hκ4 : 0 ≤ κ4)
    (hk1 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e1 ω ^ 2) ζ) ≤ κ1)
    (hk2 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e2 ω ^ 2) ζ) ≤ κ2)
    (hk3 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e3 ω ^ 2) ζ) ≤ κ3)
    (hk4 : ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e4 ω ^ 2) ζ) ≤ κ4) :
    ∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P (fun ω =>
        R0 ω * (e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) * X0 ω
        + R0 ω * (e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) * Rt0 ω
        + X0 ω * (e3 ω • Muon.outer (momV C B (X ω)) (momU C B (X ω))) * X0 ω
        + X0 ω * (e4 ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) * Rt0 ω) ζ) ≤
      a * (CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * κ1) * b + a * (CS / B * κ2) * a
        + b * (CS / B * κ3) * b + b * (CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B * κ4) * a := by
  have hCS : 0 ≤ CS := (bf_opNorm_nonneg _).trans hSo
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hKuu : 0 ≤ CS * (Real.sqrt 2 + Real.sqrt (γ * B)) / B := by positivity
  have hKuv : 0 ≤ CS / B := by positivity
  have hI : ∀ e : Ω → ℝ, MemLp e 2 P → Integrable e P := fun e h => h.integrable one_le_two
  -- integrability of the weighted cross products
  have iuu : ∀ e : Ω → ℝ, MemLp e 2 P → ∀ p q : Fin m,
      Integrable (fun ω => (X ω).1 p * (X ω).1 q * e ω) P := by
    intro e he p q
    have := (bf_integrable_mul (mΩ := mΩ) (bf_memLp_sq_fst (mΩ := mΩ) P X hX p q) he).add ((hI e he).const_mul ((1 : Mat m m) p q))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have ivv : ∀ e : Ω → ℝ, MemLp e 2 P → ∀ p q : Fin n,
      Integrable (fun ω => (X ω).2 p * (X ω).2 q * e ω) P := by
    intro e he p q
    have := (bf_integrable_mul (mΩ := mΩ) (bf_memLp_sq_snd (mΩ := mΩ) P X hX p q) he).add ((hI e he).const_mul ((1 : Mat n n) p q))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have iuv : ∀ e : Ω → ℝ, MemLp e 2 P → ∀ (p : Fin m) (q : Fin n),
      Integrable (fun ω => (X ω).1 p * (X ω).2 q * e ω) P := fun e he p q =>
    bf_integrable_mul (mΩ := mΩ) (bf_memLp_cross (mΩ := mΩ) P X hX p q) he
  have ivu : ∀ e : Ω → ℝ, MemLp e 2 P → ∀ (p : Fin n) (q : Fin m),
      Integrable (fun ω => (X ω).2 p * (X ω).1 q * e ω) P := fun e he p q => by
    have := iuv e he q p
    simpa only [mul_comm ((X _).2 p)] using this
  have hu : ∀ ω, momU C B (X ω) = (Real.sqrt B)⁻¹ • (rOut C *ᵥ (X ω).1) := fun ω => rfl
  have hv : ∀ ω, momV C B (X ω) = (Real.sqrt B)⁻¹ • (rIn C *ᵥ (X ω).2) := fun ω => rfl
  have hent : ∀ {d d' : ℕ} (e : Ω → ℝ) (u : Ω → Vec d) (v : Ω → Vec d') (k : Fin d) (l : Fin d'),
      (fun ω => (e ω • Muon.outer (u ω) (v ω)) k l) = fun ω => e ω * (u ω k * v ω l) := by
    intro d d' e u v k l; funext ω; simp [Muon.outer, Matrix.vecMulVec_apply]
  have F1 : ∀ k l, Integrable (fun ω => (e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) k l) P := by
    intro k l; rw [hent]
    exact cm_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).1) (rOut C) (rOut C) _ _
      (fun ω => momU C B (X ω)) (fun ω => momU C B (X ω)) e1 hu hu (iuu e1 hl1) k l
  have F2 : ∀ k l, Integrable (fun ω => (e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) k l) P := by
    intro k l; rw [hent]
    exact cm_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).2) (rOut C) (rIn C) _ _
      (fun ω => momU C B (X ω)) (fun ω => momV C B (X ω)) e2 hu hv (iuv e2 hl2) k l
  have F3 : ∀ k l, Integrable (fun ω => (e3 ω • Muon.outer (momV C B (X ω)) (momU C B (X ω))) k l) P := by
    intro k l; rw [hent]
    exact cm_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).1) (rIn C) (rOut C) _ _
      (fun ω => momV C B (X ω)) (fun ω => momU C B (X ω)) e3 hv hu (ivu e3 hl3) k l
  have F4 : ∀ k l, Integrable (fun ω => (e4 ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) k l) P := by
    intro k l; rw [hent]
    exact cm_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).2) (rIn C) (rIn C) _ _
      (fun ω => momV C B (X ω)) (fun ω => momV C B (X ω)) e4 hv hv (ivv e4 hl4) k l
  have eb : ∀ {d d' : ℕ} (L : Ω → Mat d d') (c : ℝ) (h : ∀ ω, opNorm (L ω) ≤ c) ω i j,
      |L ω i j| ≤ c := fun L c h ω i j => (cm_abs_entry_le _ _ _).trans (h ω)
  -- Bessel bounds
  have B1 := bessel_frob_uu (mΩ := mΩ) P C CS γ hB hSo hm X hX G hG hind e1 he1 hl1
  have B4 := bessel_frob_vv (mΩ := mΩ) P C CS γ hB hSi hn X hX G hG hind e4 he4 hl4
  have B2 := bessel_frob_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind e2 he2 hl2
  have B3 := bessel_frob_uv (mΩ := mΩ) P C CS hB hSo hSi X hX G hG hind e3 he3 hl3
  -- the four terms
  have hLI : ∀ {p q r t : ℕ} (L : Ω → Mat p q) (R : Ω → Mat r t) (cL cR : ℝ) (hcL : 0 ≤ cL)
      (hL : ∀ i j, Measurable[G] (fun ω => L ω i j)) (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
      (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR) (F : Ω → Mat q r)
      (hF : ∀ k l, Integrable (fun ω => F ω k l) P) (i : Fin p) (j : Fin t),
      Integrable (fun ω => (L ω * F ω * R ω) i j) P := fun L R cL cR hcL hL hR hLb hRb F hF i j =>
    cm_int_LFR (mΩ := mΩ) P G hG L R cL cR hcL hL hR hLb hRb F hF i j
  have A1 := hLI R0 X0 a b ha hR0m hX0m (eb R0 a hR0) (eb X0 b hX00)
    (fun ω => e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) F1
  have A2 := hLI R0 Rt0 a a ha hR0m hRt0m (eb R0 a hR0) (eb Rt0 a hRt0)
    (fun ω => e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) F2
  have A3 := hLI X0 X0 b b hb hX0m hX0m (eb X0 b hX00) (eb X0 b hX00)
    (fun ω => e3 ω • Muon.outer (momV C B (X ω)) (momU C B (X ω))) F3
  have A4 := hLI X0 Rt0 b a hb hX0m hRt0m (eb X0 b hX00) (eb Rt0 a hRt0)
    (fun ω => e4 ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) F4
  have S12 := cm_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) * X0 ω)
    (fun ω => R0 ω * (e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) * Rt0 ω) A1 A2
  have S123 := cm_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) * X0 ω
      + R0 ω * (e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) * Rt0 ω)
    (fun ω => X0 ω * (e3 ω • Muon.outer (momV C B (X ω)) (momU C B (X ω))) * X0 ω)
    (fun i j => (A1 i j).add (A2 i j)) A3
  have S1234 := cm_condExpMat_add (mΩ := mΩ) P G
    (fun ω => R0 ω * (e1 ω • Muon.outer (momU C B (X ω)) (momU C B (X ω))) * X0 ω
      + R0 ω * (e2 ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) * Rt0 ω
      + X0 ω * (e3 ω • Muon.outer (momV C B (X ω)) (momU C B (X ω))) * X0 ω)
    (fun ω => X0 ω * (e4 ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) * Rt0 ω)
    (fun i j => ((A1 i j).add (A2 i j)).add (A3 i j)) A4
  have T1 := cm_term (mΩ := mΩ) P G hG R0 X0 a b ha hb hR0m hX0m (eb R0 a hR0) (eb X0 b hX00)
    _ F1 a b _ ha hb (mul_nonneg hKuu hκ1) hR0 hX00
    (by filter_upwards [B1, hk1] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hKuu))
  have T2 := cm_term (mΩ := mΩ) P G hG R0 Rt0 a a ha ha hR0m hRt0m (eb R0 a hR0) (eb Rt0 a hRt0)
    _ F2 a a _ ha ha (mul_nonneg hKuv hκ2) hR0 hRt0
    (by filter_upwards [B2, hk2] with ζ h1 h2
        exact h1.1.trans (mul_le_mul_of_nonneg_left h2 hKuv))
  have T3 := cm_term (mΩ := mΩ) P G hG X0 X0 b b hb hb hX0m hX0m (eb X0 b hX00) (eb X0 b hX00)
    _ F3 b b _ hb hb (mul_nonneg hKuv hκ3) hX00 hX00
    (by filter_upwards [B3, hk3] with ζ h1 h2
        exact h1.2.trans (mul_le_mul_of_nonneg_left h2 hKuv))
  have T4 := cm_term (mΩ := mΩ) P G hG X0 Rt0 b a hb ha hX0m hRt0m (eb X0 b hX00) (eb Rt0 a hRt0)
    _ F4 b a _ hb ha (mul_nonneg hKuu hκ4) hX00 hRt0
    (by filter_upwards [B4, hk4] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 hKuu))
  filter_upwards [S12, S123, S1234, T1, T2, T3, T4] with ζ s12 s123 s1234 t1 t2 t3 t4
  rw [s1234, s123, s12]
  refine (bf_fro_add _ _).trans ?_
  refine add_le_add ((bf_fro_add _ _).trans (add_le_add ((bf_fro_add _ _).trans (add_le_add t1 t2)) t3)) t4

/-- Final constant bookkeeping for `lem_app_drift_multiplier_i`. -/
private lemma cm_arith (s0 s w D ϖ CS c r2 rg : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) (hw : 1 ≤ w)
    (hD : 0 ≤ D) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hCS : 0 ≤ CS) (hc : 0 ≤ c) (hr2 : 0 ≤ r2)
    (hrg : 0 ≤ rg) :
    (1 / s) * (CS * (r2 + rg * w) / w ^ 2 * (D * (c * ϖ ^ 2))) * (1 / (2 * Real.sqrt s))
      + (1 / s) * (CS / w ^ 2 * (D * s * (c * ϖ))) * (1 / s)
      + (1 / (2 * Real.sqrt s)) * (CS / w ^ 2 * (D * (c * ϖ))) * (1 / (2 * Real.sqrt s))
      + (1 / (2 * Real.sqrt s)) * (CS * (r2 + rg * w) / w ^ 2 * (D * s * (c * ϖ ^ 2 / s))) * (1 / s)
      ≤ c * CS * ((r2 + rg) / Real.sqrt s0 + 5 / 4) * D * ϖ / (s * w) := by
  have hs' : 0 < s := lt_of_lt_of_le hs0 hs
  have hw0 : 0 < w := by linarith
  have ht0 : 0 < Real.sqrt s0 := Real.sqrt_pos.2 hs0
  have ht : 0 < Real.sqrt s := Real.sqrt_pos.2 hs'
  have htt : Real.sqrt s0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have hts : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs'.le
  have hw2 : w ≤ w ^ 2 := by nlinarith
  have hq : (r2 + rg * w) / w ^ 2 ≤ (r2 + rg) / w := by
    rw [div_le_div_iff₀ (by positivity) hw0]
    nlinarith [mul_nonneg hr2 (sub_nonneg.2 hw), mul_nonneg hrg hw0.le, mul_nonneg hr2 hw0.le]
  have hq2 : 1 / w ^ 2 ≤ 1 / w := one_div_le_one_div_of_le hw0 hw2
  have hϖ2 : ϖ ^ 2 ≤ ϖ := by nlinarith
  have hi : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt s0) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  have hi0 : 0 ≤ 1 / (2 * Real.sqrt s) := by positivity
  have hi0' : 0 ≤ 1 / (2 * Real.sqrt s0) := by positivity
  have hKq : 0 ≤ (r2 + rg * w) / w ^ 2 := by positivity
  have hP : 0 ≤ CS * D * c := by positivity
  -- term 1 and 4
  have e1 : (1 / s) * (CS * (r2 + rg * w) / w ^ 2 * (D * (c * ϖ ^ 2))) * (1 / (2 * Real.sqrt s))
      = (CS * D * c) / s * ((r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))) := by
    field_simp
  have e4 : (1 / (2 * Real.sqrt s)) * (CS * (r2 + rg * w) / w ^ 2 * (D * s * (c * ϖ ^ 2 / s))) * (1 / s)
      = (CS * D * c) / s * ((r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))) := by
    field_simp
  have e2 : (1 / s) * (CS / w ^ 2 * (D * s * (c * ϖ))) * (1 / s)
      = (CS * D * c) / s * (1 / w ^ 2 * ϖ) := by
    field_simp
  have e3 : (1 / (2 * Real.sqrt s)) * (CS / w ^ 2 * (D * (c * ϖ))) * (1 / (2 * Real.sqrt s))
      = (CS * D * c) / s * (1 / w ^ 2 * ϖ * (1 / 4)) := by
    field_simp
    rw [Real.sq_sqrt hs'.le]
    ring
  have b1 : (r2 + rg * w) / w ^ 2 * ϖ ^ 2 * (1 / (2 * Real.sqrt s))
      ≤ (r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0)) := by
    gcongr
  have b2 : 1 / w ^ 2 * ϖ ≤ 1 / w * ϖ := by gcongr
  have b3 : 1 / w ^ 2 * ϖ * (1 / 4) ≤ 1 / w * ϖ * (1 / 4) := by gcongr
  have hPs : 0 ≤ (CS * D * c) / s := by positivity
  rw [e1, e2, e3, e4]
  calc _ ≤ (CS * D * c) / s * ((r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0)))
        + (CS * D * c) / s * (1 / w * ϖ) + (CS * D * c) / s * (1 / w * ϖ * (1 / 4))
        + (CS * D * c) / s * ((r2 + rg) / w * ϖ * (1 / (2 * Real.sqrt s0))) := by
        gcongr
    _ = _ := by field_simp; ring

/-- Pointwise four-term decomposition of `g (X_s(M) - X_s(M₀))`. -/
private lemma cm_decomp {m n : ℕ} (M M0 : Mat m n) (g hh s : ℝ) (u : Vec m) (v : Vec n)
    (hM : M = M0 + hh • Muon.outer u v) (hs : 0 < s) :
    g • (Muon.DetEquiv.Xs M s - Muon.DetEquiv.Xs M0 s) =
      Muon.DetEquiv.Rs M0 s * ((g * Muon.DetEquiv.alpha3 M0 hh u v s) • Muon.outer u u) *
          Muon.DetEquiv.Xs M0 s
        + Muon.DetEquiv.Rs M0 s * ((g * (s * Muon.DetEquiv.alpha1 M0 hh u v s)) • Muon.outer u v) *
          Muon.DetEquiv.Rts M0 s
        + Muon.DetEquiv.Xs M0 s * ((-(g * Muon.DetEquiv.alpha1 M0 hh u v s)) • Muon.outer v u) *
          Muon.DetEquiv.Xs M0 s
        + Muon.DetEquiv.Xs M0 s * ((-(g * (s * Muon.DetEquiv.alpha2 M0 hh u v s))) • Muon.outer v v) *
          Muon.DetEquiv.Rts M0 s := by
  rw [(lem_app_drift_column M M0 hh s u v hM hs).2]
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  module

/-- `L²` membership from a pointwise domination by an `L²` function. -/
private lemma cm_memLp2 (P : Measure Ω) (e a : Ω → ℝ) (D : ℝ) (he : Measurable[mΩ] e)
    (hea : ∀ ω, |e ω| ≤ D * |a ω|) (ha2 : Integrable (fun ω => |a ω| ^ 2) P) : MemLp e 2 P := by
  have hle : ∀ ω, e ω ^ 2 ≤ D ^ 2 * |a ω| ^ 2 := fun ω => by
    rw [← sq_abs (e ω)]
    have := pow_le_pow_left₀ (abs_nonneg _) (hea ω) 2
    linarith [this, show (D * |a ω|) ^ 2 = D ^ 2 * |a ω| ^ 2 by ring]
  refine (memLp_two_iff_integrable_sq he.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (ha2.const_mul (D ^ 2)) (he.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact hle ω

private theorem cm_i_main (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
        sigmaOthers F S t j] h →
      (∀ ω, |h ω| ≤ D) →
      ∀ s : ℝ, s0 ≤ s →
        ∀ᵐ ω ∂P, fro (Muon.Foundations.condExpMat (sigmaOthers F S t j) P
          (fun ω' => h ω' • (Muon.DetEquiv.Xs (ageBuf F S t j M0 ϖ ω') s -
            Muon.DetEquiv.Xs (M0 ω') s)) ω) ≤
          C * D * ϖ / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨Cc, hCc⟩ := lem_app_drift_coeffmoments 2 (by norm_num) s0 hs0 CS γ hγ
  refine ⟨|Cc| * CS * ((Real.sqrt 2 + Real.sqrt γ) / Real.sqrt s0 + 5 / 4), ?_⟩
  intro Ω inst m n B P _ F S t j M0 ϖ D g hCo hCi hm hn hϖ0 hϖ1 hM0 hg hD s hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hB : 0 < B := F.hB
  have hCS : 0 ≤ CS := (bf_opNorm_nonneg _).trans hCo
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hlaw : P.map X = gaussPair m n := S.law _ _
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hind : Indep (sigmaOthers F S t j) (MeasurableSpace.comap X inferInstance) P := by
    have hind0 := (iIndepFun_iff_iIndep
      (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
      (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
    have hdisj : Disjoint {q : ℤ × Fin B | q ≠ (t + 1 - (j : ℤ), slotOne F.hB)}
        ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)) := by
      rw [Set.disjoint_singleton_right]; exact fun h => h rfl
    have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hind0 hdisj
    have hB' : MeasurableSpace.comap X inferInstance ≤
        ⨆ i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B)),
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
      le_iSup₂ (f := fun i (_ : i ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Set (ℤ × Fin B))) =>
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance)
        (t + 1 - (j : ℤ), slotOne F.hB) (Set.mem_singleton _)
    exact indep_of_indep_of_le_right key hB'
  have hindc : Indep (MeasurableSpace.comap X inferInstance) (sigmaOthers F S t j) P := hind.symm
  obtain ⟨-, ⟨i1, c1'⟩, ⟨i3, c3'⟩, ⟨i2, c2'⟩⟩ :=
    hCc Ω m n B P F S t j M0 ϖ hCo hCi hm hn hϖ0 hϖ1 hM0 s hs
  -- measurability
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hX.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hM0c : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] M0 :=
    hM0.mono le_sup_right le_rfl
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hUm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momU F.C B (X ω)) := by
    have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
    exact this.comp hXc
  have hVm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => momV F.C B (X ω)) := by
    have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
    exact this.comp hXc
  have hDm : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => ϖ * resid F.A (X ω)) := (hdm.comp hXc).const_mul ϖ
  have hq : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => (M0 ω, ϖ * resid F.A (X ω), momU F.C B (X ω), momV F.C B (X ω))) :=
    hM0c.prodMk (hDm.prodMk (hUm.prodMk hVm))
  obtain ⟨c1, c2, c3⟩ := cm_alpha_cont (m := m) (n := n) s hspos
  have hA1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlpha1 F S t j M0 ϖ s) := c1.measurable.comp hq
  have hA2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlpha2 F S t j M0 ϖ s) := c2.measurable.comp hq
  have hA3 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (ageAlpha3 F S t j M0 ϖ s) := c3.measurable.comp hq
  have hD0 : 0 ≤ D := by
    obtain ⟨ω0, -⟩ := (Filter.Eventually.of_forall (p := fun _ : Ω => True) (fun _ => trivial) :
      ∀ᵐ ω ∂P, True).exists
    exact (abs_nonneg _).trans (hD ω0)
  -- the four coefficients
  have E1m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => g ω * ageAlpha3 F S t j M0 ϖ s ω) := hg.mul hA3
  have E2m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => g ω * (s * ageAlpha1 F S t j M0 ϖ s ω)) := hg.mul (hA1.const_mul s)
  have E3m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => -(g ω * ageAlpha1 F S t j M0 ϖ s ω)) := (hg.mul hA1).neg
  have E4m : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => -(g ω * (s * ageAlpha2 F S t j M0 ϖ s ω))) := (hg.mul (hA2.const_mul s)).neg
  have hDs : 0 ≤ D * s := mul_nonneg hD0 hspos.le
  have ea1 : ∀ ω, |g ω * ageAlpha3 F S t j M0 ϖ s ω| ≤ D * |ageAlpha3 F S t j M0 ϖ s ω| :=
    fun ω => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hD ω) (abs_nonneg _)
  have ea2 : ∀ ω, |g ω * (s * ageAlpha1 F S t j M0 ϖ s ω)| ≤
      (D * s) * |ageAlpha1 F S t j M0 ϖ s ω| := fun ω => by
    rw [abs_mul, abs_mul, abs_of_pos hspos]
    calc _ ≤ D * (s * |ageAlpha1 F S t j M0 ϖ s ω|) :=
          mul_le_mul_of_nonneg_right (hD ω) (by positivity)
      _ = _ := by ring
  have ea3 : ∀ ω, |-(g ω * ageAlpha1 F S t j M0 ϖ s ω)| ≤ D * |ageAlpha1 F S t j M0 ϖ s ω| :=
    fun ω => by rw [abs_neg, abs_mul]; exact mul_le_mul_of_nonneg_right (hD ω) (abs_nonneg _)
  have ea4 : ∀ ω, |-(g ω * (s * ageAlpha2 F S t j M0 ϖ s ω))| ≤
      (D * s) * |ageAlpha2 F S t j M0 ϖ s ω| := fun ω => by
    rw [abs_neg, abs_mul, abs_mul, abs_of_pos hspos]
    calc _ ≤ D * (s * |ageAlpha2 F S t j M0 ϖ s ω|) :=
          mul_le_mul_of_nonneg_right (hD ω) (by positivity)
      _ = _ := by ring
  have L1 := cm_memLp2 P _ _ D (E1m.mono hGc le_rfl) ea1 i3
  have L2 := cm_memLp2 P _ _ (D * s) (E2m.mono hGc le_rfl) ea2 i1
  have L3 := cm_memLp2 P _ _ D (E3m.mono hGc le_rfl) ea3 i1
  have L4 := cm_memLp2 P _ _ (D * s) (E4m.mono hGc le_rfl) ea4 i2
  have hc0 : 0 ≤ |Cc| := abs_nonneg _
  have K1 := cm_cond_sq P (sigmaOthers F S t j) _ _ D (|Cc| * ϖ ^ 2) hD0 (by positivity)
    (E1m.mono hGc le_rfl) ea1 i3
    (by filter_upwards [c3'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K2 := cm_cond_sq P (sigmaOthers F S t j) _ _ (D * s) (|Cc| * ϖ) hDs (by positivity)
    (E2m.mono hGc le_rfl) ea2 i1
    (by filter_upwards [c1'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K3 := cm_cond_sq P (sigmaOthers F S t j) _ _ D (|Cc| * ϖ) hD0 (by positivity)
    (E3m.mono hGc le_rfl) ea3 i1
    (by filter_upwards [c1'] with ω h; exact h.trans_eq (by rw [mul_pow, mul_pow, sq_abs]))
  have K4 := cm_cond_sq P (sigmaOthers F S t j) _ _ (D * s) (|Cc| * ϖ ^ 2 / s) hDs (by positivity)
    (E4m.mono hGc le_rfl) ea4 i2
    (by filter_upwards [c2'] with ω h
        exact h.trans_eq (by rw [div_pow, div_pow, mul_pow, mul_pow, sq_abs]))
  -- G-measurable resolvent factors
  have hentm : ∀ {a b : ℕ} (Φ : Mat m n → Mat a b), Continuous Φ → ∀ (i : Fin a) (j' : Fin b),
      Measurable[sigmaOthers F S t j] (fun ω => Φ (M0 ω) i j') := by
    intro a b Φ hΦ i k
    exact (((measurable_pi_apply k).comp (measurable_pi_apply i) : Measurable (fun f : Mat a b => f i k))).comp (hΦ.measurable.comp hM0)
  have hXs : Continuous (fun M : Mat m n => Muon.DetEquiv.Xs M s) := by
    unfold Muon.DetEquiv.Xs; exact (cm_Rs_continuous s hspos).matrix_mul continuous_id
  have hF := cm_four (mΩ := inst) P F.C CS γ hB hCo hCi hm hn X hlaw (sigmaOthers F S t j) hG hindc
    (fun ω => Muon.DetEquiv.Rs (M0 ω) s) (fun ω => Muon.DetEquiv.Rts (M0 ω) s)
    (fun ω => Muon.DetEquiv.Xs (M0 ω) s) (1 / s) (1 / (2 * Real.sqrt s)) (by positivity)
    (by positivity)
    (hentm _ (cm_Rs_continuous s hspos)) (hentm _ (cm_Rts_continuous s hspos)) (hentm _ hXs)
    (fun ω => (Muon.DetEquiv.lem_app_de_resolvent (M0 ω) s hspos).1)
    (fun ω => (Muon.DetEquiv.lem_app_de_resolvent (M0 ω) s hspos).2.1)
    (fun ω => (Muon.DetEquiv.lem_app_de_resolvent (M0 ω) s hspos).2.2.1)
    _ _ _ _ E1m E2m E3m E4m L1 L2 L3 L4
    (D * (|Cc| * ϖ ^ 2)) (D * s * (|Cc| * ϖ)) (D * (|Cc| * ϖ)) (D * s * (|Cc| * ϖ ^ 2 / s))
    (by positivity) (by positivity) (by positivity) (by positivity) K1 K2 K3 K4
  have hfun : (fun ω' => g ω' • (Muon.DetEquiv.Xs (ageBuf F S t j M0 ϖ ω') s -
      Muon.DetEquiv.Xs (M0 ω') s)) = fun ω =>
        Muon.DetEquiv.Rs (M0 ω) s * ((g ω * ageAlpha3 F S t j M0 ϖ s ω) •
          Muon.outer (momU F.C B (X ω)) (momU F.C B (X ω))) * Muon.DetEquiv.Xs (M0 ω) s
        + Muon.DetEquiv.Rs (M0 ω) s * ((g ω * (s * ageAlpha1 F S t j M0 ϖ s ω)) •
          Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))) * Muon.DetEquiv.Rts (M0 ω) s
        + Muon.DetEquiv.Xs (M0 ω) s * ((-(g ω * ageAlpha1 F S t j M0 ϖ s ω)) •
          Muon.outer (momV F.C B (X ω)) (momU F.C B (X ω))) * Muon.DetEquiv.Xs (M0 ω) s
        + Muon.DetEquiv.Xs (M0 ω) s * ((-(g ω * (s * ageAlpha2 F S t j M0 ϖ s ω))) •
          Muon.outer (momV F.C B (X ω)) (momV F.C B (X ω))) * Muon.DetEquiv.Rts (M0 ω) s :=
    funext fun ω => cm_decomp (ageBuf F S t j M0 ϖ ω) (M0 ω) (g ω) (ϖ * ageD F S t j ω) s
      (ageU F S t j ω) (ageV F S t j ω) rfl hspos
  rw [hfun]
  filter_upwards [hF] with ζ hζ
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB
  have hsq : Real.sqrt (γ * (B : ℝ)) = Real.sqrt γ * Real.sqrt (B : ℝ) := Real.sqrt_mul hγ _
  rw [hsq] at hζ
  have hw1 : (1 : ℝ) ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hB)
  have hBw : (B : ℝ) = Real.sqrt (B : ℝ) ^ 2 := (Real.sq_sqrt hBpos.le).symm
  generalize Real.sqrt (B : ℝ) = w at hζ hw1 hBw ⊢
  rw [hBw] at hζ
  exact hζ.trans (cm_arith s0 s w D ϖ CS |Cc| (Real.sqrt 2) (Real.sqrt γ) hs0 hs hw1 hD0 hϖ0 hϖ1
    hCS hc0 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-! ## Deletion with a bounded multiplier (`lem:app-drift-multiplier`) -/

/-- lem:app-drift-multiplier, first claim (`eqn:app-drift-multiplier`). Snapshot `cr-2026-10-23`.
LaTeX (`section.tex` l.330–344, verbatim):

\begin{lemma}[Deletion with a bounded multiplier]\label{lem:app-drift-multiplier}
Let $s_\circ>0$. In the setting of \cref{lem:app-drift-coeffmoments}, let $h$
be a scalar random variable depending on the sample $(j,a)$ and on
$\mathcal G=\mathcal G_{ja}$, with $\abs h\le D_h$ for a constant $D_h$. Then
for every $s\ge s_\circ$,
\begin{equation}\label{eqn:app-drift-multiplier}
\big\|\EE_{\mathcal G}\big[h\,(\mathsf X_s(M)-\mathsf X_s(M_0))\big]\big\|_\F\le\frac{C\,D_h\,\varpi}{s\sqrt B},
\end{equation}
with $C$ depending only on $(s_\circ,C_\Sigma,\gamma_\star)$. In particular,
for a sample of age $j$ and $s\ge s_\circ$,
\begin{equation}\label{eqn:app-drift-deletion-mean}
\norm{\mathcal H(s)-\mathcal H_j(s)}_\F\le\frac{C\,\emaw j}{s\sqrt B},\qquad
\mathcal H_j(s)\defeq\EE\,\mathsf X_0^{(j1)} .
\end{equation}
\end{lemma}
-/
theorem lem_app_drift_multiplier_i (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
      (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
        sigmaOthers F S t j] h →
      (∀ ω, |h ω| ≤ D) →
      ∀ s : ℝ, s0 ≤ s →
        ∀ᵐ ω ∂P, fro (Muon.Foundations.condExpMat (sigmaOthers F S t j) P
          (fun ω' => h ω' • (Muon.DetEquiv.Xs (ageBuf F S t j M0 ϖ ω') s -
            Muon.DetEquiv.Xs (M0 ω') s)) ω) ≤
          C * D * ϖ / (s * Real.sqrt (B : ℝ)) := by
  exact cm_i_main s0 hs0 CS γ hγ

/-! ### Private helpers for `lem_app_drift_multiplier_ii_weights` (proved; not statements) -/

open scoped MatrixOrder in
private lemma co_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * Muon.outer z w * rIn F.C =
      Muon.outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hsym : (rIn F.C)ᵀ = rIn F.C := by
    have h : (CFC.sqrt F.C.Sin)ᴴ = CFC.sqrt F.C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F.C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, hsym]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma co_sample {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) (ω : Ω) :
    (B : ℝ)⁻¹ • sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) • Muon.outer (momU F.C B (S.zw s a ω)) (momV F.C B (S.zw s a ω)) := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) •
        Muon.outer (Matrix.mulVec (rOut F.C) (S.zw s a ω).1)
          (Matrix.mulVec (rIn F.C) (S.zw s a ω).2) := by
    unfold sampleTerm
    rw [co_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

private lemma co_hQ {m n B : ℕ} (F : FrozenParams m n B) :
    Measurable (fun x : Vec m × Vec n =>
      (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)) := by
  have hdot : Measurable (fun x : Vec m × Vec n => dotProduct x.1 (Matrix.mulVec F.A x.2)) := by
    show Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * ∑ j, F.A i j * x.2 j)
    exact Finset.measurable_sum _ (fun i _ => ((measurable_pi_apply i).comp measurable_fst).mul
      (Finset.measurable_sum _ (fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp measurable_snd))))
  have hout : Continuous (fun x : Vec m × Vec n => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  have hM : Measurable (fun x : Vec m × Vec n => rOut F.C * Muon.outer x.1 x.2 * rIn F.C) :=
    Continuous.measurable ((continuous_const.matrix_mul hout).matrix_mul continuous_const)
  exact hdot.smul hM

private lemma co_meas_del {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := co_hQ F
  have hzw : ∀ p : ℤ × Fin B, p ≠ (t + 1 - (j : ℤ), slotOne F.hB) →
      Measurable[sigmaOthers F S t j] (S.zw p.1 p.2) := by
    intro p hp
    have hle : MeasurableSpace.comap (S.zw p.1 p.2) inferInstance ≤ sigmaOthers F S t j :=
      le_iSup₂ (f := fun (p : ℤ × Fin B) (_ : p ≠ (t + 1 - (j : ℤ), slotOne F.hB)) =>
        MeasurableSpace.comap (S.zw p.1 p.2) inferInstance) p hp
    exact (comap_measurable (S.zw p.1 p.2)).mono hle le_rfl
  unfold delBufAge WeightedBufDel
  letI : MeasurableSpace Ω := sigmaOthers F S t j
  refine Measurable.tsum fun j' => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j')
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j' : ℤ) = t + 1 - (j : ℤ) ∧ b = slotOne F.hB
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have hne : ((t + 1 - (j' : ℤ), b) : ℤ × Fin B) ≠ (t + 1 - (j : ℤ), slotOne F.hB) := by
      intro heq; exact h ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
    exact hQ.comp (hzw _ hne)

private lemma co_decomp {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (w : ℕ → ℝ)
    (hw : WeightClass w) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = ageBuf F S t j (delBufAge w F S t j) (w j) ω := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) j rfl ω (hω t)
  rw [h, co_sample, smul_smul]
  rfl

private lemma co_resid_meas {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    Measurable (fun ω => resid F.A (S.zw s a ω)) := by
  have hdm : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  exact hdm.comp (S.meas s a)

private lemma co_momU_meas {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    Measurable (fun ω => momU F.C B (S.zw s a ω)) := by
  have : Measurable (momU F.C B : Vec m × Vec n → Vec m) := by unfold momU; fun_prop
  exact this.comp (S.meas s a)

private lemma co_momV_meas {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    Measurable (fun ω => momV F.C B (S.zw s a ω)) := by
  have : Measurable (momV F.C B : Vec m × Vec n → Vec n) := by unfold momV; fun_prop
  exact this.comp (S.meas s a)

private lemma co_outer_meas {d d' : ℕ} {f : Ω → Vec d} {g : Ω → Vec d'} (hf : Measurable f)
    (hg : Measurable g) : Measurable (fun ω => Muon.outer (f ω) (g ω)) := by
  have hout : Continuous (fun x : Vec d × Vec d' => Muon.outer x.1 x.2) :=
    continuous_pi fun i => continuous_pi fun j =>
      ((continuous_apply i).comp continuous_fst).mul ((continuous_apply j).comp continuous_snd)
  exact hout.measurable.comp (hf.prodMk hg)

private lemma co_ageBuf_meas {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (hM0 : Measurable (delBufAge w F S t j)) :
    Measurable (fun ω => ageBuf F S t j (delBufAge w F S t j) (w j) ω) := by
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hd : Measurable (fun ω => ageD F S t j ω) :=
    co_resid_meas F S (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hu : Measurable (fun ω => ageU F S t j ω) :=
    co_momU_meas F S (t + 1 - (j : ℤ)) (slotOne F.hB)
  have hv : Measurable (fun ω => ageV F S t j ω) :=
    co_momV_meas F S (t + 1 - (j : ℤ)) (slotOne F.hB)
  exact hM0.add ((measurable_const.mul hd).smul (co_outer_meas hu hv))

private lemma co_entry_int {m n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] (s : ℝ) (hs : 0 < s)
    (X : Ω → Mat m n) (hX : Measurable X) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => Muon.DetEquiv.Xs (X ω) s i k) P := by
  have hc : Continuous (fun M : Mat m n => Muon.DetEquiv.Xs M s) := by
    unfold Muon.DetEquiv.Xs
    exact (cm_Rs_continuous s hs).matrix_mul continuous_id
  have hm : Measurable (fun ω => Muon.DetEquiv.Xs (X ω) s) := hc.measurable.comp hX
  have hme : Measurable (fun ω => Muon.DetEquiv.Xs (X ω) s i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp hm)
  refine Integrable.mono' (integrable_const (1 / (2 * Real.sqrt s))) hme.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Real.norm_eq_abs]
  exact (cm_abs_entry_le _ i k).trans ((lem_app_de_resolvent (X ω) s hs).2.2.1)

private lemma co_tower (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (hG : G ≤ mΩ) {m n : ℕ} (F : Ω → Mat m n) :
    @Muon.mean Ω mΩ _ _ P F = @Muon.mean Ω mΩ _ _ P (Muon.Foundations.condExpMat G P F) := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Muon.Foundations.condExpMat_apply]
  exact (integral_condExp hG).symm

/-- Mean of a bounded-Frobenius random matrix: `‖𝔼Y‖_F ≤ K` when `‖Y‖_F ≤ K` a.s. -/
private lemma co_fro_mean_le {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Mat m n)
    (hY : ∀ i k, Integrable (fun ω => Y ω i k) P) (K : ℝ) (hK : ∀ᵐ ω ∂P, fro (Y ω) ≤ K) :
    fro (Muon.mean P Y) ≤ K := by
  have hint : ∀ i k, Integrable (fun ω => Muon.mean P Y i k * Y ω i k) P :=
    fun i k => (hY i k).const_mul _
  have hfro0 : 0 ≤ fro (Muon.mean P Y) := Real.sqrt_nonneg _
  have hsum_int : Integrable (fun ω => ∑ i, ∑ k, Muon.mean P Y i k * Y ω i k) P :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k
  have hsq : ∫ ω, ∑ i, ∑ k, Muon.mean P Y i k * Y ω i k ∂P = fro (Muon.mean P Y) ^ 2 := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => hint i k]
    have hfro2 : fro (Muon.mean P Y) ^ 2 = ∑ i, ∑ k, Muon.mean P Y i k * Muon.mean P Y i k := by
      unfold fro
      rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity)]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Real.norm_eq_abs, sq_abs, sq]
    rw [hfro2]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ fun k _ => hint i k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    rfl
  have hpt : ∀ ω, ∑ i, ∑ k, Muon.mean P Y i k * Y ω i k ≤ fro (Muon.mean P Y) * fro (Y ω) := by
    intro ω
    have e1 : ∑ i, ∑ k, Muon.mean P Y i k * Y ω i k =
        ∑ p : Fin m × Fin n, Muon.mean P Y p.1 p.2 * Y ω p.1 p.2 :=
      (Fintype.sum_prod_type (fun p : Fin m × Fin n => Muon.mean P Y p.1 p.2 * Y ω p.1 p.2)).symm
    have eM : fro (Muon.mean P Y) = Real.sqrt (∑ p : Fin m × Fin n, Muon.mean P Y p.1 p.2 ^ 2) := by
      unfold fro
      congr 1
      simp only [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
    have eY : fro (Y ω) = Real.sqrt (∑ p : Fin m × Fin n, Y ω p.1 p.2 ^ 2) := by
      unfold fro
      congr 1
      simp only [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]
    rw [e1, eM, eY]
    exact Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun p : Fin m × Fin n => Muon.mean P Y p.1 p.2)
      (fun p : Fin m × Fin n => Y ω p.1 p.2)
  have hle : ∫ ω, ∑ i, ∑ k, Muon.mean P Y i k * Y ω i k ∂P ≤
      ∫ _ω, fro (Muon.mean P Y) * K ∂P := by
    refine integral_mono_ae hsum_int (integrable_const _) ?_
    filter_upwards [hK] with ω hω
    exact (hpt ω).trans (mul_le_mul_of_nonneg_left hω hfro0)
  rw [hsq, integral_const, probReal_univ, one_smul] at hle
  obtain ⟨ω0, hω0⟩ := hK.exists
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hω0
  rcases hfro0.eq_or_lt with h0 | hpos
  · rw [← h0]; exact hK0
  · have h2 : fro (Muon.mean P Y) * fro (Muon.mean P Y) ≤ fro (Muon.mean P Y) * K := by
      nlinarith [hle]
    exact le_of_mul_le_mul_left h2 hpos

/-- lem:app-drift-multiplier, second claim for a general weight class (`eqn:app-drift-deletion-mean`
in the form of `thm:app-drift-mixed`(ii), proof l.889–891). Snapshot `cr-2026-10-23`.

`‖𝓗(s) − 𝓗_j(s)‖_F ≤ C w_j/(s√B)` for every `w` in `WeightClass` (`eqn:app-de-weightclass`),
`𝓗_j(s) = 𝔼 𝖷_0^{(j1)}`, with `Hmix`, `Hj` of `Muon.Drift.Defs`. The constant `C` depends only on
`(s₀, C_Σ, γ⋆)`; the weight sequence is model data, quantified after `∃ C`. -/
theorem lem_app_drift_multiplier_ii_weights (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (w : ℕ → ℝ),
      WeightClass w →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        fro (Hmix w F S t s - Hj w F S t j s) ≤ C * w j / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_multiplier_i s0 hs0 CS γ hγ
  refine ⟨C, fun Ω inst m n B P _ F S t j w hw hSo hSi hm hn s hs => ?_⟩
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hG : sigmaOthers F S t j ≤ inst := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM0 : Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := co_meas_del w F S t j
  have hM0' : Measurable (delBufAge w F S t j) := hM0.mono hG le_rfl
  have hA : Measurable (fun ω => ageBuf F S t j (delBufAge w F S t j) (w j) ω) :=
    co_ageBuf_meas w F S t j hM0'
  have hdec := co_decomp (P := P) w hw F S t j
  have hcm := hC Ω m n B P F S t j (delBufAge w F S t j) (w j) 1 (fun _ => (1 : ℝ))
    hSo hSi hm hn hw0 hw1 hM0 measurable_const (fun _ => by norm_num) s hs
  simp only [one_smul, mul_one] at hcm
  have hI1 : ∀ i k, Integrable (fun ω =>
      Muon.DetEquiv.Xs (ageBuf F S t j (delBufAge w F S t j) (w j) ω) s i k) P :=
    fun i k => co_entry_int s hspos _ hA i k
  have hI0 : ∀ i k, Integrable (fun ω => Muon.DetEquiv.Xs (delBufAge w F S t j ω) s i k) P :=
    fun i k => co_entry_int s hspos _ hM0' i k
  have hI1' : ∀ i k, Integrable (fun ω => Muon.DetEquiv.Xs (WeightedBuf w F S t ω) s i k) P :=
    fun i k => (hI1 i k).congr (by
      filter_upwards [hdec] with ω hω
      simp only [hω])
  have hkey : Hmix w F S t s - Hj w F S t j s =
      Muon.mean P (fun ω => Muon.DetEquiv.Xs (ageBuf F S t j (delBufAge w F S t j) (w j) ω) s -
        Muon.DetEquiv.Xs (delBufAge w F S t j ω) s) := by
    ext i k
    simp only [Hmix, Hj, Muon.mean, Matrix.of_apply, Matrix.sub_apply]
    rw [← integral_sub (hI1' i k) (hI0 i k)]
    refine integral_congr_ae ?_
    filter_upwards [hdec] with ω hω
    simp only [hω, Matrix.sub_apply]
  rw [hkey, co_tower P (sigmaOthers F S t j) hG]
  refine co_fro_mean_le P _ (fun i k => ?_) _ hcm
  simp only [Muon.Foundations.condExpMat_apply]
  exact integrable_condExp

/-- The EMA weights `emaW β j = (1-β)β^j` lie in `WeightClass` for `β ∈ [0,1)`. -/
theorem emaW_weightClass (β : ℝ) (hβ : 0 ≤ β ∧ β < 1) : WeightClass (Muon.emaW β) := by
  obtain ⟨hb0, hb1⟩ := hβ
  have hnn : ∀ j, 0 ≤ Muon.emaW β j := fun j =>
    mul_nonneg (by linarith) (pow_nonneg hb0 j)
  have hsum : Summable (Muon.emaW β) := by
    unfold Muon.emaW
    exact (summable_geometric_of_lt_one hb0 hb1).mul_left (1 - β)
  have htsum : ∑' j, Muon.emaW β j = 1 := by
    unfold Muon.emaW
    rw [tsum_mul_left, tsum_geometric_of_lt_one hb0 hb1]
    have : (1 - β) ≠ 0 := by linarith
    exact mul_inv_cancel₀ this
  refine ⟨⟨hnn, hsum, ⟨0, ?_⟩⟩, ?_, htsum.le⟩
  · have : 0 < Muon.emaW β 0 := by
      unfold Muon.emaW
      rw [pow_zero, mul_one]
      linarith
    exact ne_of_gt this
  · intro j
    have h1 : β ^ j ≤ 1 := pow_le_one₀ hb0 hb1.le
    have h2 : 0 ≤ β ^ j := pow_nonneg hb0 j
    unfold Muon.emaW
    nlinarith

/-- lem:app-drift-multiplier, second claim at the EMA weights (`eqn:app-drift-deletion-mean`, the
source's `emaw j`): corollary of `lem_app_drift_multiplier_ii_weights` with `w = emaW β`. -/
theorem lem_app_drift_multiplier_ii (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        fro (Hmix (Muon.emaW F.β) F S t s - Hj (Muon.emaW F.β) F S t j s) ≤
          C * Muon.emaW F.β j / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_multiplier_ii_weights s0 hs0 CS γ hγ
  refine ⟨C, fun Ω _ m n B P _ F S t j hSo hSi hm hn s hs => ?_⟩
  exact hC Ω m n B P F S t j (Muon.emaW F.β) (emaW_weightClass F.β F.hβ) hSo hSi hm hn s hs

/-! ## Rank sensitivity of the conditional Gram coefficient (`lem:app-drift-rank`) -/

/-! ### Private helpers for `lem_app_drift_rank` (proved; not statements) -/

private lemma dr_dL (s N U U' V C C' Λ Λ' V' q A a h X Y Z : ℝ) (hspos : 0 < s)
    (hN : 0 ≤ N) (hq : 0 ≤ q)
    (hΛ : Λ = (1 + h * C) ^ 2 + s * h ^ 2 * U * V)
    (hΛ' : Λ' = (1 + h * C') ^ 2 + s * h ^ 2 * U' * V')
    (hX : X = |U - U'|) (hY : Y = |V - V'|) (hZ : Z = |C - C'|)
    (ha0 : 0 ≤ a) (hA1 : 1 ≤ A) (haA : a ≤ A) (hNA : N ≤ A) (hha : |h| ≤ a)
    (hU' : s * |U'| ≤ N) (hV : s * |V| ≤ N)
    (hC : |C| ≤ q * N) (hC' : |C'| ≤ q * N) :
    |Λ - Λ'| ≤ A ^ 3 * (3 + 2 * q) * (X + Y + Z) := by
  have hX0 : 0 ≤ X := by rw [hX]; exact abs_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; exact abs_nonneg _
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact abs_nonneg _
  have hid2 : Λ - Λ' = h * (C - C') * (2 + h * (C + C')) +
      s * h ^ 2 * (V * (U - U') + U' * (V - V')) := by
    rw [hΛ, hΛ']; ring
  have hCC : |C + C'| ≤ 2 * q * N := by
    calc |C + C'| ≤ |C| + |C'| := abs_add_le _ _
      _ ≤ 2 * q * N := by linarith
  rw [hid2]
  have t1 : |h * (C - C') * (2 + h * (C + C'))| ≤ A * (2 + 2 * q * A ^ 2) * Z := by
    rw [abs_mul, abs_mul, ← hZ]
    have e1 : |2 + h * (C + C')| ≤ 2 + 2 * q * A ^ 2 := by
      calc |2 + h * (C + C')| ≤ |(2:ℝ)| + |h * (C + C')| := abs_add_le _ _
        _ ≤ 2 + 2 * q * A ^ 2 := by
          rw [abs_mul]
          have : |h| * |C + C'| ≤ a * (2 * q * N) :=
            mul_le_mul hha hCC (abs_nonneg _) ha0
          have haN : a * N ≤ A ^ 2 := by
            have := mul_le_mul haA hNA hN (by linarith)
            rw [sq]; exact this
          have h2 : a * (2 * q * N) ≤ 2 * q * A ^ 2 := by
            calc a * (2 * q * N) = (2 * q) * (a * N) := by ring
              _ ≤ (2 * q) * A ^ 2 := mul_le_mul_of_nonneg_left haN (by positivity)
          have h3 : |(2:ℝ)| = 2 := abs_of_pos (by norm_num)
          rw [h3]
          linarith
    calc |h| * Z * |2 + h * (C + C')| ≤ A * Z * (2 + 2 * q * A ^ 2) := by
          apply mul_le_mul (mul_le_mul (hha.trans haA) le_rfl hZ0 (by linarith)) e1
            (abs_nonneg _) (by positivity)
      _ = A * (2 + 2 * q * A ^ 2) * Z := by ring
  have t2 : |s * h ^ 2 * (V * (U - U') + U' * (V - V'))| ≤ A ^ 3 * (X + Y) := by
    rw [abs_mul, abs_mul, abs_of_pos hspos, abs_of_nonneg (sq_nonneg h)]
    have e2 : |V * (U - U') + U' * (V - V')| * s ≤ N * (X + Y) := by
      calc |V * (U - U') + U' * (V - V')| * s ≤ (|V| * X + |U'| * Y) * s := by
            apply mul_le_mul_of_nonneg_right _ hspos.le
            calc _ ≤ |V * (U - U')| + |U' * (V - V')| := abs_add_le _ _
              _ = _ := by rw [abs_mul, abs_mul, hX, hY]
        _ = (s * |V|) * X + (s * |U'|) * Y := by ring
        _ ≤ N * X + N * Y := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_right hV hX0
            · exact mul_le_mul_of_nonneg_right hU' hY0
        _ = N * (X + Y) := by ring
    have hh3 : h ^ 2 ≤ A ^ 2 := by
      calc h ^ 2 ≤ a ^ 2 := by rw [← sq_abs h]; exact pow_le_pow_left₀ (abs_nonneg _) hha 2
        _ ≤ A ^ 2 := pow_le_pow_left₀ ha0 haA 2
    calc s * h ^ 2 * |V * (U - U') + U' * (V - V')| =
          h ^ 2 * (|V * (U - U') + U' * (V - V')| * s) := by ring
      _ ≤ A ^ 2 * (N * (X + Y)) := by
          apply mul_le_mul hh3 e2 (by positivity) (by positivity)
      _ ≤ A ^ 3 * (X + Y) := by
          have : A ^ 2 * N ≤ A ^ 3 := by
            rw [pow_succ]; exact mul_le_mul_of_nonneg_left hNA (by positivity)
          calc A ^ 2 * (N * (X + Y)) = (A ^ 2 * N) * (X + Y) := by ring
            _ ≤ A ^ 3 * (X + Y) := mul_le_mul_of_nonneg_right this (add_nonneg hX0 hY0)
  calc _ ≤ |h * (C - C') * (2 + h * (C + C'))| +
        |s * h ^ 2 * (V * (U - U') + U' * (V - V'))| := abs_add_le _ _
    _ ≤ A * (2 + 2 * q * A ^ 2) * Z + A ^ 3 * (X + Y) := add_le_add t1 t2
    _ ≤ A ^ 3 * (3 + 2 * q) * (X + Y + Z) := by
        have hA3 : A ≤ A ^ 3 := le_self_pow₀ hA1 (by norm_num)
        have hq3 : A * (2 + 2 * q * A ^ 2) ≤ A ^ 3 * (2 + 2 * q) := by
          have e1 : A * (2 + 2 * q * A ^ 2) = 2 * A + 2 * q * A ^ 3 := by ring
          have e2 : A ^ 3 * (2 + 2 * q) = 2 * A ^ 3 + 2 * q * A ^ 3 := by ring
          rw [e1, e2]; linarith
        have h1 := mul_le_mul_of_nonneg_right hq3 hZ0
        have key : A ^ 3 * (3 + 2 * q) * (X + Y + Z) -
            (A ^ 3 * (2 + 2 * q) * Z + A ^ 3 * (X + Y)) =
            A ^ 3 * ((2 + 2 * q) * (X + Y) + Z) := by ring
        have key0 : 0 ≤ A ^ 3 * ((2 + 2 * q) * (X + Y) + Z) := by positivity
        linarith

set_option maxHeartbeats 800000 in
private lemma dr_alg (s0 s ϖ d N U U' V C C' Λ Λ' V' q c1 : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s)
    (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) (hN : 0 ≤ N) (hq : 0 ≤ q) (hc1 : 1 ≤ c1)
    (hΛ : Λ = (1 + ϖ * d * C) ^ 2 + s * (ϖ * d) ^ 2 * U * V)
    (hΛ' : Λ' = (1 + ϖ * d * C') ^ 2 + s * (ϖ * d) ^ 2 * U' * V')
    (hΛp : 0 < Λ) (hΛ'p : 0 < Λ')
    (hΛi : Λ⁻¹ ≤ (c1 * ((1 + |d|) * (1 + N))) ^ 2)
    (hΛ'i : Λ'⁻¹ ≤ (c1 * ((1 + |d|) * (1 + N))) ^ 2)
    (hU' : s * |U'| ≤ N) (hV : s * |V| ≤ N)
    (hC : |C| ≤ q * N) (hC' : |C'| ≤ q * N) :
    |(ϖ * d) ^ 2 * U / Λ - (ϖ * d) ^ 2 * U' / Λ'| ≤
      ϖ ^ 2 * (c1 ^ 2 + c1 ^ 4 * (3 + 2 * q) / s0) * ((1 + |d|) * (1 + N)) ^ 10 *
        (|U - U'| + |V - V'| + |C - C'|) := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = |d| := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; exact abs_nonneg d
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (1 + a) * (1 + N) := ⟨_, rfl⟩
  rw [← ha, ← hA] at hΛi hΛ'i
  rw [← ha, ← hA]
  have hA1 : 1 ≤ A := by rw [hA]; nlinarith
  have haA : a ≤ A := by rw [hA]; nlinarith
  have hNA : N ≤ A := by rw [hA]; nlinarith
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ϖ * d := ⟨_, rfl⟩
  rw [← hh] at hΛ hΛ' ⊢
  have hha : |h| ≤ a := by
    rw [hh, ha, abs_mul, abs_of_nonneg hϖ0]; exact mul_le_of_le_one_left (abs_nonneg d) hϖ1
  have hh2 : h ^ 2 ≤ ϖ ^ 2 * a ^ 2 := by
    rw [hh, ha, mul_pow, sq_abs]
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = |U - U'| := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = |V - V'| := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = |C - C'| := ⟨_, rfl⟩
  rw [← hX, ← hY, ← hZ]
  have hX0 : 0 ≤ X := by rw [hX]; exact abs_nonneg _
  have hY0 : 0 ≤ Y := by rw [hY]; exact abs_nonneg _
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact abs_nonneg _
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hU'0 : |U'| ≤ N / s0 := by
    rw [le_div_iff₀ hs0]; nlinarith [abs_nonneg U']
  have hid1 : h ^ 2 * U / Λ - h ^ 2 * U' / Λ' =
      h ^ 2 * ((U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')) := by
    field_simp
    ring
  have hid2 : Λ - Λ' = h * (C - C') * (2 + h * (C + C')) +
      s * h ^ 2 * (V * (U - U') + U' * (V - V')) := by
    rw [hΛ, hΛ']; ring
  have hCC : |C + C'| ≤ 2 * q * N := by
    calc |C + C'| ≤ |C| + |C'| := abs_add_le _ _
      _ ≤ 2 * q * N := by linarith
  have hdL : |Λ - Λ'| ≤ A ^ 3 * (3 + 2 * q) * (X + Y + Z) :=
    dr_dL s N U U' V C C' Λ Λ' V' q A a h X Y Z hspos hN hq hΛ hΛ' hX hY hZ ha0 hA1 haA hNA
      hha hU' hV hC hC'
  -- assemble
  rw [hid1, abs_mul, abs_of_nonneg (sq_nonneg h)]
  have hS0 : 0 ≤ X + Y + Z := by positivity
  have hLi0 : 0 ≤ Λ⁻¹ := inv_nonneg.2 hΛp.le
  have hLi0' : 0 ≤ Λ'⁻¹ := inv_nonneg.2 hΛ'p.le
  have hcA : 0 ≤ (c1 * A) ^ 2 := sq_nonneg _
  have hT1 : |(U - U') / Λ| ≤ (c1 * A) ^ 2 * X := by
    rw [abs_div, abs_of_pos hΛp, div_eq_mul_inv, mul_comm, ← hX]
    exact mul_le_mul hΛi le_rfl hX0 hcA
  have hT2 : |U' * (Λ - Λ') / (Λ * Λ')| ≤ (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) := by
    rw [abs_div, abs_of_pos (mul_pos hΛp hΛ'p), div_eq_mul_inv, mul_inv, abs_mul]
    rw [mul_comm]
    have : (Λ⁻¹ * Λ'⁻¹) ≤ (c1 * A) ^ 2 * (c1 * A) ^ 2 :=
      mul_le_mul hΛi hΛ'i hLi0' hcA
    have h2 : |U'| * |Λ - Λ'| ≤ (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) :=
      mul_le_mul hU'0 hdL (abs_nonneg _) (by positivity)
    calc Λ⁻¹ * Λ'⁻¹ * (|U'| * |Λ - Λ'|) ≤ ((c1 * A) ^ 2 * (c1 * A) ^ 2) *
          ((N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z))) :=
          mul_le_mul this h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hsum : |(U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')| ≤
      (c1 * A) ^ 2 * X + (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) :=
    (abs_sub _ _).trans (add_le_add hT1 hT2)
  have hA10 : A ^ 4 ≤ A ^ 10 := pow_le_pow_right₀ hA1 (by norm_num)
  have hS0' : 0 ≤ X + Y + Z := hS0
  have hA8 : A ^ 2 ≤ A ^ 8 := pow_le_pow_right₀ hA1 (by norm_num)
  have hK1 : 0 ≤ c1 ^ 2 := by positivity
  have hK2 : 0 ≤ c1 ^ 4 * (3 + 2 * q) / s0 := by positivity
  have e1 : (c1 * A) ^ 2 * X ≤ c1 ^ 2 * A ^ 8 * (X + Y + Z) := by
    have : X ≤ X + Y + Z := by linarith
    calc (c1 * A) ^ 2 * X = (c1 ^ 2 * A ^ 2) * X := by ring
      _ ≤ (c1 ^ 2 * A ^ 8) * (X + Y + Z) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA8 hK1) this hX0 (by positivity)
  have e2 : (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) * ((c1 * A) ^ 2 * (c1 * A) ^ 2) ≤
      (c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
    have hNA7 : N * A ^ 7 ≤ A ^ 8 := by
      rw [pow_succ A 7, mul_comm (A ^ 7) A]
      exact mul_le_mul_of_nonneg_right hNA (by positivity)
    calc (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) * ((c1 * A) ^ 2 * (c1 * A) ^ 2)
        = (c1 ^ 4 * (3 + 2 * q) / s0) * (N * A ^ 7) * (X + Y + Z) := by
          field_simp
      _ ≤ (c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
          apply mul_le_mul_of_nonneg_right _ hS0
          exact mul_le_mul_of_nonneg_left hNA7 hK2
  have hkey : (c1 * A) ^ 2 * X + (N / s0) * (A ^ 3 * (3 + 2 * q) * (X + Y + Z)) *
      ((c1 * A) ^ 2 * (c1 * A) ^ 2) ≤
      (c1 ^ 2 + c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by
    have := add_le_add e1 e2
    calc _ ≤ _ := this
      _ = _ := by ring
  have hT0 : 0 ≤ (c1 ^ 2 + c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 8 * (X + Y + Z) := by positivity
  calc h ^ 2 * |(U - U') / Λ - U' * (Λ - Λ') / (Λ * Λ')|
      ≤ (ϖ ^ 2 * A ^ 2) * ((c1 ^ 2 + c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 8 * (X + Y + Z)) := by
        apply mul_le_mul _ (hsum.trans hkey) (abs_nonneg _) (by positivity)
        calc h ^ 2 ≤ ϖ ^ 2 * a ^ 2 := hh2
          _ ≤ ϖ ^ 2 * A ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha0 haA 2) (sq_nonneg _)
    _ = ϖ ^ 2 * (c1 ^ 2 + c1 ^ 4 * (3 + 2 * q) / s0) * A ^ 10 * (X + Y + Z) := by ring

private lemma dr_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f g : α → ℝ) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Integrable (fun x => f x * g x) μ ∧
    ∫ x, f x * g x ∂μ ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  refine ⟨hf.integrable_mul hg, ?_⟩
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ) (p := 2) (q := 2)
    (by exact Real.HolderConjugate.two_two) (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hg0) (by simpa using hf) (by simpa using hg)
  simp only [Real.rpow_two, one_div] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  simpa using h

private lemma dr_isUnit {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    IsUnit (K * Kᵀ + s • (1 : Mat a a)).det := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  have h3 := Matrix.PosDef.add_posSemidef h2 h1
  rw [add_comm]
  exact isUnit_iff_ne_zero.mpr h3.det_pos.ne'

private lemma dr_rank_add {k l : ℕ} (A B : Mat k l) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rw [Matrix.mulVecLin_add]
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private lemma dr_rank_neg {k l : ℕ} (A : Mat k l) : (-A).rank = A.rank := by
  unfold Matrix.rank
  have : Matrix.mulVecLin (-A) = -Matrix.mulVecLin A := by
    ext x i; simp
  rw [this, LinearMap.range_neg]

private lemma dr_rank_sub {k l : ℕ} (A B : Mat k l) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg]
  have := dr_rank_add A (-B)
  rwa [dr_rank_neg] at this

private lemma dr_rank_sub_comm {k l : ℕ} (A B : Mat k l) : (A - B).rank = (B - A).rank := by
  rw [← neg_sub, dr_rank_neg]

/-- rank of the resolvent difference -/
private lemma dr_rank_Rs {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) :
    (Rs K s - Rs K' s).rank ≤ 2 * (K - K').rank := by
  have hG : (K * Kᵀ + s • (1 : Mat m m))⁻¹ * (K * Kᵀ + s • (1 : Mat m m)) = 1 :=
    Matrix.nonsing_inv_mul _ (dr_isUnit K s hs)
  have hG' : (K' * K'ᵀ + s • (1 : Mat m m)) * (K' * K'ᵀ + s • (1 : Mat m m))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (dr_isUnit K' s hs)
  have e : Rs K s - Rs K' s = Rs K s * (K' * K'ᵀ - K * Kᵀ) * Rs K' s := by
    unfold Rs
    have h1 : K' * K'ᵀ - K * Kᵀ = (K' * K'ᵀ + s • (1 : Mat m m)) - (K * Kᵀ + s • (1 : Mat m m)) := by
      abel
    rw [h1, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hG', Matrix.mul_one, hG,
      Matrix.one_mul]
  have e2 : K' * K'ᵀ - K * Kᵀ = (K' - K) * K'ᵀ + K * (K' - K)ᵀ := by
    simp only [Matrix.transpose_sub, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e]
  refine (Matrix.rank_mul_le_left _ _).trans ?_
  refine (Matrix.rank_mul_le_right _ _).trans ?_
  rw [e2]
  refine (dr_rank_add _ _).trans ?_
  have r1 : ((K' - K) * K'ᵀ).rank ≤ (K - K').rank := by
    rw [dr_rank_sub_comm]; exact Matrix.rank_mul_le_left _ _
  have r2 : (K * (K' - K)ᵀ).rank ≤ (K - K').rank := by
    refine (Matrix.rank_mul_le_right _ _).trans ?_
    rw [Matrix.rank_transpose, dr_rank_sub_comm]
  omega

private lemma dr_rank_Rts {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) :
    (Rts K s - Rts K' s).rank ≤ 2 * (K - K').rank := by
  have h := dr_rank_Rs Kᵀ K'ᵀ s hs
  have e1 : Rs Kᵀ s = Rts K s := by unfold Rs Rts; rw [Matrix.transpose_transpose]
  have e2 : Rs K'ᵀ s = Rts K' s := by unfold Rs Rts; rw [Matrix.transpose_transpose]
  rw [e1, e2, ← Matrix.transpose_sub, Matrix.rank_transpose] at h
  exact h

private lemma dr_rank_Xs {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) :
    (Xs K s - Xs K' s).rank ≤ 3 * (K - K').rank := by
  have e : Xs K s - Xs K' s = (Rs K s - Rs K' s) * K + Rs K' s * (K - K') := by
    unfold Xs; simp only [Matrix.sub_mul, Matrix.mul_sub]; abel
  rw [e]
  refine (dr_rank_add _ _).trans ?_
  have h1 := Matrix.rank_mul_le_left (Rs K s - Rs K' s) K
  have h2 := Matrix.rank_mul_le_right (Rs K' s) (K - K')
  have h3 := dr_rank_Rs K K' s hs
  omega

open scoped Matrix.Norms.L2Operator in
private lemma dr_opNorm_sub {a b : ℕ} (A B : Mat a b) : opNorm (A - B) ≤ opNorm A + opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_sub_le _ _

private lemma dr_nuc_Rs {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) (k : ℕ)
    (hk : (K - K').rank ≤ k) : nuc (Rs K s - Rs K' s) ≤ 4 * k / s := by
  have h1 := nuc_le_rank_mul_opNorm (Rs K s - Rs K' s)
  have h2 := dr_rank_Rs K K' s hs
  have h3 := dr_opNorm_sub (Rs K s) (Rs K' s)
  have r1 := (lem_app_de_resolvent K s hs).1
  have r2 := (lem_app_de_resolvent K' s hs).1
  have hr : ((Rs K s - Rs K' s).rank : ℝ) ≤ 2 * k := by
    exact_mod_cast h2.trans (by omega)
  have ho : opNorm (Rs K s - Rs K' s) ≤ 2 / s := by
    calc _ ≤ 1 / s + 1 / s := h3.trans (add_le_add r1 r2)
      _ = 2 / s := by ring
  have hon : 0 ≤ opNorm (Rs K s - Rs K' s) := by unfold opNorm; exact norm_nonneg _
  calc nuc (Rs K s - Rs K' s) ≤ _ := h1
    _ ≤ (2 * k) * (2 / s) := mul_le_mul hr ho hon (by positivity)
    _ = 4 * k / s := by ring

private lemma dr_nuc_Rts {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) (k : ℕ)
    (hk : (K - K').rank ≤ k) : nuc (Rts K s - Rts K' s) ≤ 4 * k / s := by
  have h1 := nuc_le_rank_mul_opNorm (Rts K s - Rts K' s)
  have h2 := dr_rank_Rts K K' s hs
  have h3 := dr_opNorm_sub (Rts K s) (Rts K' s)
  have r1 := (lem_app_de_resolvent K s hs).2.1
  have r2 := (lem_app_de_resolvent K' s hs).2.1
  have hr : ((Rts K s - Rts K' s).rank : ℝ) ≤ 2 * k := by
    exact_mod_cast h2.trans (by omega)
  have ho : opNorm (Rts K s - Rts K' s) ≤ 2 / s := by
    calc _ ≤ 1 / s + 1 / s := h3.trans (add_le_add r1 r2)
      _ = 2 / s := by ring
  have hon : 0 ≤ opNorm (Rts K s - Rts K' s) := by unfold opNorm; exact norm_nonneg _
  calc nuc (Rts K s - Rts K' s) ≤ _ := h1
    _ ≤ (2 * k) * (2 / s) := mul_le_mul hr ho hon (by positivity)
    _ = 4 * k / s := by ring

private lemma dr_nuc_Xs {m n : ℕ} (K K' : Mat m n) (s : ℝ) (hs : 0 < s) (k : ℕ)
    (hk : (K - K').rank ≤ k) : nuc (Xs K s - Xs K' s) ≤ 3 * k / Real.sqrt s := by
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have h1 := nuc_le_rank_mul_opNorm (Xs K s - Xs K' s)
  have h2 := dr_rank_Xs K K' s hs
  have h3 := dr_opNorm_sub (Xs K s) (Xs K' s)
  have r1 := (lem_app_de_resolvent K s hs).2.2.1
  have r2 := (lem_app_de_resolvent K' s hs).2.2.1
  have hr : ((Xs K s - Xs K' s).rank : ℝ) ≤ 3 * k := by
    exact_mod_cast h2.trans (by omega)
  have ho : opNorm (Xs K s - Xs K' s) ≤ 1 / Real.sqrt s := by
    calc _ ≤ 1 / (2 * Real.sqrt s) + 1 / (2 * Real.sqrt s) := h3.trans (add_le_add r1 r2)
      _ = 1 / Real.sqrt s := by field_simp; ring
  have hon : 0 ≤ opNorm (Xs K s - Xs K' s) := by unfold opNorm; exact norm_nonneg _
  calc nuc (Xs K s - Xs K' s) ≤ _ := h1
    _ ≤ (3 * k) * (1 / Real.sqrt s) := mul_le_mul hr ho hon (by positivity)
    _ = 3 * k / Real.sqrt s := by ring

private lemma dr_opNorm_one (d : ℕ) : opNorm (1 : Mat d d) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simp

private lemma dr_fro_sq_eq_trace {k l : ℕ} (A : Mat k l) : fro A ^ 2 = (Aᵀ * A).trace := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, abs_mul_abs_self, sq]
  rw [Finset.sum_comm]

private lemma dr_fro_le_nuc {k l : ℕ} (A : Mat k l) : fro A ≤ nuc A := by
  have h1 := trace_mul_le_opNorm_mul_nuc Aᵀ A
  have h2 := opNorm_le_nuc A
  rw [bf_opNorm_transpose] at h1
  have h0 : 0 ≤ fro A := Real.sqrt_nonneg _
  have h3 : fro A ^ 2 ≤ nuc A ^ 2 := by
    rw [dr_fro_sq_eq_trace]
    calc _ ≤ |(Aᵀ * A).trace| := le_abs_self _
      _ ≤ opNorm A * nuc A := h1
      _ ≤ nuc A * nuc A := mul_le_mul_of_nonneg_right h2 (nuc_nonneg A)
      _ = nuc A ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ h0 (nuc_nonneg A) two_ne_zero).mp h3

private lemma dr_trace_le_nuc {d : ℕ} (A : Mat d d) : |A.trace| ≤ nuc A := by
  have h1 := trace_mul_le_opNorm_mul_nuc (1 : Mat d d) A
  rw [Matrix.one_mul] at h1
  exact h1.trans (by
    calc opNorm (1 : Mat d d) * nuc A ≤ 1 * nuc A :=
          mul_le_mul_of_nonneg_right (dr_opNorm_one d) (nuc_nonneg A)
      _ = nuc A := one_mul _)

/-- symmetrization -/
private lemma dr_sym_nuc {d : ℕ} (D : Mat d d) : nuc ((1 / 2 : ℝ) • (D + Dᵀ)) ≤ nuc D := by
  rw [nuc_smul]
  have := nuc_add_le D Dᵀ
  rw [nuc_transpose] at this
  rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  linarith

private lemma dr_quad_eq {d : ℕ} (D : Mat d d) (z : Vec d) :
    dotProduct z (D *ᵥ z) = dotProduct z (((1 / 2 : ℝ) • (D + Dᵀ)) *ᵥ z) := by
  have h : dotProduct z (Dᵀ *ᵥ z) = dotProduct z (D *ᵥ z) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, h]
  simp only [smul_eq_mul]
  ring

private lemma dr_quad_sq {d : ℕ} (D : Mat d d) :
    Integrable (fun z : Vec d => (dotProduct z (D *ᵥ z)) ^ 2) (Muon.Foundations.stdGaussianPi d) ∧
    ∫ z, (dotProduct z (D *ᵥ z)) ^ 2 ∂(Muon.Foundations.stdGaussianPi d) ≤ 3 * nuc D ^ 2 := by
  obtain ⟨Ds, hDs⟩ : ∃ Ds : Mat d d, Ds = (1 / 2 : ℝ) • (D + Dᵀ) := ⟨_, rfl⟩
  have hsymm : Ds.IsSymm := by
    unfold Matrix.IsSymm
    rw [hDs, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hQe : ∀ z : Vec d, dotProduct z (D *ᵥ z) = dotProduct z (Ds *ᵥ z) := by
    intro z; rw [hDs]; exact dr_quad_eq D z
  have e : ∀ z : Vec d, dotProduct z (Ds *ᵥ z) = ∑ i, ∑ j, Ds i j * (z i * z j) := by
    intro z
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hmem : MemLp (fun z : Vec d => dotProduct z (Ds *ᵥ z)) 2
      (Muon.Foundations.stdGaussianPi d) := by
    have e' : (fun z : Vec d => dotProduct z (Ds *ᵥ z)) =
        fun z => ∑ i, ∑ j, Ds i j * (z i * z j) := funext e
    rw [e']
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    refine MemLp.const_mul ?_ _
    have hm : Measurable (fun z : Vec d => z i * z j) := by fun_prop
    rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
    have := bf_gfour i j i j
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only; ring
  have hsq := hmem.integrable_sq
  have hQ : (fun z : Vec d => (dotProduct z (D *ᵥ z)) ^ 2) =
      fun z => (dotProduct z (Ds *ᵥ z)) ^ 2 := by
    funext z; rw [hQe]
  rw [hQ]
  refine ⟨hsq, ?_⟩
  have hvar := lem_app_de_moments_v Ds hsymm
  have hmean := lem_app_de_moments_iv Ds hsymm
  rw [variance_eq_sub hmem, hmean] at hvar
  have h1 : ∫ z, (dotProduct z (Ds *ᵥ z)) ^ 2 ∂(Muon.Foundations.stdGaussianPi d) =
      2 * fro Ds ^ 2 + Ds.trace ^ 2 := by
    have : (fun z : Vec d => dotProduct z (Ds *ᵥ z)) ^ 2 = fun z => (dotProduct z (Ds *ᵥ z)) ^ 2 := by
      funext z; simp
    rw [this] at hvar
    linarith
  rw [h1]
  have hn : nuc Ds ≤ nuc D := by rw [hDs]; exact dr_sym_nuc D
  have hf := dr_fro_le_nuc Ds
  have ht := dr_trace_le_nuc Ds
  have hf2 : fro Ds ^ 2 ≤ nuc D ^ 2 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (hf.trans hn) 2
  have ht2 : Ds.trace ^ 2 ≤ nuc D ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (ht.trans hn) 2
  linarith

private lemma dr_bil_inner {m n : ℕ} (E : Mat m n) (z : Vec m) :
    ∫ w, (dotProduct z (E *ᵥ w)) ^ 2 ∂(Muon.Foundations.stdGaussianPi n) =
      ∑ j, (∑ i, z i * E i j) ^ 2 := by
  have e1 : ∀ w : Vec n, (dotProduct z (E *ᵥ w)) ^ 2 =
      ∑ j, ∑ l, w j * (Matrix.of (fun a b : Fin n => (∑ i, z i * E i a) * (∑ i, z i * E i b))) j l * w l := by
    intro w
    have h1 : dotProduct z (E *ᵥ w) = ∑ j, (∑ i, z i * E i j) * w j := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.of_apply]; ring
  simp_rw [e1]
  rw [Muon.Foundations.stdGaussianPi_quadratic_mean n]
  simp [Matrix.trace, sq]

private lemma dr_bil_outer {m n : ℕ} (E : Mat m n) :
    ∫ z, ∑ j, (∑ i, z i * E i j) ^ 2 ∂(Muon.Foundations.stdGaussianPi m) = fro E ^ 2 := by
  have e1 : ∀ z : Vec m, ∑ j, (∑ i, z i * E i j) ^ 2 =
      ∑ i, ∑ k, z i * (E * Eᵀ) i k * z k := by
    intro z
    simp only [sq, Finset.sum_mul_sum, Matrix.mul_apply, Matrix.transpose_apply, Finset.mul_sum,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e1]
  rw [Muon.Foundations.stdGaussianPi_quadratic_mean m, dr_fro_sq_eq_trace, Matrix.trace_mul_comm]

private lemma dr_bil_sq {m n : ℕ} (E : Mat m n) :
    Integrable (fun x : Vec m × Vec n => (dotProduct x.1 (E *ᵥ x.2)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct x.1 (E *ᵥ x.2)) ^ 2 ∂(gaussPair m n) ≤ nuc E ^ 2 := by
  have e : ∀ x : Vec m × Vec n, dotProduct x.1 (E *ᵥ x.2) = ∑ i, ∑ j, E i j * (x.1 i * x.2 j) := by
    intro x
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hmem : MemLp (fun x : Vec m × Vec n => dotProduct x.1 (E *ᵥ x.2)) 2 (gaussPair m n) := by
    have e' : (fun x : Vec m × Vec n => dotProduct x.1 (E *ᵥ x.2)) =
        fun x => ∑ i, ∑ j, E i j * (x.1 i * x.2 j) := funext e
    rw [e']
    refine memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => ?_
    exact MemLp.const_mul (bf_gfam1_memLp m n (i, j)) _
  have hint := hmem.integrable_sq
  refine ⟨hint, ?_⟩
  have hprod : ∫ x, (dotProduct x.1 (E *ᵥ x.2)) ^ 2 ∂(gaussPair m n) =
      ∫ z, ∫ w, (dotProduct z (E *ᵥ w)) ^ 2 ∂(Muon.Foundations.stdGaussianPi n)
        ∂(Muon.Foundations.stdGaussianPi m) := by
    unfold gaussPair
    exact integral_prod (fun x : Vec m × Vec n => (dotProduct x.1 (E *ᵥ x.2)) ^ 2) hint
  rw [hprod]
  simp_rw [dr_bil_inner]
  rw [dr_bil_outer]
  have := dr_fro_le_nuc E
  have h0 : 0 ≤ fro E := Real.sqrt_nonneg _
  exact pow_le_pow_left₀ h0 this 2

private lemma dr_fst_map (m n : ℕ) :
    (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
  unfold gaussPair
  rw [Measure.map_fst_prod]; simp

private lemma dr_snd_map (m n : ℕ) :
    (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
  unfold gaussPair
  rw [Measure.map_snd_prod]; simp

private lemma dr_fst_transfer {m n : ℕ} (φ : Vec m → ℝ) (hφ : Measurable φ)
    (h : Integrable φ (Muon.Foundations.stdGaussianPi m)) :
    Integrable (fun x : Vec m × Vec n => φ x.1) (gaussPair m n) ∧
      ∫ x, φ x.1 ∂(gaussPair m n) = ∫ z, φ z ∂(Muon.Foundations.stdGaussianPi m) := by
  have hm : Measurable (Prod.fst : Vec m × Vec n → Vec m) := measurable_fst
  have h' : Integrable φ ((gaussPair m n).map Prod.fst) := by rw [dr_fst_map]; exact h
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).mp h', ?_⟩
  rw [← dr_fst_map m n]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

private lemma dr_snd_transfer {m n : ℕ} (φ : Vec n → ℝ) (hφ : Measurable φ)
    (h : Integrable φ (Muon.Foundations.stdGaussianPi n)) :
    Integrable (fun x : Vec m × Vec n => φ x.2) (gaussPair m n) ∧
      ∫ x, φ x.2 ∂(gaussPair m n) = ∫ z, φ z ∂(Muon.Foundations.stdGaussianPi n) := by
  have hm : Measurable (Prod.snd : Vec m × Vec n → Vec n) := measurable_snd
  have h' : Integrable φ ((gaussPair m n).map Prod.snd) := by rw [dr_snd_map]; exact h
  refine ⟨(integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable).mp h', ?_⟩
  rw [← dr_snd_map m n]
  exact (integral_map hm.aemeasurable hφ.aestronglyMeasurable).symm

private lemma dr_dot_mulVec {a b : ℕ} (R : Mat a b) (z : Vec b) (y : Vec a) :
    dotProduct (R *ᵥ z) y = dotProduct z (Rᵀ *ᵥ y) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]

/-- scaled quadratic form: `uᵀ D u = zᵀ ((1/B) Rᵀ D R) z`. -/
private lemma dr_quad_scaled {a : ℕ} (c : ℝ) (R D : Mat a a) (z : Vec a) :
    dotProduct (c • (R *ᵥ z)) (D *ᵥ (c • (R *ᵥ z))) =
      dotProduct z (((c * c) • (Rᵀ * D * R)) *ᵥ z) := by
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dr_dot_mulVec,
    Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [smul_eq_mul]
  ring

private lemma dr_nuc_scaled {a : ℕ} (c : ℝ) (R D : Mat a a) :
    nuc ((c * c) • (Rᵀ * D * R)) ≤ (c * c) * (opNorm R * opNorm R * nuc D) := by
  rw [nuc_smul, abs_of_nonneg (mul_self_nonneg c)]
  have := nuc_mul_three_le Rᵀ D R
  rw [bf_opNorm_transpose] at this
  exact mul_le_mul_of_nonneg_left (this.trans_eq (by ring)) (mul_self_nonneg c)

private lemma dr_L2U {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSo : opNorm C.Sout ≤ CS) (D : Mat m m) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2 ∂(gaussPair m n) ≤
      3 * (CS / B * nuc D) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat m m := (c * c) • ((rOut C)ᵀ * D * rOut C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momU C B x) (D *ᵥ momU C B x)) ^ 2 = (dotProduct x.1 (F *ᵥ x.1)) ^ 2 := by
    intro x
    unfold momU
    rw [hF, dr_quad_scaled]
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := dr_quad_sq F
  have hmeas : Measurable (fun z : Vec m => (dotProduct z (F *ᵥ z)) ^ 2) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  obtain ⟨hI2, hV2⟩ := dr_fst_transfer (n := n) _ hmeas hI
  refine ⟨hI2, ?_⟩
  rw [hV2]
  refine hV.trans ?_
  have hn : nuc F ≤ CS / B * nuc D := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rOut C) * opNorm (rOut C) * nuc D) :=
      dr_nuc_scaled c (rOut C) D
    rw [bf_opNorm_rOut_mul_self, hcc] at h1
    refine h1.trans ?_
    have hD := nuc_nonneg D
    calc (B : ℝ)⁻¹ * (opNorm C.Sout * nuc D) ≤ (B : ℝ)⁻¹ * (CS * nuc D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSo hD) (by positivity)
      _ = CS / B * nuc D := by field_simp
  have h0 := nuc_nonneg F
  have := pow_le_pow_left₀ h0 hn 2
  linarith

private lemma dr_L2V {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSi : opNorm C.Sin ≤ CS) (D : Mat n n) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) ≤
      3 * (CS / B * nuc D) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat n n := (c * c) • ((rIn C)ᵀ * D * rIn C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momV C B x) (D *ᵥ momV C B x)) ^ 2 = (dotProduct x.2 (F *ᵥ x.2)) ^ 2 := by
    intro x
    unfold momV
    rw [hF, dr_quad_scaled]
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := dr_quad_sq F
  have hmeas : Measurable (fun z : Vec n => (dotProduct z (F *ᵥ z)) ^ 2) := by
    unfold dotProduct Matrix.mulVec; fun_prop
  obtain ⟨hI2, hV2⟩ := dr_snd_transfer (m := m) _ hmeas hI
  refine ⟨hI2, ?_⟩
  rw [hV2]
  refine hV.trans ?_
  have hn : nuc F ≤ CS / B * nuc D := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rIn C) * opNorm (rIn C) * nuc D) :=
      dr_nuc_scaled c (rIn C) D
    rw [bf_opNorm_rIn_mul_self, hcc] at h1
    refine h1.trans ?_
    have hD := nuc_nonneg D
    calc (B : ℝ)⁻¹ * (opNorm C.Sin * nuc D) ≤ (B : ℝ)⁻¹ * (CS * nuc D) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hSi hD) (by positivity)
      _ = CS / B * nuc D := by field_simp
  have h0 := nuc_nonneg F
  have := pow_le_pow_left₀ h0 hn 2
  linarith

private lemma dr_nuc_scaled_rect {a b : ℕ} (c : ℝ) (R : Mat a a) (E : Mat a b) (R' : Mat b b) :
    nuc ((c * c) • (Rᵀ * E * R')) ≤ (c * c) * (opNorm R * nuc E * opNorm R') := by
  rw [nuc_smul, abs_of_nonneg (mul_self_nonneg c)]
  have := nuc_mul_three_le Rᵀ E R'
  rw [bf_opNorm_transpose] at this
  exact mul_le_mul_of_nonneg_left this (mul_self_nonneg c)

private lemma dr_L2C {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (CS : ℝ)
    (hSo : opNorm C.Sout ≤ CS) (hSi : opNorm C.Sin ≤ CS) (E : Mat m n) :
    Integrable (fun x : Vec m × Vec n =>
      (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2) (gaussPair m n) ∧
    ∫ x, (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) ≤
      (CS / B * nuc E) ^ 2 := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  set c : ℝ := (Real.sqrt (B : ℝ))⁻¹ with hc
  have hcc : c * c = (B : ℝ)⁻¹ := by
    rw [hc, ← mul_inv, Real.mul_self_sqrt hBr.le]
  set F : Mat m n := (c * c) • ((rOut C)ᵀ * E * rIn C) with hF
  have hfun : ∀ x : Vec m × Vec n,
      (dotProduct (momU C B x) (E *ᵥ momV C B x)) ^ 2 = (dotProduct x.1 (F *ᵥ x.2)) ^ 2 := by
    intro x
    unfold momU momV
    rw [hF, Matrix.mulVec_smul, dotProduct_smul, smul_dotProduct, dr_dot_mulVec,
      Matrix.smul_mulVec, dotProduct_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp only [smul_eq_mul]
    congr 1
    ring
  simp_rw [hfun]
  obtain ⟨hI, hV⟩ := dr_bil_sq F
  refine ⟨hI, hV.trans ?_⟩
  have hn : nuc F ≤ CS / B * nuc E := by
    have h1 : nuc F ≤ (c * c) * (opNorm (rOut C) * nuc E * opNorm (rIn C)) :=
      dr_nuc_scaled_rect c (rOut C) E (rIn C)
    rw [hcc] at h1
    refine h1.trans ?_
    have hE := nuc_nonneg E
    have ho1 : 0 ≤ opNorm (rOut C) := by unfold opNorm; exact norm_nonneg _
    have ho2 : 0 ≤ opNorm (rIn C) := by unfold opNorm; exact norm_nonneg _
    have hCS : 0 ≤ CS := by
      have := mul_self_nonneg (opNorm (rOut C))
      rw [bf_opNorm_rOut_mul_self] at this
      exact le_trans (by unfold opNorm; exact norm_nonneg _) hSo
    have hprod : opNorm (rOut C) * opNorm (rIn C) ≤ CS := by
      have hsq : (opNorm (rOut C) * opNorm (rIn C)) ^ 2 ≤ CS ^ 2 := by
        have e : (opNorm (rOut C) * opNorm (rIn C)) ^ 2 =
            (opNorm (rOut C) * opNorm (rOut C)) * (opNorm (rIn C) * opNorm (rIn C)) := by ring
        rw [e, bf_opNorm_rOut_mul_self, bf_opNorm_rIn_mul_self, sq]
        exact mul_le_mul hSo hSi (by unfold opNorm; exact norm_nonneg _) hCS
      exact (pow_le_pow_iff_left₀ (mul_nonneg ho1 ho2) hCS two_ne_zero).mp hsq
    calc (B : ℝ)⁻¹ * (opNorm (rOut C) * nuc E * opNorm (rIn C))
        = (B : ℝ)⁻¹ * (opNorm (rOut C) * opNorm (rIn C)) * nuc E := by ring
      _ ≤ (B : ℝ)⁻¹ * CS * nuc E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (by positivity)) hE
      _ = CS / B * nuc E := by field_simp
  have h0 := nuc_nonneg F
  exact pow_le_pow_left₀ h0 hn 2

open scoped Matrix.Norms.L2Operator in
private lemma dr_mulVec_sq_le {a b : ℕ} (R : Mat a b) (u : Vec b) :
    sqNorm (R *ᵥ u) ≤ opNorm R ^ 2 * sqNorm u := by
  unfold sqNorm
  obtain ⟨v, hv⟩ : ∃ v : EuclideanSpace ℝ (Fin b), ∀ k, v.ofLp k = u k :=
    ⟨(EuclideanSpace.equiv (Fin b) ℝ).symm u, fun k => rfl⟩
  have h1 : ‖(EuclideanSpace.equiv (Fin a) ℝ).symm (R *ᵥ v)‖ ≤ opNorm R * ‖v‖ := by
    rw [opNorm_eq_norm]
    exact Matrix.l2_opNorm_mulVec R v
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow, EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at h2
  have e1 : ∀ i, ((EuclideanSpace.equiv (Fin a) ℝ).symm (R *ᵥ v)).ofLp i = (R *ᵥ u) i := by
    intro i
    simp [Matrix.mulVec, dotProduct, hv]
  have e2 : ∑ k, v.ofLp k ^ 2 = ∑ k, u k ^ 2 :=
    Finset.sum_congr rfl fun k _ => by rw [hv]
  simp only [e1, e2] at h2
  exact h2

private lemma dr_bil_le {a b : ℕ} (X : Mat a b) (u : Vec a) (v : Vec b) :
    |dotProduct u (X *ᵥ v)| ≤ opNorm X * ((sqNorm u + sqNorm v) / 2) := by
  have hon : 0 ≤ opNorm X := by unfold opNorm; exact norm_nonneg _
  have hcs : (dotProduct u (X *ᵥ v)) ^ 2 ≤ sqNorm u * sqNorm (X *ᵥ v) := by
    unfold dotProduct sqNorm
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hw := dr_mulVec_sq_le X v
  have hsu := pf_sqNorm_nonneg u
  have hsv := pf_sqNorm_nonneg v
  have key : (dotProduct u (X *ᵥ v)) ^ 2 ≤ (opNorm X * ((sqNorm u + sqNorm v) / 2)) ^ 2 := by
    calc _ ≤ sqNorm u * sqNorm (X *ᵥ v) := hcs
      _ ≤ sqNorm u * (opNorm X ^ 2 * sqNorm v) := mul_le_mul_of_nonneg_left hw hsu
      _ = opNorm X ^ 2 * (sqNorm u * sqNorm v) := by ring
      _ ≤ opNorm X ^ 2 * (((sqNorm u + sqNorm v) / 2) ^ 2) := by
          apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
          nlinarith [sq_nonneg (sqNorm u - sqNorm v)]
      _ = _ := by ring
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg hon (by positivity)) two_ne_zero).mp
    (by rw [sq_abs]; exact key)

/-- `Λ⁻¹ ≤ (c₁ (1+|d|)(1+N))²`. -/
private lemma dr_Linv (s s0 h d N c1 : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) (hN : 0 ≤ N)
    (hh : |h| ≤ |d|) (hc1 : c1 = 1 + 3 / (4 * Real.sqrt s0)) (L : ℝ)
    (hL : L ≤ (1 + 3 / (4 * Real.sqrt s) * |h| * N) ^ 2) :
    L ≤ (c1 * ((1 + |d|) * (1 + N))) ^ 2 := by
  refine hL.trans ?_
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  set c0 : ℝ := 3 / (4 * Real.sqrt s0) with hc0d
  have hc0 : 0 ≤ c0 := by rw [hc0d]; positivity
  have hcs : 3 / (4 * Real.sqrt s) ≤ c0 := by
    rw [hc0d]
    have hσ : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
    exact div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by have := Real.sqrt_le_sqrt hs; linarith)
  have hcs0 : 0 ≤ 3 / (4 * Real.sqrt s) := by positivity
  set a : ℝ := |d| with ha
  have ha0 : 0 ≤ a := abs_nonneg d
  have hin : 1 + 3 / (4 * Real.sqrt s) * |h| * N ≤ (1 + c0) * ((1 + a) * (1 + N)) := by
    have h1 : 3 / (4 * Real.sqrt s) * |h| * N ≤ c0 * a * N :=
      mul_le_mul_of_nonneg_right (mul_le_mul hcs hh (abs_nonneg _) hc0) hN
    have e : (1 + c0) * ((1 + a) * (1 + N)) =
        1 + c0 * a * N + (c0 + a + c0 * a + N + c0 * N + a * N) := by ring
    have hr : 0 ≤ c0 + a + c0 * a + N + c0 * N + a * N := by positivity
    rw [e]
    linarith
  have hin0 : 0 ≤ 1 + 3 / (4 * Real.sqrt s) * |h| * N := by
    have := abs_nonneg h; positivity
  rw [hc1]
  exact pow_le_pow_left₀ hin0 hin 2

private lemma dr_pt {m n : ℕ} (K K' : Mat m n) (u : Vec m) (v : Vec n) (d ϖ s s0 : ℝ)
    (hs0 : 0 < s0) (hs : s0 ≤ s) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1) :
    |Muon.DetEquiv.alpha2 K (ϖ * d) u v s - Muon.DetEquiv.alpha2 K' (ϖ * d) u v s| ≤
      ϖ ^ 2 * ((1 + 3 / (4 * Real.sqrt s0)) ^ 2 +
          (1 + 3 / (4 * Real.sqrt s0)) ^ 4 * (3 + 2 * (1 / (4 * Real.sqrt s0))) / s0) *
        ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ^ 4 *
        (|Muon.DetEquiv.delU K u s - Muon.DetEquiv.delU K' u s| +
          |Muon.DetEquiv.delV K v s - Muon.DetEquiv.delV K' v s| +
          |Muon.DetEquiv.delC K u v s - Muon.DetEquiv.delC K' u v s|) := by
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsq0 : 0 < Real.sqrt s0 := Real.sqrt_pos.mpr hs0
  have hsq : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  obtain ⟨hpos, -, -, -, hinv⟩ :=
    Muon.DetEquiv.lem_app_de_deletion K (ϖ * d) u v (K + (ϖ * d) • Muon.outer u v) s rfl hspos
  obtain ⟨hpos', -, -, -, hinv'⟩ :=
    Muon.DetEquiv.lem_app_de_deletion K' (ϖ * d) u v (K' + (ϖ * d) • Muon.outer u v) s rfl hspos
  have hNu := pf_sqNorm_nonneg u
  have hNv := pf_sqNorm_nonneg v
  have hN0 : 0 ≤ sqNorm u + sqNorm v := by linarith
  have hhd : |ϖ * d| ≤ |d| := by
    rw [abs_mul, abs_of_nonneg hϖ0]; exact mul_le_of_le_one_left (abs_nonneg d) hϖ1
  have hc1 : (1 : ℝ) ≤ 1 + 3 / (4 * Real.sqrt s0) := by
    have : 0 ≤ 3 / (4 * Real.sqrt s0) := by positivity
    linarith
  have hLi := dr_Linv s s0 (ϖ * d) d (sqNorm u + sqNorm v) _ hs0 hs hN0 hhd rfl _ hinv
  have hLi' := dr_Linv s s0 (ϖ * d) d (sqNorm u + sqNorm v) _ hs0 hs hN0 hhd rfl _ hinv'
  have hUb : s * |Muon.DetEquiv.delU K' u s| ≤ sqNorm u + sqNorm v := by
    have hq := pf_quad_le (Muon.DetEquiv.Rs K' s) u
    have hop := (Muon.DetEquiv.lem_app_de_resolvent K' s hspos).1
    have hq' : |Muon.DetEquiv.delU K' u s| ≤ opNorm (Muon.DetEquiv.Rs K' s) * sqNorm u := hq
    have : |Muon.DetEquiv.delU K' u s| ≤ (1 / s) * sqNorm u :=
      hq'.trans (mul_le_mul_of_nonneg_right hop hNu)
    calc s * |Muon.DetEquiv.delU K' u s| ≤ s * ((1 / s) * sqNorm u) :=
          mul_le_mul_of_nonneg_left this hspos.le
      _ = sqNorm u := by field_simp
      _ ≤ _ := by linarith
  have hVb : s * |Muon.DetEquiv.delV K v s| ≤ sqNorm u + sqNorm v := by
    have hq := pf_quad_le (Muon.DetEquiv.Rts K s) v
    have hop := (Muon.DetEquiv.lem_app_de_resolvent K s hspos).2.1
    have hq' : |Muon.DetEquiv.delV K v s| ≤ opNorm (Muon.DetEquiv.Rts K s) * sqNorm v := hq
    have : |Muon.DetEquiv.delV K v s| ≤ (1 / s) * sqNorm v :=
      hq'.trans (mul_le_mul_of_nonneg_right hop hNv)
    calc s * |Muon.DetEquiv.delV K v s| ≤ s * ((1 / s) * sqNorm v) :=
          mul_le_mul_of_nonneg_left this hspos.le
      _ = sqNorm v := by field_simp
      _ ≤ _ := by linarith
  have hCb : ∀ M : Mat m n, |Muon.DetEquiv.delC M u v s| ≤
      (1 / (4 * Real.sqrt s0)) * (sqNorm u + sqNorm v) := by
    intro M
    have hb := dr_bil_le (Muon.DetEquiv.Xs M s) u v
    have hop := (Muon.DetEquiv.lem_app_de_resolvent M s hspos).2.2.1
    have hb' : |Muon.DetEquiv.delC M u v s| ≤ opNorm (Muon.DetEquiv.Xs M s) *
        ((sqNorm u + sqNorm v) / 2) := hb
    refine hb'.trans ?_
    have h1 : opNorm (Muon.DetEquiv.Xs M s) * ((sqNorm u + sqNorm v) / 2) ≤
        (1 / (2 * Real.sqrt s)) * ((sqNorm u + sqNorm v) / 2) :=
      mul_le_mul_of_nonneg_right hop (by positivity)
    refine h1.trans ?_
    have h2 : 1 / (2 * Real.sqrt s) ≤ 2 * (1 / (4 * Real.sqrt s0)) := by
      have : Real.sqrt s0 ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
      rw [div_le_iff₀ (by positivity)]
      have : 1 / (4 * Real.sqrt s0) * (2 * (2 * Real.sqrt s)) = Real.sqrt s / Real.sqrt s0 := by
        field_simp; ring
      calc (1:ℝ) ≤ Real.sqrt s / Real.sqrt s0 := by
            rw [le_div_iff₀ hsq0]; linarith
        _ = _ := by rw [← this]; ring
    nlinarith [mul_le_mul_of_nonneg_right h2 hN0]
  have hq0 : (0:ℝ) ≤ 1 / (4 * Real.sqrt s0) := by positivity
  have halg := dr_alg s0 s ϖ d (sqNorm u + sqNorm v) (Muon.DetEquiv.delU K u s)
    (Muon.DetEquiv.delU K' u s) (Muon.DetEquiv.delV K v s) (Muon.DetEquiv.delC K u v s)
    (Muon.DetEquiv.delC K' u v s) (Muon.DetEquiv.delLambda K (ϖ * d) u v s)
    (Muon.DetEquiv.delLambda K' (ϖ * d) u v s) (Muon.DetEquiv.delV K' v s)
    (1 / (4 * Real.sqrt s0)) (1 + 3 / (4 * Real.sqrt s0)) hs0 hs hϖ0 hϖ1 hN0 hq0 hc1
    rfl rfl hpos hpos' hLi hLi' hUb hVb (hCb K) (hCb K')
  have e : Muon.DetEquiv.alpha2 K (ϖ * d) u v s - Muon.DetEquiv.alpha2 K' (ϖ * d) u v s =
      (ϖ * d) ^ 2 * Muon.DetEquiv.delU K u s / Muon.DetEquiv.delLambda K (ϖ * d) u v s -
      (ϖ * d) ^ 2 * Muon.DetEquiv.delU K' u s / Muon.DetEquiv.delLambda K' (ϖ * d) u v s := rfl
  rw [e]
  refine halg.trans ?_
  have hA10 : ((1 + |d|) * (1 + (sqNorm u + sqNorm v))) ^ 10 ≤
      ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 1 + |d| := by linarith [abs_nonneg d]
    have h2 : (1 : ℝ) ≤ 1 + (sqNorm u + sqNorm v) := by linarith
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
    exact mul_le_mul (pow_le_pow_right₀ h1 (by norm_num)) (pow_le_pow_right₀ h2 (by norm_num))
      (by positivity) (by positivity)
  have hK0 : 0 ≤ (1 + 3 / (4 * Real.sqrt s0)) ^ 2 +
      (1 + 3 / (4 * Real.sqrt s0)) ^ 4 * (3 + 2 * (1 / (4 * Real.sqrt s0))) / s0 := by positivity
  have hS : 0 ≤ |Muon.DetEquiv.delU K u s - Muon.DetEquiv.delU K' u s| +
      |Muon.DetEquiv.delV K v s - Muon.DetEquiv.delV K' v s| +
      |Muon.DetEquiv.delC K u v s - Muon.DetEquiv.delC K' u v s| := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA10 (mul_nonneg (sq_nonneg ϖ) hK0)) hS

/-- The coefficient-difference function `g = |δU| + |δV| + |δC|` is in `L²` with the bound
from the nuclear norms. -/
private lemma dr_g {m n B : ℕ} (F : FrozenParams m n B) (K K' : Mat m n) (s : ℝ) (hs : 0 < s)
    (CS : ℝ) (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS) (k : ℕ)
    (hk : (K - K').rank ≤ k) :
    MemLp (fun x : Vec m × Vec n =>
      |Muon.DetEquiv.delU K (momU F.C B x) s - Muon.DetEquiv.delU K' (momU F.C B x) s| +
      |Muon.DetEquiv.delV K (momV F.C B x) s - Muon.DetEquiv.delV K' (momV F.C B x) s| +
      |Muon.DetEquiv.delC K (momU F.C B x) (momV F.C B x) s -
        Muon.DetEquiv.delC K' (momU F.C B x) (momV F.C B x) s|) 2 (gaussPair m n) ∧
    ∫ x, (|Muon.DetEquiv.delU K (momU F.C B x) s - Muon.DetEquiv.delU K' (momU F.C B x) s| +
      |Muon.DetEquiv.delV K (momV F.C B x) s - Muon.DetEquiv.delV K' (momV F.C B x) s| +
      |Muon.DetEquiv.delC K (momU F.C B x) (momV F.C B x) s -
        Muon.DetEquiv.delC K' (momU F.C B x) (momV F.C B x) s|) ^ 2 ∂(gaussPair m n) ≤
      3 * (3 * (CS / B * (4 * k / s)) ^ 2 + 3 * (CS / B * (4 * k / s)) ^ 2 +
        (CS / B * (3 * k / Real.sqrt s)) ^ 2) := by
  have hB := F.hB
  set C := F.C with hCdef
  have hUc : Continuous (momU C B) := by unfold momU; fun_prop
  have hVc : Continuous (momV C B) := by unfold momV; fun_prop
  have eU : ∀ x : Vec m × Vec n,
      Muon.DetEquiv.delU K (momU C B x) s - Muon.DetEquiv.delU K' (momU C B x) s =
      dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x) := by
    intro x; unfold Muon.DetEquiv.delU; rw [Matrix.sub_mulVec, dotProduct_sub]
  have eV : ∀ x : Vec m × Vec n,
      Muon.DetEquiv.delV K (momV C B x) s - Muon.DetEquiv.delV K' (momV C B x) s =
      dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x) := by
    intro x; unfold Muon.DetEquiv.delV; rw [Matrix.sub_mulVec, dotProduct_sub]
  have eC : ∀ x : Vec m × Vec n,
      Muon.DetEquiv.delC K (momU C B x) (momV C B x) s -
        Muon.DetEquiv.delC K' (momU C B x) (momV C B x) s =
      dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x) := by
    intro x; unfold Muon.DetEquiv.delC; rw [Matrix.sub_mulVec, dotProduct_sub]
  simp_rw [eU, eV, eC]
  obtain ⟨hIU, hVU⟩ := dr_L2U C hB CS hSo (Rs K s - Rs K' s)
  obtain ⟨hIV, hVV⟩ := dr_L2V C hB CS hSi (Rts K s - Rts K' s)
  obtain ⟨hIC, hVC⟩ := dr_L2C C hB CS hSo hSi (Xs K s - Xs K' s)
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := le_trans (by unfold opNorm; exact norm_nonneg _) hSo
  have mU : Measurable (fun x : Vec m × Vec n =>
      dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) := by
    have := hUc; unfold dotProduct Matrix.mulVec; fun_prop
  have mV : Measurable (fun x : Vec m × Vec n =>
      dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) := by
    have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have mC : Measurable (fun x : Vec m × Vec n =>
      dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) := by
    have := hUc; have := hVc; unfold dotProduct Matrix.mulVec; fun_prop
  have lU : MemLp (fun x : Vec m × Vec n =>
      dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) 2 (gaussPair m n) :=
    (memLp_two_iff_integrable_sq mU.aestronglyMeasurable).mpr hIU
  have lV : MemLp (fun x : Vec m × Vec n =>
      dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) 2 (gaussPair m n) :=
    (memLp_two_iff_integrable_sq mV.aestronglyMeasurable).mpr hIV
  have lC : MemLp (fun x : Vec m × Vec n =>
      dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) 2 (gaussPair m n) :=
    (memLp_two_iff_integrable_sq mC.aestronglyMeasurable).mpr hIC
  refine ⟨(lU.abs.add lV.abs).add lC.abs, ?_⟩
  have hsq : ∀ x : Vec m × Vec n,
      (|dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)| +
        |dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)| +
        |dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)|) ^ 2 ≤
      3 * ((dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) ^ 2) := by
    intro x
    set a := dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)
    set b := dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)
    set c := dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)
    have := sq_abs a; have := sq_abs b; have := sq_abs c
    nlinarith [sq_nonneg (|a| - |b|), sq_nonneg (|b| - |c|), sq_nonneg (|a| - |c|)]
  have hsumI : Integrable (fun x : Vec m × Vec n =>
      3 * ((dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) ^ 2)) (gaussPair m n) :=
    ((hIU.add hIV).add hIC).const_mul 3
  have hgI := ((lU.abs.add lV.abs).add lC.abs).integrable_sq
  calc _ ≤ ∫ x, 3 * ((dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) ^ 2 +
        (dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) ^ 2 +
        (dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) ^ 2) ∂(gaussPair m n) :=
        integral_mono hgI hsumI hsq
    _ = 3 * (∫ x, (dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n) +
        ∫ x, (dotProduct (momU C B x) ((Xs K s - Xs K' s) *ᵥ momV C B x)) ^ 2 ∂(gaussPair m n)) := by
        have hAB : Integrable (fun x : Vec m × Vec n =>
            (dotProduct (momU C B x) ((Rs K s - Rs K' s) *ᵥ momU C B x)) ^ 2 +
            (dotProduct (momV C B x) ((Rts K s - Rts K' s) *ᵥ momV C B x)) ^ 2) (gaussPair m n) :=
          hIU.add hIV
        rw [integral_const_mul, integral_add hAB hIC, integral_add hIU hIV]
    _ ≤ _ := by
        have n1 := dr_nuc_Rs K K' s hs k hk
        have n2 := dr_nuc_Rts K K' s hs k hk
        have n3 := dr_nuc_Xs K K' s hs k hk
        have c0 : 0 ≤ CS / B := by positivity
        have b1 : 3 * (CS / B * nuc (Rs K s - Rs K' s)) ^ 2 ≤ 3 * (CS / B * (4 * k / s)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left n1 c0) 2) (by norm_num)
        have b2 : 3 * (CS / B * nuc (Rts K s - Rts K' s)) ^ 2 ≤ 3 * (CS / B * (4 * k / s)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _))
            (mul_le_mul_of_nonneg_left n2 c0) 2) (by norm_num)
        have b3 : (CS / B * nuc (Xs K s - Xs K' s)) ^ 2 ≤ (CS / B * (3 * k / Real.sqrt s)) ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg c0 (nuc_nonneg _)) (mul_le_mul_of_nonneg_left n3 c0) 2
        linarith

private lemma dr_gbound (s s0 CS B k : ℝ) (hs0 : 0 < s0) (hs : s0 ≤ s) (hBr : 0 < B) (_hCS : 0 ≤ CS)
    (_hk : 0 ≤ k) :
    3 * (3 * (CS / B * (4 * k / s)) ^ 2 + 3 * (CS / B * (4 * k / s)) ^ 2 +
        (CS / B * (3 * k / Real.sqrt s)) ^ 2) ≤
      (Real.sqrt (3 * (96 / s0 + 9)) * CS * k / (B * Real.sqrt s)) ^ 2 := by
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsq : Real.sqrt s ^ 2 = s := Real.sq_sqrt hspos.le
  have hsr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (CS / B * k / Real.sqrt s) ^ 2 := ⟨_, rfl⟩
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have ha2 : (CS / B * (4 * k / s)) ^ 2 = 16 * y / s := by
    rw [hy, div_pow, hsq]; field_simp; ring
  have hb2 : (CS / B * (3 * k / Real.sqrt s)) ^ 2 = 9 * y := by
    rw [hy]; field_simp; ring
  have hR : (Real.sqrt (3 * (96 / s0 + 9)) * CS * k / (B * Real.sqrt s)) ^ 2 =
      3 * (96 / s0 + 9) * y := by
    have h3 : 0 ≤ 3 * (96 / s0 + 9) := by positivity
    have e : Real.sqrt (3 * (96 / s0 + 9)) * CS * k / (B * Real.sqrt s) =
        Real.sqrt (3 * (96 / s0 + 9)) * (CS / B * k / Real.sqrt s) := by
      field_simp
    rw [e, mul_pow, Real.sq_sqrt h3, hy]
  rw [hR, ha2, hb2]
  have h1 : 16 * y / s ≤ 16 * y / s0 := div_le_div_of_nonneg_left (by positivity) hs0 hs
  have : 3 * (3 * (16 * y / s) + 3 * (16 * y / s) + 9 * y) ≤ 3 * (96 / s0 + 9) * y := by
    have e : 3 * (96 / s0 + 9) * y = 3 * (6 * (16 * y / s0) + 9 * y) := by field_simp; ring
    rw [e]; nlinarith
  exact this

/-- lem:app-drift-rank (`eqn:app-drift-rank`). Snapshot `cr-2026-10-23`. LaTeX (`section.tex`
l.404–411, verbatim):

Here `φ_ϖ(K) = phiFresh F K ϖ s` (`eqn:app-drift-phi`). Constant `C` depends only on
`(s₀, C_Σ, γ⋆)`; `k` is an arbitrary natural number, `K, K'` deterministic.

\begin{lemma}[Rank sensitivity of the conditional Gram coefficient]\label{lem:app-drift-rank}
Let $s_\circ>0$, $s\ge s_\circ$, $\varpi\in[0,1]$, and let
$K,K'\in\R^{\Nout\times\Nin}$ with $\operatorname{rank}(K-K')\le k$. Then
\begin{equation}\label{eqn:app-drift-rank}
\abs{\phi_\varpi(K)-\phi_\varpi(K')}\le\frac{C\,\varpi^2\,k}{\sqrt s\,B},
\end{equation}
with $C$ depending only on $(s_\circ,C_\Sigma,\gamma_\star)$.
\end{lemma}
-/
theorem lem_app_drift_rank (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (F : FrozenParams m n B) (K K' : Mat m n) (ϖ s : ℝ) (k : ℕ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ s → Matrix.rank (K - K') ≤ k →
        |phiFresh F K ϖ s - phiFresh F K' ϖ s| ≤ C * ϖ ^ 2 * k / (Real.sqrt s * B) := by
  obtain ⟨K8, hK80, hK8⟩ := cm_W_moment 8 (by norm_num) CS γ
  obtain ⟨K0, hK0def⟩ : ∃ K0 : ℝ, K0 = (1 + 3 / (4 * Real.sqrt s0)) ^ 2 +
      (1 + 3 / (4 * Real.sqrt s0)) ^ 4 * (3 + 2 * (1 / (4 * Real.sqrt s0))) / s0 := ⟨_, rfl⟩
  have hK0 : 0 ≤ K0 := by rw [hK0def]; positivity
  refine ⟨K0 * Real.sqrt K8 * Real.sqrt (3 * (96 / s0 + 9)) * CS, ?_⟩
  intro m n B F K K' ϖ s k hSo hSi hm hn hϖ0 hϖ1 hs hrank
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hsr : 0 < Real.sqrt s := Real.sqrt_pos.mpr hspos
  have hB := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := le_trans (by unfold opNorm; exact norm_nonneg _) hSo
  have hIK := phiFresh_integrable F K ϖ s hspos
  have hIK' := phiFresh_integrable F K' ϖ s hspos
  have hfm : freshMeas m n = gaussPair m n := rfl
  rw [hfm] at hIK hIK'
  have hdiff : phiFresh F K ϖ s - phiFresh F K' ϖ s = ∫ x, (
      Muon.DetEquiv.alpha2 K (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s -
      Muon.DetEquiv.alpha2 K' (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s) ∂(gaussPair m n) := by
    unfold phiFresh
    rw [hfm]
    exact (integral_sub hIK hIK').symm
  obtain ⟨hWI, hWint⟩ := hK8 m n B F.C ⟨hm, hn⟩ hγ ⟨hSo, hSi⟩ F.A F.hA
  obtain ⟨hgL, hgint⟩ := dr_g F K K' s hspos CS hSo hSi k hrank
  have hmN : Measurable (momN F.C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV; fun_prop
  have hmr : Measurable (fun x : Vec m × Vec n => resid F.A x) := by unfold resid; fun_prop
  have hf4m : Measurable (fun x : Vec m × Vec n =>
      (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) := by fun_prop
  have hf4L : MemLp (fun x : Vec m × Vec n =>
      (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) 2 (gaussPair m n) := by
    rw [memLp_two_iff_integrable_sq hf4m.aestronglyMeasurable]
    refine hWI.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only; rw [← pow_mul]
  obtain ⟨hprodI, hprod⟩ := dr_cs (gaussPair m n) _ _
    (fun x => by positivity)
    (fun x => by positivity) hf4L hgL
  have hpt : ∀ x : Vec m × Vec n,
      |Muon.DetEquiv.alpha2 K (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s -
      Muon.DetEquiv.alpha2 K' (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s| ≤
      (ϖ ^ 2 * K0) * ((((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4) *
        (|Muon.DetEquiv.delU K (momU F.C B x) s - Muon.DetEquiv.delU K' (momU F.C B x) s| +
      |Muon.DetEquiv.delV K (momV F.C B x) s - Muon.DetEquiv.delV K' (momV F.C B x) s| +
      |Muon.DetEquiv.delC K (momU F.C B x) (momV F.C B x) s -
        Muon.DetEquiv.delC K' (momU F.C B x) (momV F.C B x) s|)) := by
    intro x
    have h := dr_pt K K' (momU F.C B x) (momV F.C B x) (resid F.A x) ϖ s s0 hs0 hs hϖ0 hϖ1
    rw [cm_sq_eq F x, ← hK0def] at h
    refine h.trans (le_of_eq ?_)
    ring
  have hdI : Integrable (fun x : Vec m × Vec n =>
      Muon.DetEquiv.alpha2 K (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s -
      Muon.DetEquiv.alpha2 K' (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s) (gaussPair m n) :=
    hIK.sub hIK'
  have hrhsI := hprodI.const_mul (ϖ ^ 2 * K0)
  have h1 : |∫ x, (
      Muon.DetEquiv.alpha2 K (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s -
      Muon.DetEquiv.alpha2 K' (ϖ * resid F.A x) (momU F.C B x) (momV F.C B x) s) ∂(gaussPair m n)| ≤
      (ϖ ^ 2 * K0) * ∫ x, (((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4) *
        (|Muon.DetEquiv.delU K (momU F.C B x) s - Muon.DetEquiv.delU K' (momU F.C B x) s| +
      |Muon.DetEquiv.delV K (momV F.C B x) s - Muon.DetEquiv.delV K' (momV F.C B x) s| +
      |Muon.DetEquiv.delC K (momU F.C B x) (momV F.C B x) s -
        Muon.DetEquiv.delC K' (momU F.C B x) (momV F.C B x) s|) ∂(gaussPair m n) := by
    rw [← integral_const_mul]
    exact (abs_integral_le_integral_abs).trans (integral_mono hdI.abs hrhsI hpt)
  have hW8 : ∫ x, ((((1 + |resid F.A x|) ^ 4 * (1 + momN F.C B x) ^ 3) ^ 4)) ^ 2 ∂(gaussPair m n) ≤ K8 := by
    refine le_trans (le_of_eq ?_) hWint
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; rw [← pow_mul]
  have hG := hgint.trans (dr_gbound s s0 CS B k hs0 hs hBr hCS (Nat.cast_nonneg k))
  have h2 := hprod.trans (mul_le_mul (Real.sqrt_le_sqrt hW8) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  rw [Real.sqrt_sq (by positivity)] at h2
  rw [hdiff]
  refine h1.trans ?_
  have hc0 : 0 ≤ ϖ ^ 2 * K0 := by positivity
  refine (mul_le_mul_of_nonneg_left h2 hc0).trans (le_of_eq ?_)
  field_simp

end Muon.Drift

end
