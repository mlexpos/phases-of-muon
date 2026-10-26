import Muon.DetEquiv.Gram
import Muon.DetEquiv.Concentration
import Muon.DetEquiv.Branch
import Muon.Foundations.Conventions

/-!
# Appendix B: trace closure with bounded tests (task L-B.10)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`, label
`cor:app-de-trace` (l.1163–1176). CARD §5 WP L-B.10.
Interface draft: every declaration has proof `sorry`; proofs are assigned to proof workers.

Reuse, nothing redefined: `SetupRegime`, `WeightClass`, `Fw` (`DetEquiv.Scalar`); `Rbar`, `Rtbar`,
`branchSol` (`DetEquiv.Branch`); `normTrace` (`DetEquiv.Concentration`); `Rs`, `Rts`
(`DetEquiv.Resolvent`); `WeightedBuf`, `FrozenSamples` (`DetEquiv.SampleModel`, `Setup.Frozen`);
`IsDetEquiv`, `nuOut`, `nuIn`, `opNorm` (`Foundations.Conventions`).

Representation choices:
* Hypotheses are those of `thm:app-de-gram` (the `Gram.lean` signature), in the same order.
* The deterministic test matrices `T_B`, `T~_B` are sequences `T k`, `T' k` with a uniform bound
  `∃ CT, ∀ k, ‖T k‖ ≤ CT` (the source's "for all B"); the bound is a hypothesis.
* `E sup_{s∈I}` is `∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (…)`. Working in `ℝ≥0∞` gives no junk value.
  The lower Lebesgue integral of a supremum over the uncountable `I` is the outer expectation; it
  equals the source's `E sup` once the supremum is measurable (source §6.14). Measurability is
  not assumed here and not proved here.
* The normalization `1/N_out` (resp. `1/N_in`) is `normTrace (T k) (R.m k)` (resp. `(R.n k)`).
* `σ(-s)` and `σ~(-s)` are the first and second components of `branchSol (Fw w) νo νi s`, the
  solution of `def:app-de-branch`.
* Sign convention: `Rs M s = (M Mᵀ + s)⁻¹` is `R(-s)`, and `Rbar F νo νi C s` is `Rbar(-s)`.
* The non-record bridge `cor_app_de_trace_detEquiv` restates the output-side closure in the shared
  predicate `IsDetEquiv` at `z = -s`, `s ∈ I`. Its definitions read `-z.re`; values off `Z` are
  never inspected by `IsDetEquiv`.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder ENNReal
open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon Muon.Setup

noncomputable section

namespace Muon.DetEquiv

/-! ### Private helpers for `cor_app_de_trace_i/_ii` -/


private lemma pt_sum_sq_mulVec_le_c {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) (y : Fin b → ℂ) :
    ∑ k, ‖(T *ᵥ y) k‖ ^ 2 ≤ opNorm T ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin T (WithLp.toLp 2 y)‖ ≤ opNorm T * ‖WithLp.toLp 2 y‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin T)).le_opNorm (WithLp.toLp 2 y)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using hsq

private lemma pt_opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
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

private lemma pt_opNorm_nonneg {𝕜 : Type*} [RCLike 𝕜] {m n : ℕ} (K : Matrix (Fin m) (Fin n) 𝕜) :
    0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

private lemma pt_opNorm_map_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) (f : ℂ → ℝ)
    (hf : ∀ z, |f z| ≤ ‖z‖) (hl : ∀ (x : Fin b → ℝ), ∀ k, ((T.map f) *ᵥ x) k =
      f ((T *ᵥ (fun i => (x i : ℂ))) k)) :
    opNorm (T.map f) ≤ opNorm T := by
  refine pt_opNorm_le_of_sq _ _ (pt_opNorm_nonneg T) fun x => ?_
  have h1 := pt_sum_sq_mulVec_le_c T (fun i => (x i : ℂ))
  calc ∑ k, ((T.map f) *ᵥ x) k ^ 2 ≤ ∑ k, ‖(T *ᵥ (fun i => (x i : ℂ))) k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hl x k]
        calc f _ ^ 2 = |f _| ^ 2 := (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) (hf _) 2
    _ ≤ opNorm T ^ 2 * ∑ i, ‖((x i : ℂ))‖ ^ 2 := h1
    _ = opNorm T ^ 2 * ∑ i, x i ^ 2 := by
        simp [Complex.norm_real, sq_abs]

private lemma pt_opNorm_re_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (T.map Complex.re) ≤ opNorm T :=
  pt_opNorm_map_le T Complex.re Complex.abs_re_le_norm (fun x k => by
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum])

private lemma pt_opNorm_im_le {a b : ℕ} (T : Matrix (Fin a) (Fin b) ℂ) :
    opNorm (T.map Complex.im) ≤ opNorm T :=
  pt_opNorm_map_le T Complex.im Complex.abs_im_le_norm (fun x k => by
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.im_sum])

private lemma pt_trace_duality {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (E : Mat k k) :
    ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖ ≤ 2 * opNorm T * nuc E := by
  have hre : (Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).re =
      Matrix.trace ((T.map Complex.re) * E) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.re_sum, Matrix.map_apply]
  have him : (Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).im =
      Matrix.trace ((T.map Complex.im) * E) := by
    simp [Matrix.trace, Matrix.mul_apply, Complex.im_sum, Matrix.map_apply]
  have h1 := trace_mul_le_opNorm_mul_nuc (T.map Complex.re) E
  have h2 := trace_mul_le_opNorm_mul_nuc (T.map Complex.im) E
  have hn := nuc_nonneg E
  have hr := pt_opNorm_re_le T
  have hi := pt_opNorm_im_le T
  calc ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖
      ≤ |(Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).re| +
        |(Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ opNorm T * nuc E + opNorm T * nuc E := by
        rw [hre, him]
        exact add_le_add (h1.trans (mul_le_mul_of_nonneg_right hr hn))
          (h2.trans (mul_le_mul_of_nonneg_right hi hn))
    _ = 2 * opNorm T * nuc E := by ring

/-- `‖Tr(T E)‖ ≤ 2 ‖T‖ k ‖E‖`. -/
private lemma pt_trace_bound {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (E : Mat k k) :
    ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖ ≤ 2 * opNorm T * ((k : ℝ) * opNorm E) := by
  refine (pt_trace_duality T E).trans ?_
  have h2 := nuc_le_rank_mul_opNorm E
  have h4 : (Matrix.rank E : ℝ) ≤ k := by exact_mod_cast Matrix.rank_le_height _
  have hR := pt_opNorm_nonneg E
  have hT := pt_opNorm_nonneg T
  exact mul_le_mul_of_nonneg_left (h2.trans (mul_le_mul_of_nonneg_right h4 hR)) (by positivity)

private lemma pt_normTrace_sub {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) (R R' : Mat k k) :
    normTrace T B R - normTrace T B R' = (B : ℂ)⁻¹ * Matrix.trace (T * (R - R').map (fun x : ℝ => (x : ℂ))) := by
  unfold normTrace
  rw [← mul_sub, Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b), Matrix.mul_sub, Matrix.trace_sub]

private lemma pt_normTrace_scale {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (a B : ℕ) (ha : 0 < a)
    (hB : 0 < B) (R : Mat k k) :
    normTrace T a R = (((B : ℝ) / a : ℝ) : ℂ) * normTrace T B R := by
  unfold normTrace
  have h1 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h2 : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  push_cast
  field_simp

/-- Real norm of the normalized trace of a difference, in the `a`-normalization. -/
private lemma pt_normTrace_diff_bound {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (hk : 0 < k)
    (E : Mat k k) :
    ‖normTrace T k E‖ ≤ 2 * opNorm T * opNorm E := by
  unfold normTrace
  rw [norm_mul]
  have hB : ‖(k : ℂ)⁻¹‖ = (k : ℝ)⁻¹ := by simp
  rw [hB]
  have h := pt_trace_bound T E
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  calc (k : ℝ)⁻¹ * ‖Matrix.trace (T * E.map (fun x : ℝ => (x : ℂ)))‖
      ≤ (k : ℝ)⁻¹ * (2 * opNorm T * ((k : ℝ) * opNorm E)) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = 2 * opNorm T * opNorm E := by field_simp

private lemma pt_normTrace_cont {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) :
    Continuous (fun R : Mat k k => normTrace T B R) := by
  unfold normTrace
  exact continuous_const.mul ((continuous_const.matrix_mul
    (continuous_id.matrix_map Complex.continuous_ofReal)).matrix_trace)

private lemma pt_inv_measurable {a : ℕ} : Measurable (fun X : Mat a a => X⁻¹) := by
  have hdet : Measurable (fun X : Mat a a => X.det) := (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun X : Mat a a => X.adjugate) :=
    (continuous_id.matrix_adjugate).measurable
  have hinv : (fun X : Mat a a => X⁻¹) = fun X => Ring.inverse X.det • X.adjugate :=
    funext fun X => Matrix.inv_def X
  have h1 : Measurable (fun X : Mat a a => Ring.inverse X.det) := by
    simp only [Ring.inverse_eq_inv]
    exact hdet.inv
  rw [hinv]
  exact h1.smul hadj

private lemma pt_Rs_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rs M s) := by
  have hc : Continuous (fun M : Mat a b => M * Mᵀ + s • (1 : Mat a a)) := by fun_prop
  exact (pt_inv_measurable (a := a)).comp hc.measurable

private lemma pt_meas_WB {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ : Measurable (fun x : Vec m × Vec n =>
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
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

/-- every matrix entry is bounded by the operator norm. -/
private lemma pt_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

/-- operator norm is bounded by `√(pq) · max entry`. -/
private lemma pt_opNorm_le_of_entries {p q : ℕ} (K : Mat p q) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i j, |K i j| ≤ b) : opNorm K ≤ b * Real.sqrt ((p : ℝ) * q) := by
  have hM : 0 ≤ b * Real.sqrt ((p : ℝ) * q) := by positivity
  refine pt_opNorm_le_of_sq K _ hM fun x => ?_
  have hsq : (b * Real.sqrt ((p : ℝ) * q)) ^ 2 = b ^ 2 * ((p : ℝ) * q) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [hsq]
  have hk : ∀ k, (K *ᵥ x) k ^ 2 ≤ b ^ 2 * (q * ∑ i, x i ^ 2) := by
    intro k
    have h1 : |(K *ᵥ x) k| ≤ b * ∑ j, |x j| := by
      calc |(K *ᵥ x) k| = |∑ j, K k j * x j| := by simp [Matrix.mulVec, dotProduct]
        _ ≤ ∑ j, |K k j * x j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j, b * |x j| := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]; exact mul_le_mul_of_nonneg_right (h k j) (abs_nonneg _)
        _ = b * ∑ j, |x j| := by rw [Finset.mul_sum]
    have h2 : (∑ j, |x j|) ^ 2 ≤ q * ∑ i, x i ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin q))) (f := fun j => |x j|)
      simpa [sq_abs] using this
    calc (K *ᵥ x) k ^ 2 = |(K *ᵥ x) k| ^ 2 := (sq_abs _).symm
      _ ≤ (b * ∑ j, |x j|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = b ^ 2 * (∑ j, |x j|) ^ 2 := by ring
      _ ≤ b ^ 2 * (q * ∑ i, x i ^ 2) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  calc ∑ k, (K *ᵥ x) k ^ 2 ≤ ∑ _k : Fin p, b ^ 2 * (q * ∑ i, x i ^ 2) := Finset.sum_le_sum fun k _ => hk k
    _ = b ^ 2 * ((p : ℝ) * q) * ∑ i, x i ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- `Rbar`-type bound: `(s·1 + a·A)⁻¹` is a resolvent `Rs M s` of a square root, hence `≤ 1/s`. -/
private lemma pt_shift_inv_eq {p : ℕ} (A : Mat p p) (hA : A.PosSemidef) (a s : ℝ) (ha : 0 ≤ a) :
    (s • (1 : Mat p p) + a • A)⁻¹ = Rs (Real.sqrt a • CFC.sqrt A) s := by
  have hA0 : 0 ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
  have hsym : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
    have h : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hsq : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA0
  unfold Rs
  congr 1
  rw [Matrix.transpose_smul, hsym, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Real.mul_self_sqrt ha, hsq, add_comm]

private lemma pt_branch_nonneg (F : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    0 ≤ (branchSol F ν ν' s).2.2.1 ∧ 0 ≤ (branchSol F ν ν' s).2.2.2 := by
  classical
  unfold branchSol
  split_ifs with h
  · have := h.choose_spec
    generalize h.choose = x at this
    obtain ⟨σ, σ', a, c⟩ := x
    exact ⟨this.2.2.1, this.2.2.2.1⟩
  · simp

/-- Finite-net bound: supremum over `I` of `‖Z s ω‖²` from pointwise second moments and a
deterministic Lipschitz bound. -/
private lemma pt_net_bound {I : Set ℝ} (hI : IsCompact I) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (Z : ℝ → Ω → ℂ) (Λ : ℝ), 0 ≤ Λ → (∀ s ∈ I, Measurable (Z s)) →
      (∀ ω, ∀ s ∈ I, ∀ s' ∈ I, ‖Z s ω - Z s' ω‖ ≤ Λ * |s - s'|) →
      ∀ V : ℝ≥0∞, (∀ s ∈ I, ∫⁻ ω, ENNReal.ofReal (‖Z s ω‖ ^ 2) ∂P ≤ V) →
      ∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖Z s ω‖ ^ 2) ∂P ≤
        2 * (N : ℝ≥0∞) * V + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
  obtain ⟨F, hFI, hFfin, hcov⟩ := hI.finite_cover_balls hδ
  refine ⟨hFfin.toFinset.card, ?_⟩
  intro Ω _ P _ Z Λ hΛ hmeas hlip V hV
  set Fs := hFfin.toFinset with hFs
  have hmemF : ∀ i, i ∈ Fs ↔ i ∈ F := fun i => hFfin.mem_toFinset
  have hpt : ∀ ω, (⨆ s ∈ I, ENNReal.ofReal (‖Z s ω‖ ^ 2)) ≤
      2 * ∑ i ∈ Fs, ENNReal.ofReal (‖Z i ω‖ ^ 2) + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
    intro ω
    refine iSup₂_le fun s hs => ?_
    have hs' := hcov hs
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at hs'
    obtain ⟨i, hiF, hdist⟩ := hs'
    have hiI : i ∈ I := hFI hiF
    have h1 : ‖Z s ω‖ ≤ ‖Z i ω‖ + Λ * δ := by
      have := hlip ω s hs i hiI
      have h2 : Λ * |s - i| ≤ Λ * δ := mul_le_mul_of_nonneg_left (by
        rw [Real.dist_eq] at hdist; exact hdist.le) hΛ
      calc ‖Z s ω‖ = ‖(Z s ω - Z i ω) + Z i ω‖ := by ring_nf
        _ ≤ ‖Z s ω - Z i ω‖ + ‖Z i ω‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have h3 : ‖Z s ω‖ ^ 2 ≤ 2 * ‖Z i ω‖ ^ 2 + 2 * (Λ * δ) ^ 2 := by
      have h0 := norm_nonneg (Z s ω)
      nlinarith [sq_nonneg (‖Z i ω‖ - Λ * δ), norm_nonneg (Z i ω), mul_nonneg hΛ hδ.le]
    calc ENNReal.ofReal (‖Z s ω‖ ^ 2) ≤ ENNReal.ofReal (2 * ‖Z i ω‖ ^ 2 + 2 * (Λ * δ) ^ 2) :=
          ENNReal.ofReal_le_ofReal h3
      _ = 2 * ENNReal.ofReal (‖Z i ω‖ ^ 2) + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num)]
          simp
      _ ≤ _ := by
          gcongr
          exact Finset.single_le_sum (f := fun i => ENNReal.ofReal (‖Z i ω‖ ^ 2))
            (fun _ _ => zero_le) ((hmemF i).2 hiF)
  have hmeasi : ∀ i ∈ Fs, Measurable (fun ω => ENNReal.ofReal (‖Z i ω‖ ^ 2)) := fun i hi =>
    ((hmeas i (hFI ((hmemF i).1 hi))).norm.pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖Z s ω‖ ^ 2) ∂P
      ≤ ∫⁻ ω, (2 * ∑ i ∈ Fs, ENNReal.ofReal (‖Z i ω‖ ^ 2) + ENNReal.ofReal (2 * (Λ * δ) ^ 2)) ∂P :=
        lintegral_mono hpt
    _ = 2 * ∑ i ∈ Fs, ∫⁻ ω, ENNReal.ofReal (‖Z i ω‖ ^ 2) ∂P + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (by simp), lintegral_finsetSum _ hmeasi]
    _ ≤ 2 * (Fs.card • V) + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
        gcongr
        exact Finset.sum_le_card_nsmul _ _ _ fun i hi => hV i (hFI ((hmemF i).1 hi))
    _ = 2 * (Fs.card : ℝ≥0∞) * V + ENNReal.ofReal (2 * (Λ * δ) ^ 2) := by
        rw [nsmul_eq_mul, mul_assoc]

private lemma pt_nt_sub {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) (R R' : Mat k k) :
    normTrace T B (R - R') = normTrace T B R - normTrace T B R' :=
  (pt_normTrace_sub T B R R').symm

private lemma pt_normTrace_norm_le {k : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (B : ℕ) (E : Mat k k) :
    ‖normTrace T B E‖ ≤ (B : ℝ)⁻¹ * (2 * opNorm T * ((k : ℝ) * opNorm E)) := by
  unfold normTrace
  rw [norm_mul]
  have hB : ‖(B : ℂ)⁻¹‖ = (B : ℝ)⁻¹ := by simp
  rw [hB]
  exact mul_le_mul_of_nonneg_left (pt_trace_bound T E) (by positivity)

private lemma pt_int_Rs {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (K : Ω' → Mat m n) (hK : Measurable K) (s : ℝ) (hs : 0 < s) (i k : Fin m) :
    Integrable (fun ω => Rs (K ω) s i k) P := by
  refine Integrable.of_bound (C := 1 / s)
    (((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      ((pt_Rs_measurable s).comp hK))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  exact (pt_abs_entry_le_opNorm _ i k).trans (lem_app_de_resolvent (K ω) s hs).1

private lemma pt_mean_normTrace {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {a b : ℕ} (K : Ω' → Mat a b) (hK : Measurable K) (s : ℝ) (hs : 0 < s)
    (T : Matrix (Fin a) (Fin a) ℂ) (Bn : ℕ) :
    ∫ ω, normTrace T Bn (Rs (K ω) s) ∂P =
      normTrace T Bn (Muon.mean P fun ω => Rs (K ω) s) := by
  unfold normTrace
  rw [integral_const_mul]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Muon.mean,
    Matrix.of_apply]
  rw [integral_finset_sum _ (fun i _ => integrable_finsetSum _ fun j _ =>
    ((pt_int_Rs P K hK s hs j i).ofReal).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => ((pt_int_Rs P K hK s hs j i).ofReal).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  congr 1
  exact integral_ofReal

private lemma pt_gen {I : Set ℝ} (hI : IsCompact I) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      {a b : ℕ} (K : Ω → Mat a b), Measurable K → ∀ (sm : ℝ), 0 < sm → (∀ s ∈ I, sm ≤ s) →
      ∀ (T : Matrix (Fin a) (Fin a) ℂ) (CT : ℝ), opNorm T ≤ CT → ∀ (Bn : ℕ), 0 < Bn → 0 < a →
      ∀ (V : ℝ), 0 ≤ V →
      (∀ s ∈ I, cVar P (fun ω => normTrace T Bn (Rs (K ω) s)) ≤ ENNReal.ofReal V) →
      ∀ (Rb : ℝ → Mat a a) (ε : ℝ), 0 ≤ ε →
      (∀ s ∈ I, opNorm (Muon.mean P (fun ω => Rs (K ω) s) - Rb s) ≤ ε) →
      ∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖normTrace T a (Rs (K ω) s - Rb s)‖ ^ 2) ∂P ≤
        ENNReal.ofReal (4 * N * ((Bn : ℝ) / a) ^ 2 * V
          + 16 * (2 * CT * δ / sm ^ 2) ^ 2 + 8 * CT ^ 2 * ε ^ 2) := by
  obtain ⟨N, hN⟩ := pt_net_bound hI hδ
  refine ⟨N, ?_⟩
  intro Ω _ P _ a b K hK sm hsm hsmI T CT hT Bn hBn ha V hV0 hV Rb ε hε0 hε
  have hCT0 : 0 ≤ CT := (pt_opNorm_nonneg T).trans hT
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hBR : (0 : ℝ) < Bn := by exact_mod_cast hBn
  set c : ℝ := (Bn : ℝ) / a with hc
  have hc0 : 0 < c := by positivity
  set Λ0 : ℝ := (a : ℝ) / Bn * (2 * CT / sm ^ 2) with hΛ0
  have hΛ00 : 0 ≤ Λ0 := by positivity
  have hcΛ : c * Λ0 = 2 * CT / sm ^ 2 := by
    rw [hc, hΛ0]; field_simp
  -- the normalized trace
  set Y : ℝ → Ω → ℂ := fun s ω => normTrace T Bn (Rs (K ω) s) with hYdef
  set μ : ℝ → ℂ := fun s => ∫ ω, Y s ω ∂P with hμdef
  have hYmeas : ∀ s, Measurable (Y s) := fun s =>
    (pt_normTrace_cont T Bn).measurable.comp ((pt_Rs_measurable s).comp hK)
  have hYbd : ∀ s ∈ I, ∀ ω, ‖Y s ω‖ ≤ (Bn : ℝ)⁻¹ * (2 * CT * ((a : ℝ) * (1 / sm))) := by
    intro s hs ω
    have hs0 : sm ≤ s := hsmI s hs
    have h1 := pt_normTrace_norm_le T Bn (Rs (K ω) s)
    have h2 := (lem_app_de_resolvent (K ω) s (hsm.trans_le hs0)).1
    have h3 : 1 / s ≤ 1 / sm := one_div_le_one_div_of_le hsm hs0
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hRn := pt_opNorm_nonneg (Rs (K ω) s)
    have hTn := pt_opNorm_nonneg T
    have h4 : (a : ℝ) * opNorm (Rs (K ω) s) ≤ (a : ℝ) * (1 / sm) :=
      mul_le_mul_of_nonneg_left (h2.trans h3) haR.le
    exact mul_le_mul (by linarith) h4 (by positivity) (by positivity)
  have hYint : ∀ s ∈ I, Integrable (Y s) P := fun s hs =>
    Integrable.of_bound (C := (Bn : ℝ)⁻¹ * (2 * CT * ((a : ℝ) * (1 / sm))))
      (hYmeas s).aestronglyMeasurable (Filter.Eventually.of_forall (hYbd s hs))
  have hYlip : ∀ ω, ∀ s ∈ I, ∀ s' ∈ I, ‖Y s ω - Y s' ω‖ ≤ Λ0 * |s - s'| := by
    intro ω s hs s' hs'
    have hs0 : sm ≤ s := hsmI s hs
    have hs'0 : sm ≤ s' := hsmI s' hs'
    have hsp : 0 < s := hsm.trans_le hs0
    have hsp' : 0 < s' := hsm.trans_le hs'0
    show ‖normTrace T Bn (Rs (K ω) s) - normTrace T Bn (Rs (K ω) s')‖ ≤ _
    rw [← pt_nt_sub]
    refine (pt_normTrace_norm_le T Bn _).trans ?_
    have h2 := (lem_app_de_resolvent (K ω) s hsp).2.2.2.2.2.2 s' hsp'
    have hss : |s - s'| / (s * s') ≤ |s - s'| / sm ^ 2 := by
      apply div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
      nlinarith
    have hTn := pt_opNorm_nonneg T
    have hRn := pt_opNorm_nonneg (Rs (K ω) s - Rs (K ω) s')
    calc (Bn : ℝ)⁻¹ * (2 * opNorm T * ((a : ℝ) * opNorm (Rs (K ω) s - Rs (K ω) s')))
        ≤ (Bn : ℝ)⁻¹ * (2 * CT * ((a : ℝ) * (|s - s'| / sm ^ 2))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h4 : (a : ℝ) * opNorm (Rs (K ω) s - Rs (K ω) s') ≤ (a : ℝ) * (|s - s'| / sm ^ 2) :=
            mul_le_mul_of_nonneg_left (h2.trans hss) haR.le
          exact mul_le_mul (by linarith) h4 (by positivity) (by positivity)
      _ = Λ0 * |s - s'| := by rw [hΛ0]; field_simp
  have hμlip : ∀ s ∈ I, ∀ s' ∈ I, ‖μ s - μ s'‖ ≤ Λ0 * |s - s'| := by
    intro s hs s' hs'
    simp only [hμdef]
    rw [← integral_sub (hYint s hs) (hYint s' hs')]
    refine (norm_integral_le_of_norm_le_const (C := Λ0 * |s - s'|)
      (Filter.Eventually.of_forall fun ω => hYlip ω s hs s' hs')).trans ?_
    rw [probReal_univ, mul_one]
  set Zf : ℝ → Ω → ℂ := fun s ω => Y s ω - μ s with hZdef
  have hZmeas : ∀ s ∈ I, Measurable (Zf s) := fun s _ => (hYmeas s).sub_const _
  have hZlip : ∀ ω, ∀ s ∈ I, ∀ s' ∈ I, ‖Zf s ω - Zf s' ω‖ ≤ (2 * Λ0) * |s - s'| := by
    intro ω s hs s' hs'
    have h1 := hYlip ω s hs s' hs'
    have h2 := hμlip s hs s' hs'
    calc ‖Zf s ω - Zf s' ω‖ = ‖(Y s ω - Y s' ω) - (μ s - μ s')‖ := by simp only [hZdef]; ring_nf
      _ ≤ ‖Y s ω - Y s' ω‖ + ‖μ s - μ s'‖ := norm_sub_le _ _
      _ ≤ (2 * Λ0) * |s - s'| := by linarith
  have hnet := hN P Zf (2 * Λ0) (by positivity) hZmeas hZlip (ENNReal.ofReal V) (fun s hs => hV s hs)
  -- pointwise bound
  have hpt : ∀ ω, ∀ s ∈ I, ENNReal.ofReal (‖normTrace T a (Rs (K ω) s - Rb s)‖ ^ 2) ≤
      ENNReal.ofReal (2 * c ^ 2) * (⨆ s' ∈ I, ENNReal.ofReal (‖Zf s' ω‖ ^ 2)) +
        ENNReal.ofReal (8 * CT ^ 2 * ε ^ 2) := by
    intro ω s hs
    have hsp : 0 < s := hsm.trans_le (hsmI s hs)
    set E : Mat a a := Muon.mean P (fun ω => Rs (K ω) s) with hE
    have hμs : μ s = normTrace T Bn E := pt_mean_normTrace P K hK s hsp T Bn
    have hsplit : normTrace T a (Rs (K ω) s - Rb s) =
        (c : ℂ) * Zf s ω + normTrace T a (E - Rb s) := by
      rw [pt_nt_sub, pt_nt_sub, pt_normTrace_scale T a Bn ha hBn (Rs (K ω) s),
        pt_normTrace_scale T a Bn ha hBn E]
      simp only [hZdef, hYdef, hμs]
      ring
    have hb : ‖normTrace T a (E - Rb s)‖ ≤ 2 * CT * ε := by
      refine (pt_normTrace_diff_bound T ha _).trans ?_
      have h1 := hε s hs
      have hn := pt_opNorm_nonneg (E - Rb s)
      have hTn := pt_opNorm_nonneg T
      exact mul_le_mul (by linarith) h1 hn (by positivity)
    have hn1 : ‖normTrace T a (Rs (K ω) s - Rb s)‖ ≤ c * ‖Zf s ω‖ + 2 * CT * ε := by
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hc0.le]
      linarith
    have hn2 : ‖normTrace T a (Rs (K ω) s - Rb s)‖ ^ 2 ≤ 2 * c ^ 2 * ‖Zf s ω‖ ^ 2 + 8 * CT ^ 2 * ε ^ 2 := by
      have h0 := norm_nonneg (normTrace T a (Rs (K ω) s - Rb s))
      have h3 : ‖normTrace T a (Rs (K ω) s - Rb s)‖ ^ 2 ≤ (c * ‖Zf s ω‖ + 2 * CT * ε) ^ 2 :=
        pow_le_pow_left₀ h0 hn1 2
      nlinarith [sq_nonneg (c * ‖Zf s ω‖ - 2 * CT * ε)]
    refine le_trans (ENNReal.ofReal_le_ofReal hn2) ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity)]
    gcongr
    exact le_iSup₂ (f := fun s' (_ : s' ∈ I) => ENNReal.ofReal (‖Zf s' ω‖ ^ 2)) s hs
  calc ∫⁻ ω, ⨆ s ∈ I, ENNReal.ofReal (‖normTrace T a (Rs (K ω) s - Rb s)‖ ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * c ^ 2) * (⨆ s' ∈ I, ENNReal.ofReal (‖Zf s' ω‖ ^ 2)) +
        ENNReal.ofReal (8 * CT ^ 2 * ε ^ 2)) ∂P :=
        lintegral_mono fun ω => iSup₂_le fun s hs => hpt ω s hs
    _ = ENNReal.ofReal (2 * c ^ 2) * ∫⁻ ω, (⨆ s' ∈ I, ENNReal.ofReal (‖Zf s' ω‖ ^ 2)) ∂P +
        ENNReal.ofReal (8 * CT ^ 2 * ε ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (2 * c ^ 2) * (2 * (N : ℝ≥0∞) * ENNReal.ofReal V +
          ENNReal.ofReal (2 * ((2 * Λ0) * δ) ^ 2)) + ENNReal.ofReal (8 * CT ^ 2 * ε ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (4 * N * c ^ 2 * V + 16 * (2 * CT * δ / sm ^ 2) ^ 2 + 8 * CT ^ 2 * ε ^ 2) := by
        have e1 : (2 : ℝ≥0∞) = ENNReal.ofReal 2 := by simp
        have e2 : (N : ℝ≥0∞) = ENNReal.ofReal N := (ENNReal.ofReal_natCast N).symm
        rw [e2, e1, ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        have : 16 * (2 * CT * δ / sm ^ 2) ^ 2 = 16 * (c * Λ0 * δ) ^ 2 := by rw [hcΛ]; ring
        rw [this]
        ring

private lemma pt_exists_sm {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
  by_cases hne : I.Nonempty
  · exact ⟨sInf I, hIpos (hI.sInf_mem hne), fun s hs => csInf_le hI.bddBelow hs⟩
  · exact ⟨1, one_pos, fun s hs => (hne ⟨s, hs⟩).elim⟩

private lemma pt_le_iSup_mem {I : Set ℝ} (f : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (h : ∀ s ∈ I, f s ≤ M) {s : ℝ} (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  have hbdd : BddAbove (Set.range fun s : ℝ => ⨆ (_ : s ∈ I), f s) :=
    ⟨M, by
      rintro _ ⟨x, rfl⟩
      exact Real.iSup_le (fun hx => h x hx) hM⟩
  calc f s = ⨆ (_ : s ∈ I), f s := (ciSup_pos (f := fun _ : s ∈ I => f s) hs).symm
    _ ≤ ⨆ s' : ℝ, ⨆ (_ : s' ∈ I), f s' := le_ciSup hbdd s

private lemma pt_Rts_eq {m n : ℕ} (M : Mat m n) (s : ℝ) : Rts M s = Rs Mᵀ s := by
  simp [Rts, Rs]

private lemma pt_entry_mean_le {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {a : ℕ} (X : Ω' → Mat a a) (b : ℝ) (hb : ∀ ω, opNorm (X ω) ≤ b) (i j : Fin a) :
    |Muon.mean P X i j| ≤ b := by
  unfold Muon.mean
  simp only [Matrix.of_apply]
  have := norm_integral_le_of_norm_le_const (μ := P) (f := fun ω => X ω i j) (C := b)
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact (pt_abs_entry_le_opNorm _ i j).trans (hb ω))
  rw [probReal_univ, mul_one, Real.norm_eq_abs] at this
  exact this

private lemma pt_gram_pointwise (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∀ η > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ η ∧
      opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ η := by
  intro η hη
  have h := thm_app_de_gram R w hw P S νo νi hνo hνi t I hI hIpos
  obtain ⟨sm, hsm, hsmI⟩ := pt_exists_sm hI hIpos
  filter_upwards [h.eventually (gt_mem_nhds hη)] with k hk s hs
  have hs0 : 0 < s := hsm.trans_le (hsmI s hs)
  have hsms : sm ≤ s := hsmI s hs
  set f : ℝ → ℝ := fun s => opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) with hf
  have hb1 : ∀ s ∈ I, f s ≤ (2 / sm) * (Real.sqrt ((R.m k : ℝ) * R.m k) + Real.sqrt ((R.n k : ℝ) * R.n k)) := by
    intro s hs
    have hs0 : 0 < s := hsm.trans_le (hsmI s hs)
    have h2s : 2 / s ≤ 2 / sm := div_le_div_of_nonneg_left (by norm_num) hsm (hsmI s hs)
    have hRb1 : opNorm (Rbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ 1 / s := by
      have e : Rbar (Fw w) (νo k) (νi k) (R.F k).C s =
          Rs (Real.sqrt (branchSol (Fw w) (νo k) (νi k) s).2.2.1 • CFC.sqrt (R.F k).C.Sout) s := by
        rw [← pt_shift_inv_eq _ (R.F k).C.psdOut _ _ (pt_branch_nonneg _ _ _ _).1]
        rfl
      rw [e]; exact (lem_app_de_resolvent _ s hs0).1
    have hRb2 : opNorm (Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ 1 / s := by
      have e : Rtbar (Fw w) (νo k) (νi k) (R.F k).C s =
          Rs (Real.sqrt (branchSol (Fw w) (νo k) (νi k) s).2.2.2 • CFC.sqrt (R.F k).C.Sin) s := by
        rw [← pt_shift_inv_eq _ (R.F k).C.psdIn _ _ (pt_branch_nonneg _ _ _ _).2]
        rfl
      rw [e]; exact (lem_app_de_resolvent _ s hs0).1
    have hE1 : ∀ i j, |expRes w (R.F k) (S k) t s i j| ≤ 1 / s := fun i j =>
      pt_entry_mean_le (P k) (fun ω => Rs (WeightedBuf w (R.F k) (S k) t ω) s) (1 / s)
        (fun ω => (lem_app_de_resolvent _ s hs0).1) i j
    have hE2 : ∀ i j, |expResT w (R.F k) (S k) t s i j| ≤ 1 / s := fun i j =>
      pt_entry_mean_le (P k) (fun ω => Rts (WeightedBuf w (R.F k) (S k) t ω) s) (1 / s)
        (fun ω => (lem_app_de_resolvent _ s hs0).2.1) i j
    have hD1 : opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤
        (2 / sm) * Real.sqrt ((R.m k : ℝ) * R.m k) := by
      refine (pt_opNorm_le_of_entries _ (2 / s) (by positivity) fun i j => ?_).trans ?_
      · rw [Matrix.sub_apply]
        calc _ ≤ |expRes w (R.F k) (S k) t s i j| + |Rbar (Fw w) (νo k) (νi k) (R.F k).C s i j| :=
              abs_sub _ _
          _ ≤ 1 / s + 1 / s := add_le_add (hE1 i j) ((pt_abs_entry_le_opNorm _ i j).trans hRb1)
          _ = 2 / s := by ring
      · exact mul_le_mul_of_nonneg_right h2s (Real.sqrt_nonneg _)
    have hD2 : opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤
        (2 / sm) * Real.sqrt ((R.n k : ℝ) * R.n k) := by
      refine (pt_opNorm_le_of_entries _ (2 / s) (by positivity) fun i j => ?_).trans ?_
      · rw [Matrix.sub_apply]
        calc _ ≤ |expResT w (R.F k) (S k) t s i j| + |Rtbar (Fw w) (νo k) (νi k) (R.F k).C s i j| :=
              abs_sub _ _
          _ ≤ 1 / s + 1 / s := add_le_add (hE2 i j) ((pt_abs_entry_le_opNorm _ i j).trans hRb2)
          _ = 2 / s := by ring
      · exact mul_le_mul_of_nonneg_right h2s (Real.sqrt_nonneg _)
    simp only [hf]
    rw [mul_add]
    exact add_le_add hD1 hD2
  have hM0 : 0 ≤ (2 / sm) * (Real.sqrt ((R.m k : ℝ) * R.m k) + Real.sqrt ((R.n k : ℝ) * R.n k)) := by
    positivity
  have hfs := pt_le_iSup_mem (I := I) f _ hM0 hb1 hs
  have h3 : f s < η := lt_of_le_of_lt hfs hk
  have n1 := pt_opNorm_nonneg (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s)
  have n2 := pt_opNorm_nonneg (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)
  simp only [hf] at h3
  exact ⟨by linarith, by linarith⟩

private lemma pt_final {I : Set ℝ} (hI : IsCompact I) (sm : ℝ) (hsm : 0 < sm)
    (hsmI : ∀ s ∈ I, sm ≤ s)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (a b Bn : ℕ → ℕ) (K : ∀ k, Ω k → Mat (a k) (b k)) (hK : ∀ k, Measurable (K k))
    (T : ∀ k, Matrix (Fin (a k)) (Fin (a k)) ℂ) (CT : ℝ) (hT : ∀ k, opNorm (T k) ≤ CT)
    (V : ℕ → ℝ) (hV0 : ∀ k, 0 ≤ V k)
    (hV : ∀ k, ∀ s ∈ I,
      cVar (P k) (fun ω => normTrace (T k) (Bn k) (Rs (K k ω) s)) ≤ ENNReal.ofReal (V k))
    (hVlim : Tendsto (fun k => ((Bn k : ℝ) / a k) ^ 2 * V k) atTop (𝓝 0))
    (hpos : ∀ᶠ k in atTop, 0 < a k ∧ 0 < Bn k)
    (Rb : ∀ k, ℝ → Mat (a k) (a k))
    (hbias : ∀ η > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm (Muon.mean (P k) (fun ω => Rs (K k ω) s) - Rb k s) ≤ η) :
    Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ I,
      ENNReal.ofReal (‖normTrace (T k) (a k) (Rs (K k ω) s - Rb k s)‖ ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε' hε'
  by_cases htop : ε' = ⊤
  · exact Filter.Eventually.of_forall fun k => by rw [htop]; exact le_top
  have hr : 0 < ε'.toReal := ENNReal.toReal_pos hε'.ne' htop
  set r := ε'.toReal with hrdef
  have hε'r : ε' = ENNReal.ofReal r := (ENNReal.ofReal_toReal htop).symm
  have hCT0 : 0 ≤ CT := (pt_opNorm_nonneg _).trans (hT 0)
  -- the net mesh
  set u : ℝ := Real.sqrt (r / 48) with hu
  have hu0 : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu2 : u ^ 2 = r / 48 := Real.sq_sqrt (by positivity)
  set δ : ℝ := sm ^ 2 * u / (2 * CT + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hx : 2 * CT * δ / sm ^ 2 ≤ u := by
    rw [hδ]
    have : 2 * CT * (sm ^ 2 * u / (2 * CT + 1)) / sm ^ 2 = (2 * CT / (2 * CT + 1)) * u := by
      field_simp
    rw [this]
    have h1 : 2 * CT / (2 * CT + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  have hx0 : 0 ≤ 2 * CT * δ / sm ^ 2 := by positivity
  have hT2 : 16 * (2 * CT * δ / sm ^ 2) ^ 2 ≤ r / 3 := by
    have : (2 * CT * δ / sm ^ 2) ^ 2 ≤ u ^ 2 := pow_le_pow_left₀ hx0 hx 2
    rw [hu2] at this
    linarith
  -- the bias level
  set η : ℝ := Real.sqrt (r / (24 * (CT ^ 2 + 1))) with hη
  have hη0 : 0 < η := Real.sqrt_pos.mpr (by positivity)
  have hη2 : η ^ 2 = r / (24 * (CT ^ 2 + 1)) := Real.sq_sqrt (by positivity)
  have hT3 : 8 * CT ^ 2 * η ^ 2 ≤ r / 3 := by
    rw [hη2]
    have : 8 * CT ^ 2 * (r / (24 * (CT ^ 2 + 1))) = (r / 3) * (CT ^ 2 / (CT ^ 2 + 1)) := by
      field_simp; ring
    rw [this]
    have h1 : CT ^ 2 / (CT ^ 2 + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    have : 0 ≤ r / 3 := by positivity
    nlinarith
  obtain ⟨N, hN⟩ := pt_gen hI hδ0
  have hlim := hVlim.eventually (Iio_mem_nhds (show (0 : ℝ) < r / (12 * ((N : ℝ) + 1)) by positivity))
  filter_upwards [hpos, hlim, hbias η hη0] with k hk hlk hbk
  rw [hε'r]
  refine le_trans (hN (P k) (K k) (hK k) sm hsm hsmI (T k) CT (hT k) (Bn k) hk.2 hk.1 (V k)
    (hV0 k) (hV k) (Rb k) η hη0.le hbk) (ENNReal.ofReal_le_ofReal ?_)
  have hlk' : ((Bn k : ℝ) / a k) ^ 2 * V k < r / (12 * ((N : ℝ) + 1)) := hlk
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : 4 * (N : ℝ) * ((Bn k : ℝ) / a k) ^ 2 * V k ≤ r / 3 := by
    have e : 4 * (N : ℝ) * ((Bn k : ℝ) / a k) ^ 2 * V k =
        4 * (N : ℝ) * (((Bn k : ℝ) / a k) ^ 2 * V k) := by ring
    rw [e]
    have hp : 0 ≤ ((Bn k : ℝ) / a k) ^ 2 * V k := by have := hV0 k; positivity
    calc 4 * (N : ℝ) * (((Bn k : ℝ) / a k) ^ 2 * V k)
        ≤ 4 * ((N : ℝ) + 1) * (((Bn k : ℝ) / a k) ^ 2 * V k) := by nlinarith
      _ ≤ 4 * ((N : ℝ) + 1) * (r / (12 * ((N : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hlk'.le (by positivity)
      _ = r / 3 := by field_simp; ring
  linarith

private lemma pt_regime_facts (a Bn : ℕ → ℕ) (γ : ℝ) (hγ : 0 < γ)
    (ha : Tendsto (fun k => (a k : ℝ) / Bn k) atTop (𝓝 γ)) (hB : Tendsto Bn atTop atTop) (c0 : ℝ) :
    (∀ᶠ k in atTop, 0 < a k ∧ 0 < Bn k) ∧
      Tendsto (fun k => ((Bn k : ℝ) / a k) ^ 2 * (c0 / Bn k)) atTop (𝓝 0) := by
  have hBr : Tendsto (fun k => (Bn k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hB
  refine ⟨?_, ?_⟩
  · have h1 : ∀ᶠ k in atTop, 0 < Bn k := hB.eventually_gt_atTop 0
    have h2 : ∀ᶠ k in atTop, 0 < (a k : ℝ) / Bn k := ha.eventually (lt_mem_nhds hγ)
    filter_upwards [h1, h2] with k hk1 hk2
    refine ⟨?_, hk1⟩
    have hk1' : (0 : ℝ) < Bn k := by exact_mod_cast hk1
    have : (0 : ℝ) < a k := by
      by_contra hneg
      push Not at hneg
      have : (a k : ℝ) / Bn k ≤ 0 := div_nonpos_of_nonpos_of_nonneg hneg hk1'.le
      linarith
    exact_mod_cast this
  · have h1 : Tendsto (fun k => ((Bn k : ℝ) / a k)) atTop (𝓝 γ⁻¹) := by
      have := ha.inv₀ hγ.ne'
      refine this.congr fun k => ?_
      simp
    have h2 : Tendsto (fun k => c0 / (Bn k : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hBr
    have := (h1.pow 2).mul h2
    simpa using this

private lemma pt_sumPow_nonneg (w : ℕ → ℝ) : 0 ≤ sumPow w 2 := tsum_nonneg fun j => sq_nonneg _

private lemma pt2_opNorm_real_sq {a b : ℕ} (S : Mat a b) (u : Fin b → ℝ) :
    ∑ k, (S *ᵥ u) k ^ 2 ≤ opNorm S ^ 2 * ∑ i, u i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin S (WithLp.toLp 2 u)‖ ≤ opNorm S * ‖WithLp.toLp 2 u‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin S)).le_opNorm (WithLp.toLp 2 u)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma pt2_opNorm_map_ofReal_le {a b : ℕ} (S : Mat a b) :
    opNorm (S.map (fun x : ℝ => (x : ℂ))) ≤ opNorm S := by
  have hM : 0 ≤ opNorm S := by unfold opNorm; exact norm_nonneg _
  have key : ∀ y : Fin b → ℂ, ∑ k, ‖((S.map (fun x : ℝ => (x : ℂ))) *ᵥ y) k‖ ^ 2 ≤
      opNorm S ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
    intro y
    have hk : ∀ k, ‖((S.map (fun x : ℝ => (x : ℂ))) *ᵥ y) k‖ ^ 2 =
        (S *ᵥ (fun i => (y i).re)) k ^ 2 + (S *ᵥ (fun i => (y i).im)) k ^ 2 := by
      intro k
      rw [Complex.sq_norm, Complex.normSq_apply]
      simp [Matrix.mulVec, dotProduct, Matrix.map_apply, Complex.re_sum, Complex.im_sum]
      ring
    calc ∑ k, ‖((S.map (fun x : ℝ => (x : ℂ))) *ᵥ y) k‖ ^ 2
        = ∑ k, ((S *ᵥ (fun i => (y i).re)) k ^ 2 + (S *ᵥ (fun i => (y i).im)) k ^ 2) :=
          Finset.sum_congr rfl fun k _ => hk k
      _ = ∑ k, (S *ᵥ (fun i => (y i).re)) k ^ 2 + ∑ k, (S *ᵥ (fun i => (y i).im)) k ^ 2 :=
          Finset.sum_add_distrib
      _ ≤ opNorm S ^ 2 * ∑ i, (y i).re ^ 2 + opNorm S ^ 2 * ∑ i, (y i).im ^ 2 :=
          add_le_add (pt2_opNorm_real_sq S _) (pt2_opNorm_real_sq S _)
      _ = opNorm S ^ 2 * ∑ i, ‖y i‖ ^ 2 := by
          rw [← mul_add, ← Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Complex.sq_norm, Complex.normSq_apply]
          ring
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ hM fun x => ?_
  have hx := key (WithLp.ofLp x)
  have hsq : ‖Matrix.toEuclideanLin (S.map (fun x : ℝ => (x : ℂ))) x‖ ^ 2 ≤ (opNorm S * ‖x‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)]
    simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct] using hx
  show ‖Matrix.toEuclideanLin (S.map (fun x : ℝ => (x : ℂ))) x‖ ≤ opNorm S * ‖x‖
  nlinarith [norm_nonneg (Matrix.toEuclideanLin (S.map (fun x : ℝ => (x : ℂ))) x),
    mul_nonneg hM (norm_nonneg x)]

open scoped Matrix.Norms.L2Operator in
private lemma pt2_opNorm_scale_le {d B : ℕ} (S : Mat d d) (γ CS : ℝ) (hdim : (d : ℝ) ≤ γ * B)
    (hS : opNorm S ≤ CS) :
    opNorm (((d : ℂ) / (B : ℂ)) • S.map (fun x : ℝ => (x : ℂ))) ≤ |γ| * CS := by
  have hc : ‖((d : ℂ) / (B : ℂ))‖ ≤ |γ| := by
    rcases Nat.eq_zero_or_pos B with rfl | hB
    · simp
    · have hB' : (0 : ℝ) < B := by exact_mod_cast hB
      rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_iff₀ hB']
      calc (d : ℝ) ≤ γ * B := hdim
        _ ≤ |γ| * B := mul_le_mul_of_nonneg_right (le_abs_self γ) hB'.le
  have h2 := (pt2_opNorm_map_ofReal_le S).trans hS
  rw [opNorm_eq_norm, norm_smul, ← opNorm_eq_norm]
  exact mul_le_mul hc h2 (by unfold opNorm; exact norm_nonneg _) (abs_nonneg γ)

private lemma pt2_normTrace_Sout {d B : ℕ} (S E : Mat d d) :
    normTrace (((d : ℂ) / (B : ℂ)) • S.map (fun x : ℝ => (x : ℂ))) d E =
      (((B : ℝ)⁻¹ * (S * E).trace : ℝ) : ℂ) := by
  unfold normTrace
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  rcases Nat.eq_zero_or_pos B with rfl | hB
  · simp
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hB' : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]
  have htr : (S.map (fun x : ℝ => (x : ℂ)) * E.map (fun x : ℝ => (x : ℂ))).trace =
      (((S * E).trace : ℝ) : ℂ) := by
    simp [Matrix.trace, Matrix.mul_apply, Matrix.map_apply, Complex.ofReal_sum]
  rw [htr]
  push_cast
  field_simp

private lemma pt2_branch_trace {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) {s a σ : ℝ}
    (hs : 0 < s) (ha : 0 ≤ a) (hσ : σ = ∫ x, x / (a * x + s) ∂(nuOut C B)) :
    (B : ℝ)⁻¹ * (C.Sout * (s • (1 : Matrix (Fin m) (Fin m) ℝ) + a • C.Sout)⁻¹).trace = σ := by
  rw [hσ, (def_app_de_branch_trace C hB hs ha).1, add_comm (s • (1 : Matrix (Fin m) (Fin m) ℝ))]

private lemma pt2_branch_trace_in {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) {s c σ : ℝ}
    (hs : 0 < s) (hc : 0 ≤ c) (hσ : σ = ∫ x, x / (c * x + s) ∂(nuIn C B)) :
    (B : ℝ)⁻¹ * (C.Sin * (s • (1 : Matrix (Fin n) (Fin n) ℝ) + c • C.Sin)⁻¹).trace = σ := by
  rw [hσ, (def_app_de_branch_trace C hB hs hc).2, add_comm (s • (1 : Matrix (Fin n) (Fin n) ℝ))]

private lemma pt2_branchSol_trace {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (F : ℝ → ℝ)
    (ν ν' : FiniteMeasure ℝ) (hν : (ν : Measure ℝ) = nuOut C B) {s : ℝ} (hs : 0 < s)
    (h : IsBranchSol F ν ν' s (branchSol F ν ν' s)) :
    (B : ℝ)⁻¹ * (C.Sout * Rbar F ν ν' C s).trace = (branchSol F ν ν' s).1 := by
  unfold Rbar
  generalize branchSol F ν ν' s = x at h ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  simp only [IsBranchSol] at h
  obtain ⟨-, -, ha, -, hσ, -, -, -⟩ := h
  rw [hν] at hσ
  exact pt2_branch_trace C hB hs ha hσ

private lemma pt2_branchSol_trace_in {m n B : ℕ} (C : Covariances m n) (hB : 0 < B) (F : ℝ → ℝ)
    (ν ν' : FiniteMeasure ℝ) (hν' : (ν' : Measure ℝ) = nuIn C B) {s : ℝ} (hs : 0 < s)
    (h : IsBranchSol F ν ν' s (branchSol F ν ν' s)) :
    (B : ℝ)⁻¹ * (C.Sin * Rtbar F ν ν' C s).trace = (branchSol F ν ν' s).2.1 := by
  unfold Rtbar
  generalize branchSol F ν ν' s = x at h ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  simp only [IsBranchSol] at h
  obtain ⟨-, -, -, hc, -, hσ', -, -⟩ := h
  rw [hν'] at hσ'
  exact pt2_branch_trace_in C hB hs hc hσ'

private lemma pt2_hK (R : SetupRegime) (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k)) (k : ℕ) :
    (νo k, νi k) ∈ classK R.CSig (max R.γstar 1) := by
  obtain ⟨o1, o2⟩ := assum_app_setup_regime_nuOut R k
  obtain ⟨i1, i2⟩ := assum_app_setup_regime_nuIn R k
  have hle : ENNReal.ofReal R.γstar ≤ ENNReal.ofReal (max R.γstar 1) :=
    ENNReal.ofReal_le_ofReal (le_max_left _ _)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hνo k]; exact (measure_mono (Set.subset_univ _)).trans (o2.trans hle)
  · rw [hνo k]; exact o1
  · rw [hνi k]; exact (measure_mono (Set.subset_univ _)).trans (i2.trans hle)
  · rw [hνi k]; exact i1



/-- `cor:app-de-trace`, part (i), snapshot `cr-2026-10-23`. The output-side trace closure (first display).
LaTeX (`section.tex` l.1163–1176):
\begin{corollary}[Trace closure with bounded tests]\label{cor:app-de-trace}
Under the hypotheses of \cref{thm:app-de-gram}, let $I\subset(0,\infty)$ be compact and let
$T=T_B\in\mathbb{C}^{\Nout\times\Nout}$ and $\widetilde T=\widetilde T_B\in\mathbb{C}^{\Nin\times\Nin}$
be deterministic with $\norm{T_B},\norm{\widetilde T_B}\le C_T$ for all $B$. Then
\begin{equation}\label{eqn:app-de-trace-closure}
\EE\sup_{s\in I}\Big|\frac1{\Nout}\Tr\big[T\big(R(-s)-\Rbar(-s)\big)\big]\Big|^2\longrightarrow0,\qquad
\EE\sup_{s\in I}\Big|\frac1{\Nin}\Tr\big[\widetilde T\big(\widetilde R(-s)-\Rtbar(-s)\big)\big]\Big|^2\longrightarrow0 .
\end{equation}
In particular, in mean square and uniformly on compact $s$-intervals,
\[
\frac1B\Tr\big(\Sigmaout R(-s)\big)\longrightarrow\sigma(-s),\qquad
\frac1B\Tr\big(\Sigmain\widetilde R(-s)\big)\longrightarrow\tilde\sigma(-s).
\]
\end{corollary}
-/
theorem cor_app_de_trace_i
    (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (T : ∀ k, Matrix (Fin (R.m k)) (Fin (R.m k)) ℂ) (hT : ∃ CT : ℝ, ∀ k, opNorm (T k) ≤ CT) :
    Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ I,
      ENNReal.ofReal (‖normTrace (T k) (R.m k)
        (Rs (WeightedBuf w (R.F k) (S k) t ω) s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s)‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
  obtain ⟨CT, hCT⟩ := hT
  obtain ⟨sm, hsm, hsmI⟩ := pt_exists_sm hI hIpos
  obtain ⟨Cv, hCv0, Hv⟩ := lem_app_de_variance_i I hI hIpos R.CSig R.γstar
  have hCT0 : 0 ≤ CT := (pt_opNorm_nonneg _).trans (hCT 0)
  have hbias := pt_gram_pointwise R w hw P S νo νi hνo hνi t I hI hIpos
  obtain ⟨hpos, hlim⟩ := pt_regime_facts R.m R.B R.prop.γout R.prop.γout_pos R.prop.ratio_out
    R.prop.B_top (Cv * CT ^ 2 * sumPow w 2)
  refine pt_final hI sm hsm hsmI P R.m R.n R.B (fun k => WeightedBuf w (R.F k) (S k) t)
    (fun k => pt_meas_WB w (R.F k) (S k) t) T CT hCT
    (fun k => Cv * CT ^ 2 * sumPow w 2 / (R.B k : ℝ))
    (fun k => by have := pt_sumPow_nonneg w; positivity) ?_ hlim hpos
    (fun k s => Rbar (Fw w) (νo k) (νi k) (R.F k).C s) ?_
  · intro k s hs
    exact Hv (R.m k) (R.n k) (R.B k) w hw (Ω k) (P k) (R.F k) (S k) t (R.normOut k) (R.normIn k)
      ((Nat.cast_le.mpr (le_max_left _ _)).trans (R.dims k))
      ((Nat.cast_le.mpr (le_max_right _ _)).trans (R.dims k)) s hs (T k) CT (hCT k)
  · intro η hη
    filter_upwards [hbias η hη] with k hk s hs
    exact (hk s hs).1

/-- `cor:app-de-trace`, part (ii), snapshot `cr-2026-10-23`. The input-side trace closure (second display).
LaTeX (`section.tex` l.1163–1176):
\begin{corollary}[Trace closure with bounded tests]\label{cor:app-de-trace}
Under the hypotheses of \cref{thm:app-de-gram}, let $I\subset(0,\infty)$ be compact and let
$T=T_B\in\mathbb{C}^{\Nout\times\Nout}$ and $\widetilde T=\widetilde T_B\in\mathbb{C}^{\Nin\times\Nin}$
be deterministic with $\norm{T_B},\norm{\widetilde T_B}\le C_T$ for all $B$. Then
\begin{equation}\label{eqn:app-de-trace-closure}
\EE\sup_{s\in I}\Big|\frac1{\Nout}\Tr\big[T\big(R(-s)-\Rbar(-s)\big)\big]\Big|^2\longrightarrow0,\qquad
\EE\sup_{s\in I}\Big|\frac1{\Nin}\Tr\big[\widetilde T\big(\widetilde R(-s)-\Rtbar(-s)\big)\big]\Big|^2\longrightarrow0 .
\end{equation}
In particular, in mean square and uniformly on compact $s$-intervals,
\[
\frac1B\Tr\big(\Sigmaout R(-s)\big)\longrightarrow\sigma(-s),\qquad
\frac1B\Tr\big(\Sigmain\widetilde R(-s)\big)\longrightarrow\tilde\sigma(-s).
\]
\end{corollary}
-/
theorem cor_app_de_trace_ii
    (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (T' : ∀ k, Matrix (Fin (R.n k)) (Fin (R.n k)) ℂ) (hT' : ∃ CT : ℝ, ∀ k, opNorm (T' k) ≤ CT) :
    Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ I,
      ENNReal.ofReal (‖normTrace (T' k) (R.n k)
        (Rts (WeightedBuf w (R.F k) (S k) t ω) s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
  obtain ⟨CT, hCT⟩ := hT'
  obtain ⟨sm, hsm, hsmI⟩ := pt_exists_sm hI hIpos
  obtain ⟨Cv, hCv0, Hv⟩ := lem_app_de_variance_ii I hI hIpos R.CSig R.γstar
  have hCT0 : 0 ≤ CT := (pt_opNorm_nonneg _).trans (hCT 0)
  have hbias := pt_gram_pointwise R w hw P S νo νi hνo hνi t I hI hIpos
  obtain ⟨hpos, hlim⟩ := pt_regime_facts R.n R.B R.prop.γin R.prop.γin_pos R.prop.ratio_in
    R.prop.B_top (Cv * CT ^ 2 * sumPow w 2)
  refine pt_final hI sm hsm hsmI P R.n R.m R.B (fun k ω => (WeightedBuf w (R.F k) (S k) t ω)ᵀ)
    (fun k => (continuous_id.matrix_transpose).measurable.comp (pt_meas_WB w (R.F k) (S k) t))
    T' CT hCT
    (fun k => Cv * CT ^ 2 * sumPow w 2 / (R.B k : ℝ))
    (fun k => by have := pt_sumPow_nonneg w; positivity) ?_ hlim hpos
    (fun k s => Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) ?_
  · intro k s hs
    exact Hv (R.m k) (R.n k) (R.B k) w hw (Ω k) (P k) (R.F k) (S k) t (R.normOut k) (R.normIn k)
      ((Nat.cast_le.mpr (le_max_left _ _)).trans (R.dims k))
      ((Nat.cast_le.mpr (le_max_right _ _)).trans (R.dims k)) s hs (T' k) CT (hCT k)
  · intro η hη
    filter_upwards [hbias η hη] with k hk s hs
    exact (hk s hs).2

/-- `cor:app-de-trace`, in particular (output side), snapshot `cr-2026-10-23`. The in-particular sentence, output side: mean square at each `s ∈ I`, and the uniform form over `I`.
LaTeX (`section.tex` l.1163–1176):
\begin{corollary}[Trace closure with bounded tests]\label{cor:app-de-trace}
Under the hypotheses of \cref{thm:app-de-gram}, let $I\subset(0,\infty)$ be compact and let
$T=T_B\in\mathbb{C}^{\Nout\times\Nout}$ and $\widetilde T=\widetilde T_B\in\mathbb{C}^{\Nin\times\Nin}$
be deterministic with $\norm{T_B},\norm{\widetilde T_B}\le C_T$ for all $B$. Then
\begin{equation}\label{eqn:app-de-trace-closure}
\EE\sup_{s\in I}\Big|\frac1{\Nout}\Tr\big[T\big(R(-s)-\Rbar(-s)\big)\big]\Big|^2\longrightarrow0,\qquad
\EE\sup_{s\in I}\Big|\frac1{\Nin}\Tr\big[\widetilde T\big(\widetilde R(-s)-\Rtbar(-s)\big)\big]\Big|^2\longrightarrow0 .
\end{equation}
In particular, in mean square and uniformly on compact $s$-intervals,
\[
\frac1B\Tr\big(\Sigmaout R(-s)\big)\longrightarrow\sigma(-s),\qquad
\frac1B\Tr\big(\Sigmain\widetilde R(-s)\big)\longrightarrow\tilde\sigma(-s).
\]
\end{corollary}
-/
theorem cor_app_de_trace_iii
    (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    (∀ s ∈ I, Tendsto (fun k => ∫⁻ ω,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sout *
        Rs (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0)) ∧
    Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ I,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sout *
        Rs (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
  have hsup : ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Ioi 0 → Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ J,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sout *
        Rs (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
    intro J hJ hJpos
    have hT : ∃ CT : ℝ, ∀ k, opNorm (((R.m k : ℂ) / (R.B k : ℂ)) •
        (R.F k).C.Sout.map (fun x : ℝ => (x : ℂ))) ≤ CT :=
      ⟨|R.γstar| * R.CSig, fun k => pt2_opNorm_scale_le (R.F k).C.Sout R.γstar R.CSig
        ((Nat.cast_le.mpr (le_max_left _ _)).trans (R.dims k)) (R.normOut k)⟩
    have hres := cor_app_de_trace_i R w hw P S νo νi hνo hνi t J hJ hJpos
      (fun k => ((R.m k : ℂ) / (R.B k : ℂ)) • (R.F k).C.Sout.map (fun x : ℝ => (x : ℂ))) hT
    refine Tendsto.congr (fun k => ?_) hres
    refine lintegral_congr fun ω => iSup_congr fun s => iSup_congr fun hs => ?_
    have hpos : 0 < s := hJpos hs
    have hsol := branchSol_spec (Fw_admissible hw.1) (lt_of_lt_of_le one_pos R.hC)
      (lt_of_lt_of_le one_pos (le_max_right _ _)) (pt2_hK R νo νi hνo hνi k) hpos
    have hkey : (R.B k : ℝ)⁻¹ * ((R.F k).C.Sout * (Rs (WeightedBuf w (R.F k) (S k) t ω) s -
        Rbar (Fw w) (νo k) (νi k) (R.F k).C s)).trace =
        (R.B k : ℝ)⁻¹ * ((R.F k).C.Sout * Rs (WeightedBuf w (R.F k) (S k) t ω) s).trace -
          (branchSol (Fw w) (νo k) (νi k) s).1 := by
      rw [Matrix.mul_sub, Matrix.trace_sub, mul_sub,
        pt2_branchSol_trace (R.F k).C (R.F k).hB (Fw w) (νo k) (νi k) (hνo k) hpos hsol]
    try dsimp only
    rw [pt2_normTrace_Sout, hkey, Complex.norm_real]
  refine ⟨fun s hs => ?_, hsup I hI hIpos⟩
  have h1 := hsup {s} isCompact_singleton (Set.singleton_subset_iff.mpr (hIpos hs))
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left] using h1

/-- `cor:app-de-trace`, in particular (input side), snapshot `cr-2026-10-23`. The in-particular sentence, input side: mean square at each `s ∈ I`, and the uniform form over `I`.
LaTeX (`section.tex` l.1163–1176):
\begin{corollary}[Trace closure with bounded tests]\label{cor:app-de-trace}
Under the hypotheses of \cref{thm:app-de-gram}, let $I\subset(0,\infty)$ be compact and let
$T=T_B\in\mathbb{C}^{\Nout\times\Nout}$ and $\widetilde T=\widetilde T_B\in\mathbb{C}^{\Nin\times\Nin}$
be deterministic with $\norm{T_B},\norm{\widetilde T_B}\le C_T$ for all $B$. Then
\begin{equation}\label{eqn:app-de-trace-closure}
\EE\sup_{s\in I}\Big|\frac1{\Nout}\Tr\big[T\big(R(-s)-\Rbar(-s)\big)\big]\Big|^2\longrightarrow0,\qquad
\EE\sup_{s\in I}\Big|\frac1{\Nin}\Tr\big[\widetilde T\big(\widetilde R(-s)-\Rtbar(-s)\big)\big]\Big|^2\longrightarrow0 .
\end{equation}
In particular, in mean square and uniformly on compact $s$-intervals,
\[
\frac1B\Tr\big(\Sigmaout R(-s)\big)\longrightarrow\sigma(-s),\qquad
\frac1B\Tr\big(\Sigmain\widetilde R(-s)\big)\longrightarrow\tilde\sigma(-s).
\]
\end{corollary}
-/
theorem cor_app_de_trace_iv
    (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    (∀ s ∈ I, Tendsto (fun k => ∫⁻ ω,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sin *
        Rts (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).2.1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0)) ∧
    Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ I,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sin *
        Rts (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).2.1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
  have hsup : ∀ J : Set ℝ, IsCompact J → J ⊆ Set.Ioi 0 → Tendsto (fun k => ∫⁻ ω, ⨆ s ∈ J,
      ENNReal.ofReal (‖(R.B k : ℝ)⁻¹ * Matrix.trace ((R.F k).C.Sin *
        Rts (WeightedBuf w (R.F k) (S k) t ω) s) - (branchSol (Fw w) (νo k) (νi k) s).2.1‖ ^ 2)
      ∂(P k)) atTop (𝓝 0) := by
    intro J hJ hJpos
    have hT : ∃ CT : ℝ, ∀ k, opNorm (((R.n k : ℂ) / (R.B k : ℂ)) •
        (R.F k).C.Sin.map (fun x : ℝ => (x : ℂ))) ≤ CT :=
      ⟨|R.γstar| * R.CSig, fun k => pt2_opNorm_scale_le (R.F k).C.Sin R.γstar R.CSig
        ((Nat.cast_le.mpr (le_max_right _ _)).trans (R.dims k)) (R.normIn k)⟩
    have hres := cor_app_de_trace_ii R w hw P S νo νi hνo hνi t J hJ hJpos
      (fun k => ((R.n k : ℂ) / (R.B k : ℂ)) • (R.F k).C.Sin.map (fun x : ℝ => (x : ℂ))) hT
    refine Tendsto.congr (fun k => ?_) hres
    refine lintegral_congr fun ω => iSup_congr fun s => iSup_congr fun hs => ?_
    have hpos : 0 < s := hJpos hs
    have hsol := branchSol_spec (Fw_admissible hw.1) (lt_of_lt_of_le one_pos R.hC)
      (lt_of_lt_of_le one_pos (le_max_right _ _)) (pt2_hK R νo νi hνo hνi k) hpos
    have hkey : (R.B k : ℝ)⁻¹ * ((R.F k).C.Sin * (Rts (WeightedBuf w (R.F k) (S k) t ω) s -
        Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)).trace =
        (R.B k : ℝ)⁻¹ * ((R.F k).C.Sin * Rts (WeightedBuf w (R.F k) (S k) t ω) s).trace -
          (branchSol (Fw w) (νo k) (νi k) s).2.1 := by
      rw [Matrix.mul_sub, Matrix.trace_sub, mul_sub,
        pt2_branchSol_trace_in (R.F k).C (R.F k).hB (Fw w) (νo k) (νi k) (hνi k) hpos hsol]
    try dsimp only
    rw [pt2_normTrace_Sout, hkey, Complex.norm_real]
  refine ⟨fun s hs => ?_, hsup I hI hIpos⟩
  have h1 := hsup {s} isCompact_singleton (Set.singleton_subset_iff.mpr (hIpos hs))
  simpa only [Set.mem_singleton_iff, iSup_iSup_eq_left] using h1

/-- Trace form of `normTrace` on a difference: `N⁻¹ Tr((A − C)_ℂ T) = normTrace T N (A − C)`. -/
private lemma pt_normTrace_eq {k B : ℕ} (T : Matrix (Fin k) (Fin k) ℂ) (A C : Mat k k) :
    normTrace T B (A - C) = (B : ℂ)⁻¹ *
      ((A.map (fun x : ℝ => (x : ℂ)) - C.map (fun x : ℝ => (x : ℂ))) * T).trace := by
  unfold normTrace
  rw [Matrix.map_sub _ (fun a b => Complex.ofReal_sub a b), Matrix.trace_mul_comm T]

/-- `cor:app-de-trace` (non-record bridge), snapshot `cr-2026-10-23`. Non-record bridge to the shared predicate `def:deterministic-equivalent` (`IsDetEquiv`) at each `z = -s`, `s ∈ I`, with `N_out` normalization. Not the declaration of record of the label.
LaTeX (`section.tex` l.1163–1176):
\begin{corollary}[Trace closure with bounded tests]\label{cor:app-de-trace}
Under the hypotheses of \cref{thm:app-de-gram}, let $I\subset(0,\infty)$ be compact and let
$T=T_B\in\mathbb{C}^{\Nout\times\Nout}$ and $\widetilde T=\widetilde T_B\in\mathbb{C}^{\Nin\times\Nin}$
be deterministic with $\norm{T_B},\norm{\widetilde T_B}\le C_T$ for all $B$. Then
\begin{equation}\label{eqn:app-de-trace-closure}
\EE\sup_{s\in I}\Big|\frac1{\Nout}\Tr\big[T\big(R(-s)-\Rbar(-s)\big)\big]\Big|^2\longrightarrow0,\qquad
\EE\sup_{s\in I}\Big|\frac1{\Nin}\Tr\big[\widetilde T\big(\widetilde R(-s)-\Rtbar(-s)\big)\big]\Big|^2\longrightarrow0 .
\end{equation}
In particular, in mean square and uniformly on compact $s$-intervals,
\[
\frac1B\Tr\big(\Sigmaout R(-s)\big)\longrightarrow\sigma(-s),\qquad
\frac1B\Tr\big(\Sigmain\widetilde R(-s)\big)\longrightarrow\tilde\sigma(-s).
\]
\end{corollary}
-/
theorem cor_app_de_trace_detEquiv
    (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    IsDetEquiv (Ω := Ω) P (fun k => R.m k) (d₁ := fun k => R.m k) (d₂ := fun k => R.m k)
      ((fun s : ℝ => -(s : ℂ)) '' I)
      (fun k z ω => (Rs (WeightedBuf w (R.F k) (S k) t ω) (-z.re)).map (fun x : ℝ => (x : ℂ)))
      (fun k z => (Rbar (Fw w) (νo k) (νi k) (R.F k).C (-z.re)).map (fun x : ℝ => (x : ℂ))) := by
  refine Muon.Setup.isDetEquiv_of_meanSquare P (fun k => R.m k) _ _ _ ?_ ?_
  · intro k z _ i j
    exact Complex.measurable_ofReal.comp
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
        ((pt_Rs_measurable (-z.re)).comp (pt_meas_WB w (R.F k) (S k) t))))
  · rintro z ⟨s, hs, rfl⟩ T hT
    have h1 := cor_app_de_trace_i R w hw P S νo νi hνo hνi t {s} isCompact_singleton
      (Set.singleton_subset_iff.mpr (hIpos hs)) T hT
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left] at h1
    refine Tendsto.congr (fun k => ?_) h1
    simp only [Complex.neg_re, Complex.ofReal_re, neg_neg]
    refine lintegral_congr fun ω => ?_
    rw [pt_normTrace_eq]

end Muon.DetEquiv

end
