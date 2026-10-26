import Muon.DetEquiv.Concentration
import Muon.DetEquiv.Branch
import Muon.DetEquiv.Scalar
import Muon.Setup.Regime
import Muon.Setup.Residual
import Muon.DetEquiv.BranchStability

/-!
# Appendix B: Gram closure and the residual Gaussian limit (task L-B.9)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`, the labels
`lem:app-de-gaussian` (l.1446–1451) and `thm:app-de-gram` (l.1150–1161). CARD §5 WP L-B.9.
Interface draft: every theorem has proof `sorry`; the proofs are assigned to proof workers.

Reuse, nothing redefined: `SetupRegime`, `gaussPair`, `lem_app_setup_residual_iii` (`Setup`);
`WeightClass`, `Fw`, `J` (`DetEquiv.Scalar`); `Rbar`, `Rtbar`, `branchSol` (`DetEquiv.Branch`);
`psiX` (`DetEquiv.Concentration`); `expRes`, `expResT`, `WeightedBuf`, `FrozenSamples`
(`DetEquiv.SampleModel`, `Setup.Frozen`); `nuOut`, `nuIn`, `Covariances`, `opNorm`, `fro`
(`Foundations.Conventions`); `resid` (`Setup.Model`).

Representation choices:
* Spectral measures. `ν_out`, `ν_in` are `Muon.nuOut`, `Muon.nuIn` as `Measure ℝ`. The branch
  functions take `FiniteMeasure ℝ`, so the theorem takes finite measures `νo k`, `νi k` with
  `(νo k : Measure ℝ) = nuOut (R.F k).C (R.B k)` (and `nuIn` for the input side). The
  finiteness proof is not restated here (the `B ≥ 1` finiteness lives in the G2 layer).
* Regime. The full `assum:app-setup-regime` is carried as a `SetupRegime` (the five facts used
  are a subset; a B-local `DERegime` is open question Q5 of CARD §8).
* Time. `M_t` of the frozen model is the buffer at a fixed time `t : ℤ`; the statement is for every
  `t`, and the stationary law makes the choice immaterial.
* Weights. `WeightClass w` (`eqn:app-de-weightclass` with "not all zero", coordinator ruling L2).
* The `sup_{s∈I}` is `⨆ s ∈ I`. It is a real supremum of a family that is bounded on `I` (this
  boundedness is part of the content of the theorem, not assumed).
* The lemma's `sup_{0≤x≤q_I}` is `⨆ x ∈ Icc 0 qI`; the lemma has no sign assumption on `q_I`
  (for `q_I < 0` the set is empty and the statement is trivial).
* Operator norms are `Muon.opNorm` (the L2 operator norm), as in `CARD` §2.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon Muon.Setup

noncomputable section

namespace Muon.DetEquiv

/-! ### Private helpers for `lem_app_de_gaussian` (fully proved) -/

private lemma gram_resid_cont {m n : ℕ} (Δ : Mat m n) :
    Continuous (fun p : Vec m × Vec n => resid Δ p) := by
  unfold resid
  fun_prop

private lemma gram_psi_cont {x : ℝ} (hx : 0 ≤ x) : Continuous (psiX x) := by
  unfold psiX
  refine Continuous.div (by fun_prop) (by fun_prop) (fun d => ?_)
  have := mul_nonneg hx (sq_nonneg d)
  exact (by linarith : (0:ℝ) < 1 + x * d ^ 2).ne'

private lemma gram_psi_abs {x d : ℝ} (hx : 0 ≤ x) : |psiX x d| ≤ d ^ 2 := by
  unfold psiX
  have h1 := mul_nonneg hx (sq_nonneg d)
  rw [abs_of_nonneg (div_nonneg (sq_nonneg d) (by linarith))]
  exact div_le_self (sq_nonneg d) (by linarith)

private lemma gram_psi_lip {x x' d : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    |psiX x d - psiX x' d| ≤ |x - x'| * d ^ 4 := by
  unfold psiX
  have h1 : 0 < 1 + x * d ^ 2 := by have := mul_nonneg hx (sq_nonneg d); linarith
  have h2 : 0 < 1 + x' * d ^ 2 := by have := mul_nonneg hx' (sq_nonneg d); linarith
  have h1' := h1.ne'
  have h2' := h2.ne'
  have key : d ^ 2 / (1 + x * d ^ 2) - d ^ 2 / (1 + x' * d ^ 2)
      = (x' - x) * d ^ 4 / ((1 + x * d ^ 2) * (1 + x' * d ^ 2)) := by
    field_simp
    ring
  have hab : 1 ≤ (1 + x * d ^ 2) * (1 + x' * d ^ 2) := by
    nlinarith [mul_nonneg hx (sq_nonneg d), mul_nonneg hx' (sq_nonneg d),
      mul_nonneg (mul_nonneg hx (sq_nonneg d)) (mul_nonneg hx' (sq_nonneg d))]
  rw [key, abs_div, abs_of_pos (mul_pos h1 h2), abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ d ^ 4), abs_sub_comm x' x]
  exact div_le_self (by positivity) hab

private lemma gram_resid_pow4_int {m n : ℕ} (Δ : Mat m n) (hΔ : fro Δ = 1) :
    Integrable (fun p : Vec m × Vec n => resid Δ p ^ 4) (gaussPair m n) := by
  by_contra h
  have h0 := integral_undef h
  obtain ⟨_, _, h4, _, _⟩ := lem_app_setup_residual_i Δ hΔ
  have hS : 0 ≤ ∑ k ∈ Finset.range (min m n), svals Δ k ^ 4 :=
    Finset.sum_nonneg (fun k _ => by positivity)
  linarith

private lemma gram_integral_map {m n : ℕ} {Ω' : Type*} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] (z : Ω' → Vec m) (w : Ω' → Vec n)
    (hlaw : P.map (fun ω => (z ω, w ω)) = gaussPair m n)
    (hae : AEMeasurable (fun ω => (z ω, w ω)) P) (f : Vec m × Vec n → ℝ)
    (hf : Continuous f) :
    ∫ ω, f (z ω, w ω) ∂P = ∫ p, f p ∂(gaussPair m n) := by
  rw [← hlaw, integral_map hae hf.aestronglyMeasurable]

private lemma gram_psi_gauss_lip {m n : ℕ} (Δ : Mat m n) (hΔ : fro Δ = 1) (hop : opNorm Δ ≤ 1)
    {x x' : ℝ} (hx : 0 ≤ x) (hx' : 0 ≤ x') :
    |(∫ p, psiX x (resid Δ p) ∂(gaussPair m n)) - ∫ p, psiX x' (resid Δ p) ∂(gaussPair m n)|
      ≤ 9 * |x - x'| := by
  have hint : ∀ y : ℝ, 0 ≤ y →
      Integrable (fun p : Vec m × Vec n => psiX y (resid Δ p)) (gaussPair m n) := by
    intro y hy
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (gram_resid_pow4_int Δ hΔ))
      ((gram_psi_cont hy).comp (gram_resid_cont Δ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    show ‖psiX y (resid Δ p)‖ ≤ 1 + resid Δ p ^ 4
    rw [Real.norm_eq_abs]
    have h1 := gram_psi_abs (x := y) (d := resid Δ p) hy
    nlinarith [sq_nonneg (resid Δ p ^ 2 - 1), sq_nonneg (resid Δ p)]
  have hon : 0 ≤ opNorm Δ := by unfold opNorm; exact norm_nonneg _
  have h9 : ∫ p, resid Δ p ^ 4 ∂(gaussPair m n) ≤ 9 := by
    have := (lem_app_setup_residual_i Δ hΔ).2.2.2.1
    nlinarith
  have hbound : ∀ᵐ p ∂(gaussPair m n),
      ‖psiX x (resid Δ p) - psiX x' (resid Δ p)‖ ≤ |x - x'| * resid Δ p ^ 4 :=
    Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact gram_psi_lip hx hx'
  have key := norm_integral_le_of_norm_le (μ := gaussPair m n)
    (f := fun p => psiX x (resid Δ p) - psiX x' (resid Δ p))
    (g := fun p => |x - x'| * resid Δ p ^ 4)
    ((gram_resid_pow4_int Δ hΔ).const_mul _) hbound
  rw [integral_sub (hint x hx) (hint x' hx'), Real.norm_eq_abs] at key
  calc |(∫ p, psiX x (resid Δ p) ∂(gaussPair m n)) - ∫ p, psiX x' (resid Δ p) ∂(gaussPair m n)|
      ≤ ∫ p, |x - x'| * resid Δ p ^ 4 ∂(gaussPair m n) := key
    _ = |x - x'| * ∫ p, resid Δ p ^ 4 ∂(gaussPair m n) := integral_const_mul _ _
    _ ≤ |x - x'| * 9 := mul_le_mul_of_nonneg_left h9 (abs_nonneg _)
    _ = 9 * |x - x'| := by ring

private lemma gram_aem {Ω : Type*} [MeasurableSpace Ω] {m n : ℕ}
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

/-- `lem:app-de-gaussian`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1446–1451):
\begin{lemma}[Uniform Gaussian limit of the residual functional]\label{lem:app-de-gaussian}
With $\psi_x$ as in \cref{lem:app-de-replace} and $d=z^\T\Ahat w$,
\[
r_B\defeq\sup_{0\le x\le q_I}\abs{\EE\,\psi_x(d)-\Jfun(x)}\longrightarrow0 .
\]
\end{lemma}
-/
theorem lem_app_de_gaussian {m n : ℕ → ℕ} {Ω : ℕ → Type*} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (A : ∀ k, Mat (m k) (n k)) (z : ∀ k, Ω k → Vec (m k)) (w : ∀ k, Ω k → Vec (n k))
    (hlaw : ∀ k, (P k).map (fun ω => (z k ω, w k ω)) = gaussPair (m k) (n k))
    (hA : ∀ k, fro (A k) = 1) (hAn : Tendsto (fun k => opNorm (A k)) atTop (𝓝 0))
    (qI : ℝ) :
    Tendsto (fun k => ⨆ x ∈ Icc (0 : ℝ) qI,
      |∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k) - J x|) atTop (𝓝 0) := by
  -- pointwise limit: frozen residual CLT (part iii) applied to the bounded continuous `psiX x`
  have hpt : ∀ x : ℝ, 0 ≤ x → Tendsto (fun k => ∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k))
      atTop (𝓝 (J x)) := by
    intro x hx
    exact (lem_app_setup_residual_iii P A z w hlaw hA hAn).2 (psiX x) (gram_psi_cont hx)
      (fun d => (gram_psi_abs hx).trans (le_add_of_nonneg_left zero_le_one))
  have hop : ∀ᶠ k in atTop, opNorm (A k) < 1 := hAn.eventually (gt_mem_nhds zero_lt_one)
  have hE : ∀ k, ∀ x : ℝ, 0 ≤ x → ∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k)
      = ∫ p, psiX x (resid (A k) p) ∂(gaussPair (m k) (n k)) := fun k x hx =>
    gram_integral_map (P k) (z k) (w k) (hlaw k) (gram_aem (P k) _ (hlaw k)) (fun p => psiX x (resid (A k) p))
      ((gram_psi_cont hx).comp (gram_resid_cont (A k)))
  -- Lipschitz bound for the limit J, inherited from the uniform finite-N bound
  have hJ : ∀ x x' : ℝ, 0 ≤ x → 0 ≤ x' → |J x - J x'| ≤ 9 * |x - x'| := by
    intro x x' hx hx'
    have hc : Tendsto (fun k => |(∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k))
        - ∫ ω, psiX x' (resid (A k) (z k ω, w k ω)) ∂(P k)|) atTop (𝓝 |J x - J x'|) :=
      (continuous_abs.tendsto _).comp ((hpt x hx).sub (hpt x' hx'))
    refine le_of_tendsto hc ?_
    filter_upwards [hop] with k hk
    rw [hE k x hx, hE k x' hx']
    exact gram_psi_gauss_lip (A k) (hA k) hk.le hx hx'
  -- uniform bound via a finite net on [0, qI]
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨t, htsub, htfin, hcover⟩ :=
    finite_cover_balls_of_compact (isCompact_Icc (a := (0:ℝ)) (b := qI)) (by linarith : (0:ℝ) < ε / 36)
  have hnet : ∀ᶠ k in atTop, ∀ xi ∈ t,
      dist (∫ ω, psiX xi (resid (A k) (z k ω, w k ω)) ∂(P k)) (J xi) < ε / 3 := by
    refine (eventually_all_finite htfin).2 (fun xi hxi => ?_)
    exact Metric.tendsto_nhds.1 (hpt xi (htsub hxi).1) (ε / 3) (by linarith)
  filter_upwards [hnet, hop] with k hk1 hk2
  have hbound : ∀ x ∈ Icc (0:ℝ) qI,
      |(∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k)) - J x| ≤ 5 * ε / 6 := by
    intro x hx
    obtain ⟨xi, hxi, hball⟩ := mem_iUnion₂.1 (hcover hx)
    have hdist : |x - xi| < ε / 36 := by
      rw [← Real.dist_eq]; exact Metric.mem_ball.1 hball
    have h1 := hk1 xi hxi
    rw [Real.dist_eq] at h1
    have hL1 := gram_psi_gauss_lip (A k) (hA k) hk2.le hx.1 (htsub hxi).1
    rw [← hE k x hx.1, ← hE k xi (htsub hxi).1] at hL1
    have hL2 := hJ xi x (htsub hxi).1 hx.1
    rw [abs_sub_comm xi x] at hL2
    have t1 := abs_sub_le (∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k))
      (∫ ω, psiX xi (resid (A k) (z k ω, w k ω)) ∂(P k)) (J x)
    have t2 := abs_sub_le (∫ ω, psiX xi (resid (A k) (z k ω, w k ω)) ∂(P k)) (J xi) (J x)
    linarith
  have hG0 : 0 ≤ ⨆ x ∈ Icc (0:ℝ) qI,
      |(∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k)) - J x| :=
    Real.iSup_nonneg fun x => Real.iSup_nonneg fun _ => abs_nonneg _
  have hG : (⨆ x ∈ Icc (0:ℝ) qI,
      |(∫ ω, psiX x (resid (A k) (z k ω, w k ω)) ∂(P k)) - J x|) ≤ 5 * ε / 6 :=
    Real.iSup_le (fun x => Real.iSup_le (fun hx => hbound x hx) (by linarith)) (by linarith)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hG0]
  linarith

/-! ### Private helpers for `eqn_app_de_Pj_P` -/

private lemma pj_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

private lemma pj_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma pj_sq_mulVec {a b : ℕ} (K : Mat a b) (x : Vec b) :
    ∑ i, (K *ᵥ x) i ^ 2 ≤ opNorm K ^ 2 * ∑ i, x i ^ 2 := by
  have h2 : ‖Matrix.toEuclideanLin K (WithLp.toLp 2 x)‖ ≤ opNorm K * ‖WithLp.toLp 2 x‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)).le_opNorm (WithLp.toLp 2 x)
    simpa [opNorm] using this
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)] at h3
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using h3

private lemma pj_sqrt_quad_le {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (C : ℝ) (hC : opNorm S ≤ C) (z : Vec m) :
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
  have hn : ∀ v : Vec m, ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, v i ^ 2 := by
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
    _ ≤ ‖WithLp.toLp 2 z‖ * (C * ‖WithLp.toLp 2 z‖) :=
        mul_le_mul_of_nonneg_left h4 (norm_nonneg _)
    _ = C * ‖WithLp.toLp 2 z‖ ^ 2 := by ring

/-- Fourth moment of a Gaussian: `∫ y^4 d N(0,v) = 3 v^2`. -/
private lemma pj_gauss4 (v : NNReal) :
    ∫ y : ℝ, y ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h : gaussianReal 0 v = (gaussianReal 0 1).map (fun g => Real.sqrt v * g) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  rw [h, integral_map (by fun_prop) (by fun_prop)]
  have : ∀ g : ℝ, (Real.sqrt v * g) ^ 4 = (v : ℝ) ^ 2 * g ^ 4 := by
    intro g
    have := Real.sq_sqrt (NNReal.coe_nonneg v)
    calc (Real.sqrt v * g) ^ 4 = (Real.sqrt v ^ 2) ^ 2 * g ^ 4 := by ring
      _ = _ := by rw [this]
  simp_rw [this]
  rw [integral_const_mul, Muon.Foundations.gaussian_moment_four]
  ring

private lemma pj_lint4_one (v : NNReal) :
    ∫⁻ y : ℝ, ENNReal.ofReal (y ^ 4) ∂(gaussianReal 0 v) = ENNReal.ofReal (3 * (v : ℝ) ^ 2) := by
  have h : gaussianReal 0 v = (gaussianReal 0 1).map (fun g => Real.sqrt v * g) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp
  rw [h, lintegral_map (by fun_prop) (by fun_prop)]
  have : ∀ g : ℝ, (Real.sqrt v * g) ^ 4 = (v : ℝ) ^ 2 * g ^ 4 := by
    intro g
    have := Real.sq_sqrt (NNReal.coe_nonneg v)
    calc (Real.sqrt v * g) ^ 4 = (Real.sqrt v ^ 2) ^ 2 * g ^ 4 := by ring
      _ = _ := by rw [this]
  simp_rw [this]
  have hnn : 0 ≤ (v : ℝ) ^ 2 := by positivity
  simp_rw [ENNReal.ofReal_mul hnn]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have h4 : ∫⁻ g : ℝ, ENNReal.ofReal (g ^ 4) ∂(gaussianReal 0 1) = ENNReal.ofReal 3 := by
    rw [← Muon.Foundations.gaussian_moment_four,
      ofReal_integral_eq_lintegral_ofReal (Muon.Foundations.gaussian_integrable_pow 4)
        (Filter.Eventually.of_forall fun g => by positivity)]
  rw [h4, ← ENNReal.ofReal_mul hnn]
  congr 1; ring

private lemma pj_lint4_fst {m n : ℕ} (c : Vec m) :
    ∫⁻ x : Vec m × Vec n, ENNReal.ofReal ((∑ i, x.1 i * c i) ^ 4) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (3 * (∑ i, c i ^ 2) ^ 2) := by
  have hmp : MeasurePreserving (Prod.fst : Vec m × Vec n → Vec m) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi m) := measurePreserving_fst
  have hmeas : Measurable (fun z : Vec m => ENNReal.ofReal ((∑ i, z i * c i) ^ 4)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Continuous fun z : Vec m => (∑ i, z i * c i) ^ 4).measurable
  have h1 := hmp.lintegral_comp hmeas
  have h2 : ∫⁻ z : Vec m, ENNReal.ofReal ((∑ i, z i * c i) ^ 4) ∂(Muon.Foundations.stdGaussianPi m)
      = ∫⁻ y : ℝ, ENNReal.ofReal (y ^ 4) ∂(gaussianReal 0 (Real.toNNReal (∑ i, c i ^ 2))) := by
    rw [← Muon.Foundations.stdGaussianPi_linear_map m c,
      lintegral_map (by fun_prop) (by fun_prop)]
  have h3 := pj_lint4_one (Real.toNNReal (∑ i, c i ^ 2))
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h3
  exact (le_of_eq (h1.trans (h2.trans h3)))

private lemma pj_lint4_snd {m n : ℕ} (c : Vec n) :
    ∫⁻ x : Vec m × Vec n, ENNReal.ofReal ((∑ i, x.2 i * c i) ^ 4) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (3 * (∑ i, c i ^ 2) ^ 2) := by
  have hmp : MeasurePreserving (Prod.snd : Vec m × Vec n → Vec n) (gaussPair m n)
      (Muon.Foundations.stdGaussianPi n) := measurePreserving_snd
  have hmeas : Measurable (fun z : Vec n => ENNReal.ofReal ((∑ i, z i * c i) ^ 4)) := by
    apply ENNReal.measurable_ofReal.comp
    exact (by fun_prop : Continuous fun z : Vec n => (∑ i, z i * c i) ^ 4).measurable
  have h1 := hmp.lintegral_comp hmeas
  have h2 : ∫⁻ z : Vec n, ENNReal.ofReal ((∑ i, z i * c i) ^ 4) ∂(Muon.Foundations.stdGaussianPi n)
      = ∫⁻ y : ℝ, ENNReal.ofReal (y ^ 4) ∂(gaussianReal 0 (Real.toNNReal (∑ i, c i ^ 2))) := by
    rw [← Muon.Foundations.stdGaussianPi_linear_map n c,
      lintegral_map (by fun_prop) (by fun_prop)]
  have h3 := pj_lint4_one (Real.toNNReal (∑ i, c i ^ 2))
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h3
  exact (le_of_eq (h1.trans (h2.trans h3)))

/-- Lintegral Cauchy–Schwarz for nonnegative measurable real functions. -/
private lemma pj_cs {α : Type*} [MeasurableSpace α] (μ : Measure α) (f g : α → ℝ)
    (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (A Bv : ℝ) (hA0 : 0 ≤ A) (hB0 : 0 ≤ Bv)
    (hA : ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ ≤ ENNReal.ofReal A)
    (hB : ∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ ≤ ENNReal.ofReal Bv) :
    ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ ≤ ENNReal.ofReal (Real.sqrt A * Real.sqrt Bv) := by
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ (Real.HolderConjugate.two_two)
    (f := fun x => ENNReal.ofReal (f x)) (g := fun x => ENNReal.ofReal (g x))
    (ENNReal.measurable_ofReal.comp hf).aemeasurable (ENNReal.measurable_ofReal.comp hg).aemeasurable
  have e1 : ∀ h : α → ℝ, (∀ x, 0 ≤ h x) → ∫⁻ x, ENNReal.ofReal (h x) ^ (2 : ℝ) ∂μ
      = ∫⁻ x, ENNReal.ofReal (h x ^ 2) ∂μ := by
    intro h h0
    refine lintegral_congr fun x => ?_
    rw [ENNReal.ofReal_rpow_of_nonneg (h0 x) (by norm_num)]
    congr 1
    exact Real.rpow_two _
  have e2 : ∫⁻ x, ENNReal.ofReal (f x * g x) ∂μ = ∫⁻ x, (ENNReal.ofReal (f x) * ENNReal.ofReal (g x)) ∂μ :=
    lintegral_congr fun x => ENNReal.ofReal_mul (hf0 x)
  rw [e2]
  refine hcs.trans ?_
  rw [e1 f hf0, e1 g hg0]
  have hh : (1 : ℝ) / 2 = 2⁻¹ := by norm_num
  calc (∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂μ) ^ (1 / (2 : ℝ)) *
        (∫⁻ x, ENNReal.ofReal (g x ^ 2) ∂μ) ^ (1 / (2 : ℝ))
      ≤ (ENNReal.ofReal A) ^ (1 / (2 : ℝ)) * (ENNReal.ofReal Bv) ^ (1 / (2 : ℝ)) :=
        mul_le_mul' (ENNReal.rpow_le_rpow hA (by norm_num)) (ENNReal.rpow_le_rpow hB (by norm_num))
    _ = ENNReal.ofReal (Real.sqrt A * Real.sqrt Bv) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hA0 (by norm_num),
          ENNReal.ofReal_rpow_of_nonneg hB0 (by norm_num), ← ENNReal.ofReal_mul (by positivity),
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]

/-- Triple Hölder: `∫ P |ℓ₁| |ℓ₂| ≤ √K_P · √(3 q₁ q₂)`. -/
private lemma pj_holder {α : Type*} [MeasurableSpace α] (μ : Measure α) (P l1 l2 : α → ℝ)
    (hP : Measurable P) (h1 : Measurable l1) (h2 : Measurable l2) (hP0 : ∀ x, 0 ≤ P x)
    (KP q1 q2 : ℝ) (hKP : 0 ≤ KP) (hq1 : 0 ≤ q1) (hq2 : 0 ≤ q2)
    (hPm : ∫⁻ x, ENNReal.ofReal (P x ^ 2) ∂μ ≤ ENNReal.ofReal KP)
    (h1m : ∫⁻ x, ENNReal.ofReal (l1 x ^ 4) ∂μ ≤ ENNReal.ofReal (3 * q1 ^ 2))
    (h2m : ∫⁻ x, ENNReal.ofReal (l2 x ^ 4) ∂μ ≤ ENNReal.ofReal (3 * q2 ^ 2)) :
    ∫⁻ x, ENNReal.ofReal (P x * (|l1 x| * |l2 x|)) ∂μ
      ≤ ENNReal.ofReal (Real.sqrt KP * Real.sqrt (3 * (q1 * q2))) := by
  have hmid : ∫⁻ x, ENNReal.ofReal ((|l1 x| * |l2 x|) ^ 2) ∂μ ≤ ENNReal.ofReal (3 * (q1 * q2)) := by
    have := pj_cs μ (fun x => l1 x ^ 2) (fun x => l2 x ^ 2) (by fun_prop) (by fun_prop)
      (fun x => sq_nonneg _) (fun x => sq_nonneg _) (3 * q1 ^ 2) (3 * q2 ^ 2) (by positivity)
      (by positivity)
      (by simpa only [← pow_mul] using h1m) (by simpa only [← pow_mul] using h2m)
    have e : ∀ x, (|l1 x| * |l2 x|) ^ 2 = l1 x ^ 2 * l2 x ^ 2 := fun x => by
      rw [mul_pow, sq_abs, sq_abs]
    simp_rw [e]
    refine this.trans (le_of_eq ?_)
    congr 1
    have a1 : Real.sqrt (3 * q1 ^ 2) = Real.sqrt 3 * q1 := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hq1]
    have a2 : Real.sqrt (3 * q2 ^ 2) = Real.sqrt 3 * q2 := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq hq2]
    rw [a1, a2]
    have := Real.mul_self_sqrt (show (0:ℝ) ≤ 3 by norm_num)
    linear_combination (q1 * q2) * this
  exact pj_cs μ P (fun x => |l1 x| * |l2 x|) hP (by fun_prop) hP0 (fun x => by positivity) KP
    (3 * (q1 * q2)) hKP (by positivity) hPm hmid

private lemma pj_lint_pow {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ)
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

private lemma pj_one_add_pow (a : ℝ) (ha : 0 ≤ a) (p : ℕ) : (1 + a) ^ p ≤ 2 ^ p * (1 + a ^ p) := by
  rcases le_total a 1 with h | h
  · calc (1 + a) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + a ^ p) := le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg ha p])
  · calc (1 + a) ^ p ≤ (2 * a) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * a ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + a ^ p) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private lemma pj_young (u v : ℝ) (hu : 1 ≤ u) (hv : 1 ≤ v) :
    u ^ 8 * v ^ 6 ≤ u ^ 14 + v ^ 14 := by
  rcases le_total u v with h | h
  · have h1 : u ^ 8 ≤ v ^ 8 := pow_le_pow_left₀ (by linarith) h 8
    have h2 : u ^ 8 * v ^ 6 ≤ v ^ 8 * v ^ 6 :=
      mul_le_mul_of_nonneg_right h1 (by positivity)
    have : v ^ 8 * v ^ 6 = v ^ 14 := by ring
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ u) 14]
  · have h1 : v ^ 6 ≤ u ^ 6 := pow_le_pow_left₀ (by linarith) h 6
    have h2 : u ^ 8 * v ^ 6 ≤ u ^ 8 * u ^ 6 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have : u ^ 8 * u ^ 6 = u ^ 14 := by ring
    nlinarith [pow_nonneg (by linarith : (0:ℝ) ≤ v) 14]

private lemma pj_P_moment {m n : ℕ} (C : Covariances m n) (B : ℕ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) (Ah : Mat m n) (hA : fro Ah = 1) :
    ∫⁻ x, ENNReal.ofReal (((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 2) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ))) := by
  have hC0 : 0 ≤ CSig := le_trans (pj_opNorm_nonneg _) hC.1
  have hNm : Measurable (momN C B : Vec m × Vec n → ℝ) := by
    unfold momN eucNorm momU momV
    fun_prop
  have hNnn : ∀ x, 0 ≤ momN C B x := fun x => by unfold momN; positivity
  have hdm : Measurable (fun x : Vec m × Vec n => resid Ah x) := by unfold resid; fun_prop
  -- moment of d
  have hd := pj_lint_pow (gaussPair m n) (fun x => resid Ah x) hdm 14 (by norm_num)
    (((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ ((1 : ℝ) / 7)) (by positivity)
    (by simpa using lem_app_de_moments_ii Ah hA 7 (by norm_num))
  have hdD : (((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ ((1 : ℝ) / 7)) ^ 14
      = ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [hdD] at hd
  -- moment of N
  have hN := pj_lint_pow (gaussPair m n) (momN C B) hNm 14 (by norm_num)
    (2 * CSig * γ * ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ ((1 : ℝ) / 14)) (by positivity)
    (by simpa using lem_app_de_moments_i C B γ CSig hdim hC 14 (by norm_num))
  have hNN : (2 * CSig * γ * ((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ ((1 : ℝ) / 14)) ^ 14
      = (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ) := by
    rw [mul_pow, ← Real.rpow_natCast (((Nat.doubleFactorial 27 : ℕ) : ℝ) ^ ((1 : ℝ) / 14)),
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  rw [hNN] at hN
  have habsN : ∀ x : Vec m × Vec n, |momN C B x| = momN C B x := fun x => abs_of_nonneg (hNnn x)
  simp_rw [habsN] at hN
  -- pointwise bound
  have hpt : ∀ x : Vec m × Vec n, ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 2
      ≤ 2 ^ 14 * 2 + 2 ^ 14 * |resid Ah x| ^ 14 + 2 ^ 14 * momN C B x ^ 14 := by
    intro x
    have h1 : ((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 2
        = (1 + |resid Ah x|) ^ 8 * (1 + momN C B x) ^ 6 := by ring
    rw [h1]
    refine (pj_young _ _ (by linarith [abs_nonneg (resid Ah x)]) (by linarith [hNnn x])).trans ?_
    have a1 := pj_one_add_pow _ (abs_nonneg (resid Ah x)) 14
    have a2 := pj_one_add_pow _ (hNnn x) 14
    nlinarith [a1, a2]
  calc ∫⁻ x, ENNReal.ofReal (((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 2) ∂(gaussPair m n)
      ≤ ∫⁻ x, (ENNReal.ofReal (2 ^ 14 * 2) + ENNReal.ofReal (2 ^ 14) * ENNReal.ofReal (|resid Ah x| ^ 14)
          + ENNReal.ofReal (2 ^ 14) * ENNReal.ofReal (momN C B x ^ 14)) ∂(gaussPair m n) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal (2 ^ 14 * 2) + ENNReal.ofReal (2 ^ 14) * ∫⁻ x, ENNReal.ofReal (|resid Ah x| ^ 14) ∂(gaussPair m n)
          + ENNReal.ofReal (2 ^ 14) * ∫⁻ x, ENNReal.ofReal (momN C B x ^ 14) ∂(gaussPair m n) := by
        have m1 : Measurable (fun x : Vec m × Vec n => ENNReal.ofReal (|resid Ah x| ^ 14)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        have m2 : Measurable (fun x : Vec m × Vec n => ENNReal.ofReal (momN C B x ^ 14)) :=
          ENNReal.measurable_ofReal.comp (by fun_prop)
        rw [lintegral_add_left ((m1.const_mul _).const_add _), lintegral_add_left measurable_const,
          lintegral_const_mul _ m1, lintegral_const_mul _ m2, lintegral_const, measure_univ, mul_one]
    _ ≤ ENNReal.ofReal (2 ^ 14 * 2) + ENNReal.ofReal (2 ^ 14) * ENNReal.ofReal (((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2)
          + ENNReal.ofReal (2 ^ 14) * ENNReal.ofReal ((2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ)) := by
        gcongr
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

private lemma pj_sqrt_symm {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
  have hR : (CFC.sqrt S).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian
  simpa using hR.eq

/-- A fixed linear functional of `u = Σout^{1/2} z/√B` is a linear form in `z`, with small norm. -/
private lemma pj_form_gen {k l : ℕ} (S : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosSemidef)
    (B : ℕ) (CSig b : ℝ) (hC : opNorm S ≤ CSig) (T : Mat l k) (hT : opNorm T ≤ b) (t : Vec l) :
    ∃ c : Vec k, (∀ z : Vec k, dotProduct t (T *ᵥ ((Real.sqrt (B : ℝ))⁻¹ • (CFC.sqrt S *ᵥ z)))
        = ∑ i, z i * c i) ∧
      ∑ i, c i ^ 2 ≤ CSig * b ^ 2 * (∑ i, t i ^ 2) / B := by
  have hb : 0 ≤ b := le_trans (pj_opNorm_nonneg _) hT
  refine ⟨(Real.sqrt (B : ℝ))⁻¹ • ((t ᵥ* T) ᵥ* CFC.sqrt S), fun z => ?_, ?_⟩
  · rw [Matrix.mulVec_smul, dotProduct_smul, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec]
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · have e1 : (t ᵥ* T) ᵥ* CFC.sqrt S = CFC.sqrt S *ᵥ (t ᵥ* T) := by
      rw [← Matrix.mulVec_transpose, pj_sqrt_symm]
    have e2 : t ᵥ* T = Tᵀ *ᵥ t := by rw [Matrix.mulVec_transpose]
    have h1 := pj_sqrt_quad_le S hS CSig hC (t ᵥ* T)
    have h2 := pj_sq_mulVec Tᵀ t
    rw [pj_opNorm_transpose] at h2
    rw [← e2] at h2
    have hB : (Real.sqrt (B : ℝ))⁻¹ ^ 2 = (B : ℝ)⁻¹ := by
      rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
    have h3 : ∑ i, (((Real.sqrt (B : ℝ))⁻¹ • ((t ᵥ* T) ᵥ* CFC.sqrt S)) i) ^ 2
        = (B : ℝ)⁻¹ * ∑ i, ((t ᵥ* T) ᵥ* CFC.sqrt S) i ^ 2 := by
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, hB]
    rw [h3, e1]
    have hCs : 0 ≤ CSig := le_trans (pj_opNorm_nonneg _) hC
    have h4 : opNorm T ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (pj_opNorm_nonneg _) hT 2
    have hts : 0 ≤ ∑ i, t i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc (B : ℝ)⁻¹ * ∑ i, (CFC.sqrt S *ᵥ (t ᵥ* T)) i ^ 2
        ≤ (B : ℝ)⁻¹ * (CSig * ∑ i, (t ᵥ* T) i ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (B : ℝ)⁻¹ * (CSig * (b ^ 2 * ∑ i, t i ^ 2)) := by
          gcongr
          exact h2.trans (mul_le_mul_of_nonneg_right h4 hts)
      _ = CSig * b ^ 2 * (∑ i, t i ^ 2) / B := by field_simp

private lemma pj_outer_form {m : ℕ} (p q x y : Vec m) :
    dotProduct x (outer p q *ᵥ y) = dotProduct x p * dotProduct q y := by
  simp only [dotProduct, Matrix.mulVec, outer, Matrix.vecMulVec_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

private lemma pj_real (a1 a2 a3 p q r s' K : ℝ) (h1 : |a1| ≤ K) (h2 : |a2| ≤ K) (h3 : |a3| ≤ K) :
    |a3 * (p * q) - a1 * (p * r) - a1 * (s' * q) + a2 * (s' * r)| ≤
      K * ((|p| + |s'|) * (|q| + |r|)) := by
  have hK : 0 ≤ K := le_trans (abs_nonneg _) h1
  have t3 : |a3 * (p * q)| ≤ K * (|p| * |q|) := by
    rw [abs_mul, abs_mul]; exact mul_le_mul h3 le_rfl (by positivity) hK
  have t1 : |a1 * (p * r)| ≤ K * (|p| * |r|) := by
    rw [abs_mul, abs_mul]; exact mul_le_mul h1 le_rfl (by positivity) hK
  have t1' : |a1 * (s' * q)| ≤ K * (|s'| * |q|) := by
    rw [abs_mul, abs_mul]; exact mul_le_mul h1 le_rfl (by positivity) hK
  have t2 : |a2 * (s' * r)| ≤ K * (|s'| * |r|) := by
    rw [abs_mul, abs_mul]; exact mul_le_mul h2 le_rfl (by positivity) hK
  calc |a3 * (p * q) - a1 * (p * r) - a1 * (s' * q) + a2 * (s' * r)|
      ≤ |a3 * (p * q)| + |a1 * (p * r)| + |a1 * (s' * q)| + |a2 * (s' * r)| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ K * (|p| * |q|) + K * (|p| * |r|) + K * (|s'| * |q|) + K * (|s'| * |r|) := by
        gcongr
    _ = _ := by ring

private lemma pj_pt {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) {m n : ℕ}
    (M₀ : Mat m n) (u : Vec m) (v : Vec n) (d ϖ : ℝ) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (s : ℝ) (hs : s ∈ I) (xv yv : Vec m) :
    |dotProduct xv ((Rs (M₀ + (ϖ * d) • outer u v) s - Rs M₀ s) *ᵥ yv)| ≤
      coeffConst I * ϖ * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) *
        ((|dotProduct xv (Rs M₀ s *ᵥ u)| + |dotProduct xv (Xs M₀ s *ᵥ v)|) *
          (|dotProduct yv (Rs M₀ s *ᵥ u)| + |dotProduct yv (Xs M₀ s *ᵥ v)|)) := by
  have hs0 : 0 < s := hIpos hs
  obtain ⟨b1, b2, -, -, -, -⟩ := lem_app_de_coeff hI hIpos M₀ u v (M₀ + (ϖ * d) • outer u v) d ϖ
    rfl hϖ0 hϖ1 s hs
  obtain ⟨-, hid, -, -, -⟩ := lem_app_de_deletion M₀ (ϖ * d) u v (M₀ + (ϖ * d) • outer u v) s rfl hs0
  have hN0 : 0 ≤ sqNorm u + sqNorm v := by
    unfold sqNorm
    exact add_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hP0 : 0 ≤ (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 := by positivity
  have hCc0 : 0 ≤ coeffConst I := by unfold coeffConst; positivity
  have e1 : coeffConst I * ϖ * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3
      = coeffConst I * ϖ * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := by ring
  have e2 : coeffConst I * ϖ ^ 2 * (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3
      = coeffConst I * ϖ ^ 2 * ((1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3) := by ring
  rw [e1] at b1
  rw [e2] at b2
  generalize (1 + |d|) ^ 4 * (1 + (sqNorm u + sqNorm v)) ^ 3 = P at hP0 b1 b2 ⊢
  generalize coeffConst I = Cc at hCc0 b1 b2 ⊢
  have hb1' : |alpha1 M₀ (ϖ * d) u v s| ≤ Cc * ϖ * P := by linarith [b1]
  have hϖ2 : ϖ ^ 2 ≤ ϖ := by nlinarith
  have hCP : Cc * ϖ ^ 2 * P ≤ Cc * ϖ * P := by
    have := mul_nonneg hCc0 hP0
    nlinarith [mul_le_mul_of_nonneg_left hϖ2 this]
  have hb2' : |alpha2 M₀ (ϖ * d) u v s| ≤ Cc * ϖ * P := by
    nlinarith [b2, abs_nonneg (alpha3 M₀ (ϖ * d) u v s)]
  have hb3' : |alpha3 M₀ (ϖ * d) u v s| ≤ Cc * ϖ * P := by
    nlinarith [b2, abs_nonneg (alpha2 M₀ (ϖ * d) u v s)]
  have hexp : dotProduct xv ((Rs (M₀ + (ϖ * d) • outer u v) s - Rs M₀ s) *ᵥ yv)
      = alpha3 M₀ (ϖ * d) u v s * (dotProduct xv (Rs M₀ s *ᵥ u) * dotProduct yv (Rs M₀ s *ᵥ u))
        - alpha1 M₀ (ϖ * d) u v s * (dotProduct xv (Rs M₀ s *ᵥ u) * dotProduct yv (Xs M₀ s *ᵥ v))
        - alpha1 M₀ (ϖ * d) u v s * (dotProduct xv (Xs M₀ s *ᵥ v) * dotProduct yv (Rs M₀ s *ᵥ u))
        + alpha2 M₀ (ϖ * d) u v s * (dotProduct xv (Xs M₀ s *ᵥ v) * dotProduct yv (Xs M₀ s *ᵥ v)) := by
    rw [hid]
    simp only [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_sub,
      dotProduct_add, dotProduct_smul, pj_outer_form, smul_eq_mul, dotProduct_comm (Rs M₀ s *ᵥ u) yv,
      dotProduct_comm (Xs M₀ s *ᵥ v) yv]
  rw [hexp]
  exact pj_real _ _ _ _ _ _ _ _ hb1' hb2' hb3'

private lemma pj_lin_fst_le {m n : ℕ} (c : Vec m) (Q : ℝ) (hc : ∑ i, c i ^ 2 ≤ Q) :
    ∫⁻ x : Vec m × Vec n, ENNReal.ofReal ((∑ i, x.1 i * c i) ^ 4) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (3 * Q ^ 2) := by
  refine (pj_lint4_fst c).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := pow_le_pow_left₀ h0 hc 2
  linarith

private lemma pj_lin_snd_le {m n : ℕ} (c : Vec n) (Q : ℝ) (hc : ∑ i, c i ^ 2 ≤ Q) :
    ∫⁻ x : Vec m × Vec n, ENNReal.ofReal ((∑ i, x.2 i * c i) ^ 4) ∂(gaussPair m n)
      ≤ ENNReal.ofReal (3 * Q ^ 2) := by
  refine (pj_lint4_snd c).trans (ENNReal.ofReal_le_ofReal ?_)
  have h0 : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have := pow_le_pow_left₀ h0 hc 2
  linarith

private lemma pj_N_eq {m n : ℕ} (C : Covariances m n) (B : ℕ) (x : Vec m × Vec n) :
    sqNorm (momU C B x) + sqNorm (momV C B x) = momN C B x := by
  unfold momN eucNorm sqNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _),
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

private lemma pj_inner {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) {m n : ℕ}
    (C : Covariances m n) (B : ℕ) (hB : 0 < B) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm C.Sout ≤ CSig ∧ opNorm C.Sin ≤ CSig) (Ah : Mat m n) (hA : fro Ah = 1)
    (sm : ℝ) (hsm : 0 < sm) (ϖ : ℝ) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ ≤ 1)
    (s : ℝ) (hs : s ∈ I) (hsms : sm ≤ s) (M₀ : Mat m n) (xv yv : Vec m) :
    ∫⁻ x : Vec m × Vec n, ENNReal.ofReal
        |dotProduct xv ((Rs (M₀ + (ϖ * resid Ah x) • outer (momU C B x) (momV C B x)) s - Rs M₀ s) *ᵥ yv)|
        ∂(gaussPair m n)
      ≤ ENNReal.ofReal (coeffConst I * ϖ * (4 * (Real.sqrt (2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ))) *
          Real.sqrt (3 * ((CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, xv i ^ 2) / B) *
            (CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, yv i ^ 2) / B)))))) := by
  have hs0 : 0 < s := hIpos hs
  have hCs : 0 ≤ CSig := le_trans (pj_opNorm_nonneg _) hC.1
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCc0 : 0 ≤ coeffConst I := by unfold coeffConst; positivity
  set b : ℝ := 1 / sm + 1 / (2 * Real.sqrt sm) with hbdef
  have hsq : 0 < Real.sqrt sm := Real.sqrt_pos.mpr hsm
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  obtain ⟨hR, -, hX, -⟩ := lem_app_de_resolvent M₀ s hs0
  have hT1 : opNorm (Rs M₀ s) ≤ b := by
    refine hR.trans ?_
    have : 1 / s ≤ 1 / sm := one_div_le_one_div_of_le hsm hsms
    rw [hbdef]
    have : 0 ≤ 1 / (2 * Real.sqrt sm) := by positivity
    linarith
  have hT2 : opNorm (Xs M₀ s) ≤ b := by
    refine hX.trans ?_
    have h1 : Real.sqrt sm ≤ Real.sqrt s := Real.sqrt_le_sqrt hsms
    have : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt sm) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    rw [hbdef]
    have : 0 ≤ 1 / sm := by positivity
    linarith
  obtain ⟨cx1, hcx1, hqx1⟩ := pj_form_gen C.Sout C.psdOut B CSig b hC.1 (Rs M₀ s) hT1 xv
  obtain ⟨cx2, hcx2, hqx2⟩ := pj_form_gen C.Sin C.psdIn B CSig b hC.2 (Xs M₀ s) hT2 xv
  obtain ⟨cy1, hcy1, hqy1⟩ := pj_form_gen C.Sout C.psdOut B CSig b hC.1 (Rs M₀ s) hT1 yv
  obtain ⟨cy2, hcy2, hqy2⟩ := pj_form_gen C.Sin C.psdIn B CSig b hC.2 (Xs M₀ s) hT2 yv
  set KP : ℝ := 2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ)) with hKP
  have hKP0 : 0 ≤ KP := by rw [hKP]; positivity
  set Qx : ℝ := CSig * b ^ 2 * (∑ i, xv i ^ 2) / B with hQx
  set Qy : ℝ := CSig * b ^ 2 * (∑ i, yv i ^ 2) / B with hQy
  have hQx0 : 0 ≤ Qx := by rw [hQx]; positivity
  have hQy0 : 0 ≤ Qy := by rw [hQy]; positivity
  have hPm : ∫⁻ x, ENNReal.ofReal (((1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) ^ 2) ∂(gaussPair m n)
      ≤ ENNReal.ofReal KP := pj_P_moment C B γ CSig hdim hγ hC Ah hA
  have hmeasP : Measurable (fun x : Vec m × Vec n => (1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3) := by
    unfold resid momN eucNorm momU momV
    fun_prop
  have hP0 : ∀ x : Vec m × Vec n, 0 ≤ (1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3 := by
    intro x
    have : 0 ≤ momN C B x := by unfold momN; positivity
    positivity
  have h1x : Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * cx1 i) := by fun_prop
  have h2x : Measurable (fun x : Vec m × Vec n => ∑ i, x.2 i * cx2 i) := by fun_prop
  have h1y : Measurable (fun x : Vec m × Vec n => ∑ i, x.1 i * cy1 i) := by fun_prop
  have h2y : Measurable (fun x : Vec m × Vec n => ∑ i, x.2 i * cy2 i) := by fun_prop
  have m1x := pj_lin_fst_le (n := n) cx1 Qx hqx1
  have m2x := pj_lin_snd_le (m := m) cx2 Qx hqx2
  have m1y := pj_lin_fst_le (n := n) cy1 Qy hqy1
  have m2y := pj_lin_snd_le (m := m) cy2 Qy hqy2
  set PP : Vec m × Vec n → ℝ := fun x => (1 + |resid Ah x|) ^ 4 * (1 + momN C B x) ^ 3 with hPP
  have H11 := pj_holder (gaussPair m n) PP _ _ hmeasP h1x h1y hP0 KP Qx Qy hKP0 hQx0 hQy0 hPm m1x m1y
  have H12 := pj_holder (gaussPair m n) PP _ _ hmeasP h1x h2y hP0 KP Qx Qy hKP0 hQx0 hQy0 hPm m1x m2y
  have H21 := pj_holder (gaussPair m n) PP _ _ hmeasP h2x h1y hP0 KP Qx Qy hKP0 hQx0 hQy0 hPm m2x m1y
  have H22 := pj_holder (gaussPair m n) PP _ _ hmeasP h2x h2y hP0 KP Qx Qy hKP0 hQx0 hQy0 hPm m2x m2y
  have e1x : ∀ x : Vec m × Vec n, dotProduct xv (Rs M₀ s *ᵥ momU C B x) = ∑ i, x.1 i * cx1 i :=
    fun x => hcx1 x.1
  have e2x : ∀ x : Vec m × Vec n, dotProduct xv (Xs M₀ s *ᵥ momV C B x) = ∑ i, x.2 i * cx2 i :=
    fun x => hcx2 x.2
  have e1y : ∀ x : Vec m × Vec n, dotProduct yv (Rs M₀ s *ᵥ momU C B x) = ∑ i, x.1 i * cy1 i :=
    fun x => hcy1 x.1
  have e2y : ∀ x : Vec m × Vec n, dotProduct yv (Xs M₀ s *ᵥ momV C B x) = ∑ i, x.2 i * cy2 i :=
    fun x => hcy2 x.2
  have hpt : ∀ x : Vec m × Vec n, ENNReal.ofReal
      |dotProduct xv ((Rs (M₀ + (ϖ * resid Ah x) • outer (momU C B x) (momV C B x)) s - Rs M₀ s) *ᵥ yv)|
      ≤ ENNReal.ofReal (coeffConst I * ϖ) *
        (ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.1 i * cy1 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.2 i * cy2 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.1 i * cy1 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.2 i * cy2 i|))) := by
    intro x
    have h := pj_pt hI hIpos M₀ (momU C B x) (momV C B x) (resid Ah x) ϖ hϖ0 hϖ1 s hs xv yv
    rw [pj_N_eq, e1x, e2x, e1y, e2y] at h
    have hP := hP0 x
    have hcc : 0 ≤ coeffConst I * ϖ := mul_nonneg hCc0 hϖ0
    have hn : ∀ (a b : ℝ), 0 ≤ PP x * (|a| * |b|) := fun a b => by
      have := hP0 x
      simp only [hPP]
      positivity
    rw [← ENNReal.ofReal_add (hn _ _) (hn _ _), ← ENNReal.ofReal_add (by have := hn 0 0; positivity) (hn _ _),
      ← ENNReal.ofReal_add (by have := hn 0 0; positivity) (hn _ _), ← ENNReal.ofReal_mul hcc]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    simp only [hPP]
    ring
  have hmeasT : ∀ (f g : Vec m × Vec n → ℝ), Measurable f → Measurable g →
      Measurable (fun x => ENNReal.ofReal (PP x * (|f x| * |g x|))) := fun f g hf hg =>
    ENNReal.measurable_ofReal.comp (hmeasP.mul (hf.abs.mul hg.abs))
  calc ∫⁻ x : Vec m × Vec n, ENNReal.ofReal
        |dotProduct xv ((Rs (M₀ + (ϖ * resid Ah x) • outer (momU C B x) (momV C B x)) s - Rs M₀ s) *ᵥ yv)|
        ∂(gaussPair m n)
      ≤ ∫⁻ x : Vec m × Vec n, ENNReal.ofReal (coeffConst I * ϖ) *
        (ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.1 i * cy1 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.2 i * cy2 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.1 i * cy1 i|))
        + ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.2 i * cy2 i|))) ∂(gaussPair m n) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (coeffConst I * ϖ) *
        (∫⁻ x, ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.1 i * cy1 i|)) ∂(gaussPair m n)
        + ∫⁻ x, ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.2 i * cy2 i|)) ∂(gaussPair m n)
        + ∫⁻ x, ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.1 i * cy1 i|)) ∂(gaussPair m n)
        + ∫⁻ x, ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.2 i * cy2 i|)) ∂(gaussPair m n)) := by
        have t11 := hmeasT _ _ h1x h1y
        have t12 := hmeasT _ _ h1x h2y
        have t21 := hmeasT _ _ h2x h1y
        have t22 := hmeasT _ _ h2x h2y
        have tA : Measurable (fun x : Vec m × Vec n =>
            ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.1 i * cy1 i|))
            + ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.2 i * cy2 i|))) := t11.add t12
        have tB : Measurable (fun x : Vec m × Vec n =>
            ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.1 i * cy1 i|))
            + ENNReal.ofReal (PP x * (|∑ i, x.1 i * cx1 i| * |∑ i, x.2 i * cy2 i|))
            + ENNReal.ofReal (PP x * (|∑ i, x.2 i * cx2 i| * |∑ i, x.1 i * cy1 i|))) := tA.add t21
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left tB, lintegral_add_left tA, lintegral_add_left t11]
    _ ≤ ENNReal.ofReal (coeffConst I * ϖ) *
        (ENNReal.ofReal (Real.sqrt KP * Real.sqrt (3 * (Qx * Qy)))
        + ENNReal.ofReal (Real.sqrt KP * Real.sqrt (3 * (Qx * Qy)))
        + ENNReal.ofReal (Real.sqrt KP * Real.sqrt (3 * (Qx * Qy)))
        + ENNReal.ofReal (Real.sqrt KP * Real.sqrt (3 * (Qx * Qy)))) := by
        gcongr
    _ = _ := by
        have hq : 0 ≤ Real.sqrt KP * Real.sqrt (3 * (Qx * Qy)) := by positivity
        have hcc : 0 ≤ coeffConst I * ϖ := mul_nonneg hCc0 hϖ0
        rw [← ENNReal.ofReal_add hq hq, ← ENNReal.ofReal_add (by positivity) hq,
          ← ENNReal.ofReal_add (by positivity) hq, ← ENNReal.ofReal_mul hcc]
        congr 1
        ring

section PjMain

variable {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}

private lemma pj_rOut_outer_rIn (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
    rOut F.C * outer z w * rIn F.C =
      outer (Matrix.mulVec (rOut F.C) z) (Matrix.mulVec (rIn F.C) w) := by
  have hsym : (rIn F.C)ᵀ = rIn F.C := by
    have h : (CFC.sqrt F.C.Sin)ᴴ = CFC.sqrt F.C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg F.C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hv : Matrix.vecMul w (rIn F.C) = Matrix.mulVec (rIn F.C) w := by
    rw [← Matrix.vecMul_transpose, hsym]
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma pj_decomp [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (a : Fin B) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = WeightedBufDel w F S t (t + 1 - (j : ℤ)) a ω +
      (w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) a j rfl ω (hω t)
  rw [h]
  congr 1
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S (t + 1 - (j : ℤ)) a ω =
      resid F.A (S.zw (t + 1 - (j : ℤ)) a ω) •
        outer (Matrix.mulVec (rOut F.C) (S.zw (t + 1 - (j : ℤ)) a ω).1)
        (Matrix.mulVec (rIn F.C) (S.zw (t + 1 - (j : ℤ)) a ω).2) := by
    unfold sampleTerm
    rw [pj_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

private lemma pj_meas_del (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s : ℤ) (a : Fin B) : Measurable (WeightedBufDel w F S t s a) := by
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
  unfold WeightedBufDel
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact hQ.comp (S.meas _ _)

private lemma pj_inv_measurable {a : ℕ} : Measurable (fun X : Mat a a => X⁻¹) := by
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

private lemma pj_Rs_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rs M s) := by
  have hc : Continuous (fun M : Mat a b => M * Mᵀ + s • (1 : Mat a a)) := by fun_prop
  exact (pj_inv_measurable (a := a)).comp hc.measurable

end PjMain

private lemma pj_opNorm_le_of_sq {m n : ℕ} (U : Mat m n) (M : ℝ) (hM : 0 ≤ M)
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

private lemma pj_opNorm_of_bilin {a b : ℕ} (K : Mat a b) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ (x : Vec a) (y : Vec b),
      |dotProduct x (K *ᵥ y)| ≤ c * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)) :
    opNorm K ≤ c := by
  refine pj_opNorm_le_of_sq K c hc fun y => ?_
  have h1 := h (K *ᵥ y) y
  have hS : dotProduct (K *ᵥ y) (K *ᵥ y) = ∑ k, (K *ᵥ y) k ^ 2 := by
    simp [dotProduct, sq]
  rw [hS] at h1
  set S := ∑ k, (K *ᵥ y) k ^ 2 with hSdef
  set Y := ∑ i, y i ^ 2 with hYdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [abs_of_nonneg hS0] at h1
  have hr := Real.sq_sqrt hS0
  have hq := Real.sq_sqrt hY0
  have hr0 := Real.sqrt_nonneg S
  have hq0 := Real.sqrt_nonneg Y
  have key : Real.sqrt S ≤ c * Real.sqrt Y := by
    by_contra hcon
    push Not at hcon
    have hpos : 0 < Real.sqrt S := lt_of_le_of_lt (by positivity) hcon
    nlinarith [mul_pos hpos (sub_pos.2 hcon)]
  calc S = Real.sqrt S ^ 2 := hr.symm
    _ ≤ (c * Real.sqrt Y) ^ 2 := pow_le_pow_left₀ hr0 key 2
    _ = c ^ 2 * Y := by rw [mul_pow, hq]

private lemma pj_main_lint {I : Set ℝ} (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) {Ω' : Type} [MeasurableSpace Ω']
    (P : Measure Ω') [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig)
    (sm : ℝ) (hsm : 0 < sm) (j : ℕ) (a : Fin B) (s : ℝ) (hs : s ∈ I) (hsms : sm ≤ s)
    (xv yv : Vec m) :
    ∫⁻ ω, ENNReal.ofReal |dotProduct xv ((Rs (WeightedBuf w F S t ω) s
        - Rs (WeightedBufDel w F S t (t + 1 - (j : ℤ)) a ω) s) *ᵥ yv)| ∂P
      ≤ ENNReal.ofReal (coeffConst I * w j * (4 * (Real.sqrt (2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ))) *
          Real.sqrt (3 * ((CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, xv i ^ 2) / B) *
            (CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, yv i ^ 2) / B)))))) := by
  set s' : ℤ := t + 1 - (j : ℤ) with hs'
  have hM0 : Measurable (WeightedBufDel w F S t s' a) := pj_meas_del w F S t s' a
  have hX : Measurable (S.zw s' a) := S.meas _ _
  have hind := weightedBufDel_indep w F S t s' a
  have hmap : P.map (fun ω => (WeightedBufDel w F S t s' a ω, S.zw s' a ω))
      = (P.map (WeightedBufDel w F S t s' a)).prod (gaussPair m n) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hM0.aemeasurable hX.aemeasurable).1 hind]
    congr 1
    exact S.law _ _
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  haveI : MeasurableSub₂ (Mat m m) := inferInstanceAs (MeasurableSub₂ (Fin m → Fin m → ℝ))
  set G : Mat m n × (Vec m × Vec n) → ℝ := fun p =>
    |dotProduct xv ((Rs (p.1 + (w j * resid F.A p.2) • outer (momU F.C B p.2) (momV F.C B p.2)) s
      - Rs p.1 s) *ᵥ yv)| with hG
  have hh : Continuous (fun x : Vec m × Vec n =>
      (w j * resid F.A x) • outer (momU F.C B x) (momV F.C B x)) := by
    refine continuous_pi fun i => continuous_pi fun k => ?_
    simp only [Matrix.smul_apply, smul_eq_mul, outer, Matrix.vecMulVec_apply, momU, momV, resid,
      Pi.smul_apply, dotProduct, Matrix.mulVec]
    fun_prop
  have hfin : Continuous (fun Δ : Mat m m => |dotProduct xv (Δ *ᵥ yv)|) := by
    unfold dotProduct Matrix.mulVec
    fun_prop
  have hGm : Measurable (fun p : Mat m n × (Vec m × Vec n) => ENNReal.ofReal (G p)) := by
    refine ENNReal.measurable_ofReal.comp ?_
    have h1 : Measurable (fun p : Mat m n × (Vec m × Vec n) =>
        p.1 + (w j * resid F.A p.2) • outer (momU F.C B p.2) (momV F.C B p.2)) :=
      measurable_fst.add (hh.measurable.comp measurable_snd)
    have h2 := ((pj_Rs_measurable (a := m) (b := n) s).comp h1).sub
      ((pj_Rs_measurable (a := m) (b := n) s).comp measurable_fst)
    exact hfin.measurable.comp h2
  have hpair : Measurable (fun ω => (WeightedBufDel w F S t s' a ω, S.zw s' a ω)) :=
    hM0.prodMk hX
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  calc ∫⁻ ω, ENNReal.ofReal |dotProduct xv ((Rs (WeightedBuf w F S t ω) s
        - Rs (WeightedBufDel w F S t s' a ω) s) *ᵥ yv)| ∂P
      = ∫⁻ ω, ENNReal.ofReal (G (WeightedBufDel w F S t s' a ω, S.zw s' a ω)) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [pj_decomp w hw F S t j a] with ω hω
        rw [hω]
    _ = ∫⁻ p, ENNReal.ofReal (G p) ∂(P.map (fun ω => (WeightedBufDel w F S t s' a ω, S.zw s' a ω))) :=
        (lintegral_map hGm hpair).symm
    _ = ∫⁻ p, ENNReal.ofReal (G p) ∂((P.map (WeightedBufDel w F S t s' a)).prod (gaussPair m n)) := by
        rw [hmap]
    _ = ∫⁻ m0, ∫⁻ x, ENNReal.ofReal (G (m0, x)) ∂(gaussPair m n)
          ∂(P.map (WeightedBufDel w F S t s' a)) := lintegral_prod _ hGm.aemeasurable
    _ ≤ ∫⁻ m0, ENNReal.ofReal (coeffConst I * w j * (4 * (Real.sqrt (2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ))) *
          Real.sqrt (3 * ((CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, xv i ^ 2) / B) *
            (CSig * (1 / sm + 1 / (2 * Real.sqrt sm)) ^ 2 * (∑ i, yv i ^ 2) / B))))))
          ∂(P.map (WeightedBufDel w F S t s' a)) := by
        refine lintegral_mono fun m0 => ?_
        exact pj_inner hI hIpos F.C B F.hB γ CSig hdim hγ hC F.A F.hA sm hsm (w j) hw0 hw1 s hs hsms
          m0 xv yv
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

open scoped Matrix.Norms.L2Operator in
private lemma pj_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

private lemma pj_meas_WB {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
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

private lemma pj_int_Rs {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (K : Ω' → Mat m n) (hK : Measurable K) (s : ℝ) (hs : 0 < s) (i k : Fin m) :
    Integrable (fun ω => Rs (K ω) s i k) P := by
  refine Integrable.of_bound (C := 1 / s)
    (((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      ((pj_Rs_measurable s).comp hK))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  exact (pj_abs_entry_le_opNorm _ i k).trans (lem_app_de_resolvent (K ω) s hs).1

private lemma pj_bilin_int {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m : ℕ} (D : Ω' → Mat m m) (hint : ∀ i k, Integrable (fun ω => D ω i k) P) (xv yv : Vec m) :
    dotProduct xv ((Matrix.of fun i k => ∫ ω, D ω i k ∂P) *ᵥ yv)
      = ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P := by
  have hin : ∀ i, Integrable (fun ω => xv i * ∑ k, D ω i k * yv k) P := fun i =>
    ((integrable_finsetSum _ fun k _ => (hint i k).mul_const (yv k))).const_mul (xv i)
  have h1 : ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P = ∑ i, ∫ ω, xv i * ∑ k, D ω i k * yv k ∂P := by
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct]
    exact integral_finsetSum _ fun i _ => hin i
  rw [h1]
  unfold dotProduct Matrix.mulVec
  simp only [Matrix.of_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun k _ => (hint i k).mul_const (yv k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (integral_mul_const (yv k) _).symm


/-- `eqn:app-de-Pj-P`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1655–1657):
\begin{equation}\label{eqn:app-de-Pj-P}
\norm{\mathcal P(s)-\mathcal P_j(s)}\le\frac{C_I\,\emaw j}{B}.
\end{equation}
-/
theorem eqn_app_de_Pj_P (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (CSig γ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (m n B : ℕ) (w : ℕ → ℝ), WeightClass w →
      ∀ (Ω' : Type) [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
        (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
        opNorm F.C.Sout ≤ CSig → opNorm F.C.Sin ≤ CSig →
        (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
        ∀ (j : ℕ) (a : Fin B), ∀ s ∈ I,
          opNorm (expRes w F S t s - expDelRes w F S t j a s) ≤ C * w j / B := by
  refine ⟨4 * coeffConst I * Real.sqrt (2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ))) * Real.sqrt 3 * max CSig 0 *
          (1 / sInf I + 1 / (2 * Real.sqrt (sInf I))) ^ 2, ?_, ?_⟩
  · have : 0 ≤ coeffConst I := by unfold coeffConst; positivity
    positivity
  intro m n B w hw Ω' _ P _ F S t hCo hCi hm hn j a s hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hs0 : 0 < s := hIpos hs
  have hsmI : sInf I ∈ I := hI.sInf_mem ⟨s, hs⟩
  have hsm : 0 < sInf I := hIpos hsmI
  have hsms : sInf I ≤ s := csInf_le hI.bddBelow hs
  have hCs : 0 ≤ CSig := le_trans (pj_opNorm_nonneg _) hCo
  have hγ : 0 ≤ γ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hBr
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hw0 : 0 ≤ w j := hw.1.1 j
  set sm := sInf I with hsmdef
  set s' : ℤ := t + 1 - (j : ℤ) with hs'
  set b : ℝ := 1 / sm + 1 / (2 * Real.sqrt sm) with hbdef
  set KP : ℝ := 2 ^ 14 * (2 + ((Nat.doubleFactorial 13 : ℕ) : ℝ) ^ 2
          + (2 * CSig * γ) ^ 14 * ((Nat.doubleFactorial 27 : ℕ) : ℝ)) with hKP
  have hKP0 : 0 ≤ KP := by rw [hKP]; positivity
  have hCc0 : 0 ≤ coeffConst I := by unfold coeffConst; positivity
  have hWB := pj_meas_WB w F S t
  have hM0 := pj_meas_del w F S t s' a
  haveI : MeasurableSub₂ (Mat m m) := inferInstanceAs (MeasurableSub₂ (Fin m → Fin m → ℝ))
  set D : Ω' → Mat m m := fun ω => Rs (WeightedBuf w F S t ω) s - Rs (WeightedBufDel w F S t s' a ω) s
    with hD
  have hDm : Measurable D := ((pj_Rs_measurable s).comp hWB).sub ((pj_Rs_measurable s).comp hM0)
  have hDint : ∀ i k, Integrable (fun ω => D ω i k) P := fun i k => by
    exact (pj_int_Rs P _ hWB s hs0 i k).sub (pj_int_Rs P _ hM0 s hs0 i k)
  have hE : expRes w F S t s - expDelRes w F S t j a s = Matrix.of fun i k => ∫ ω, D ω i k ∂P := by
    ext i k
    simp only [expRes, expDelRes, Muon.mean, Matrix.sub_apply, Matrix.of_apply, hD]
    rw [integral_sub (pj_int_Rs P _ hWB s hs0 i k) (pj_int_Rs P _ hM0 s hs0 i k)]
  rw [hE]
  refine pj_opNorm_of_bilin _ _ (by positivity) fun xv yv => ?_
  rw [pj_bilin_int P D hDint xv yv]
  have hlint := pj_main_lint hI hIpos w hw P F S t γ CSig ⟨hm, hn⟩ hγ ⟨hCo, hCi⟩ sm hsm j a s hs hsms xv yv
  set nx := ∑ i, xv i ^ 2 with hnx
  set ny := ∑ i, yv i ^ 2 with hny
  have hnx0 : 0 ≤ nx := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hny0 : 0 ≤ ny := Finset.sum_nonneg fun i _ => sq_nonneg _
  set κ : ℝ := CSig * b ^ 2 / B with hκ
  have hκ0 : 0 ≤ κ := by rw [hκ]; positivity
  have hsq : Real.sqrt (3 * ((CSig * b ^ 2 * nx / B) * (CSig * b ^ 2 * ny / B)))
      = Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny) := by
    have e : 3 * ((CSig * b ^ 2 * nx / B) * (CSig * b ^ 2 * ny / B))
        = (Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny)) ^ 2 := by
      have h3 := Real.sq_sqrt (show (0:ℝ) ≤ 3 by norm_num)
      have h4 := Real.sq_sqrt hnx0
      have h5 := Real.sq_sqrt hny0
      calc 3 * ((CSig * b ^ 2 * nx / B) * (CSig * b ^ 2 * ny / B))
          = (Real.sqrt 3) ^ 2 * κ ^ 2 * ((Real.sqrt nx) ^ 2 * (Real.sqrt ny) ^ 2) := by
            rw [h3, h4, h5, hκ]; ring
        _ = _ := by ring
    rw [e, Real.sqrt_sq (by positivity)]
  rw [hsq] at hlint
  have hBound0 : 0 ≤ coeffConst I * w j * (4 * (Real.sqrt KP * (Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny)))) := by
    positivity
  have hcalc : coeffConst I * w j * (4 * (Real.sqrt KP * (Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny))))
      = (4 * coeffConst I * Real.sqrt KP * Real.sqrt 3 * max CSig 0 * b ^ 2) * w j / B *
        Real.sqrt nx * Real.sqrt ny := by
    rw [max_eq_left hCs, hκ]
    field_simp
  calc |∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P|
      ≤ ∫ ω, |dotProduct xv (D ω *ᵥ yv)| ∂P := abs_integral_le_integral_abs
    _ = (∫⁻ ω, ENNReal.ofReal |dotProduct xv (D ω *ᵥ yv)| ∂P).toReal := by
        refine integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => abs_nonneg _) ?_
        have hfin : Continuous (fun Δ : Mat m m => |dotProduct xv (Δ *ᵥ yv)|) := by
          unfold dotProduct Matrix.mulVec
          fun_prop
        exact (hfin.measurable.comp hDm).aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (coeffConst I * w j * (4 * (Real.sqrt KP * (Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny)))))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint
    _ = coeffConst I * w j * (4 * (Real.sqrt KP * (Real.sqrt 3 * κ * (Real.sqrt nx * Real.sqrt ny)))) :=
        ENNReal.toReal_ofReal hBound0
    _ = _ := by
        rw [hcalc]

/-! ### Private helpers for `thm_app_de_gram` (Step 5 reduction, Step 4 glue) -/

private lemma gr_shift_posdef {m : ℕ} (S : Mat m m) (hS : S.PosSemidef) {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) : (s • (1 : Mat m m) + a • S).PosDef :=
  Matrix.PosDef.add_posSemidef (Matrix.PosDef.one.smul hs) (hS.smul ha)

private lemma gr_inv_opNorm {m : ℕ} (S : Mat m m) (hS : S.PosSemidef) {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) : opNorm ((s • (1 : Mat m m) + a • S)⁻¹) ≤ 1 / s := by
  set A : Mat m m := s • (1 : Mat m m) + a • S with hAdef
  have hA : A.PosDef := gr_shift_posdef S hS hs ha
  have hU : IsUnit A := hA.isUnit
  refine pj_opNorm_le_of_sq _ _ (by positivity) fun x => ?_
  set y : Fin m → ℝ := A⁻¹ *ᵥ x with hy
  have hAy : A *ᵥ y = x := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det A).1 hU),
      Matrix.one_mulVec]
  have hq : dotProduct y (A *ᵥ y) = s * dotProduct y y + a * dotProduct y (S *ᵥ y) := by
    rw [hAdef, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp
  have hSy : 0 ≤ dotProduct y (S *ᵥ y) := by
    have := hS.dotProduct_mulVec_nonneg y
    simpa [star_trivial] using this
  have hyy : 0 ≤ dotProduct y y := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (y i)]
  rw [hAy] at hq
  have h1 : s * dotProduct y y ≤ dotProduct y x := by nlinarith [mul_nonneg ha hSy]
  have hcs : (dotProduct y x) ^ 2 ≤ dotProduct y y * dotProduct x x := by
    simp only [dotProduct]
    simpa [sq] using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ y x
  have hyS : ∑ k, y k ^ 2 = dotProduct y y := by simp [dotProduct, sq]
  have hxS : ∑ k, x k ^ 2 = dotProduct x x := by simp [dotProduct, sq]
  rw [hyS, hxS]
  set Y := dotProduct y y
  set X := dotProduct x x
  have hX : 0 ≤ X := by
    simp only [X, dotProduct]; exact Finset.sum_nonneg fun i _ => by nlinarith [sq_nonneg (x i)]
  rcases hyy.eq_or_lt with h0 | hpos
  · rw [← h0]; positivity
  · have h2 : (s * Y) ^ 2 ≤ Y * X := by
      have h3 : 0 ≤ s * Y := by positivity
      calc (s * Y) ^ 2 ≤ (dotProduct y x) ^ 2 := pow_le_pow_left₀ h3 h1 2
        _ ≤ Y * X := hcs
    have h4 : s ^ 2 * Y ≤ X := by
      have : Y * (s ^ 2 * Y) ≤ Y * X := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    rw [div_pow, one_pow, one_div, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    linarith

open scoped Matrix.Norms.L2Operator in
private lemma gr_opNorm_mul {p q r : ℕ} (K : Mat p q) (L : Mat q r) :
    opNorm (K * L) ≤ opNorm K * opNorm L := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul K L

open scoped Matrix.Norms.L2Operator in
private lemma gr_opNorm_add {p q : ℕ} (K L : Mat p q) :
    opNorm (K + L) ≤ opNorm K + opNorm L := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_add_le K L

open scoped Matrix.Norms.L2Operator in
private lemma gr_opNorm_smul {p q : ℕ} (c : ℝ) (K : Mat p q) :
    opNorm (c • K) = |c| * opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

open scoped Matrix.Norms.L2Operator in
private lemma gr_opNorm_neg {p q : ℕ} (K : Mat p q) : opNorm (-K) = opNorm K := by
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_neg]

private lemma gr_P_approx {m : ℕ} (S P : Mat m m) (hS : S.PosSemidef) {s a : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) :
    opNorm (P - (s • (1 : Mat m m) + a • S)⁻¹) ≤
      opNorm ((1 : Mat m m) - s • P - a • (P * S)) / s := by
  set A : Mat m m := s • (1 : Mat m m) + a • S with hAdef
  have hA : A.PosDef := gr_shift_posdef S hS hs ha
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  set E : Mat m m := (1 : Mat m m) - s • P - a • (P * S) with hE
  have hPA : P * A = 1 - E := by
    rw [hE, hAdef, Matrix.mul_add, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one]
    abel
  have key : P - A⁻¹ = -(E * A⁻¹) := by
    have : P = P * (A * A⁻¹) := by rw [hAA, Matrix.mul_one]
    calc P - A⁻¹ = P * (A * A⁻¹) - A⁻¹ := by rw [← this]
      _ = (P * A) * A⁻¹ - A⁻¹ := by rw [Matrix.mul_assoc]
      _ = -(E * A⁻¹) := by rw [hPA, Matrix.sub_mul, Matrix.one_mul]; abel
  rw [key, gr_opNorm_neg]
  calc opNorm (E * A⁻¹) ≤ opNorm E * opNorm A⁻¹ := gr_opNorm_mul _ _
    _ ≤ opNorm E * (1 / s) :=
        mul_le_mul_of_nonneg_left (gr_inv_opNorm S hS hs ha) (pj_opNorm_nonneg _)
    _ = opNorm E / s := by ring

private lemma gr_inv_diff {m : ℕ} (S : Mat m m) (hS : S.PosSemidef) {s a b : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hb : 0 ≤ b) :
    opNorm ((s • (1 : Mat m m) + a • S)⁻¹ - (s • (1 : Mat m m) + b • S)⁻¹) ≤
      opNorm S * |a - b| / s ^ 2 := by
  set A : Mat m m := s • (1 : Mat m m) + a • S with hAdef
  set A' : Mat m m := s • (1 : Mat m m) + b • S with hA'def
  have hdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 (gr_shift_posdef S hS hs ha).isUnit
  have hdet' : IsUnit A'.det :=
    (Matrix.isUnit_iff_isUnit_det A').1 (gr_shift_posdef S hS hs hb).isUnit
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hAA' : A'⁻¹ * A' = 1 := Matrix.nonsing_inv_mul _ hdet'
  have hAA'' : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hdet
  have key : A⁻¹ - A'⁻¹ = (b - a) • (A⁻¹ * S * A'⁻¹) := by
    have h1 : A' - A = (b - a) • S := by
      rw [hAdef, hA'def]; module
    calc A⁻¹ - A'⁻¹ = A⁻¹ * (A' - A) * A'⁻¹ := by
          rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc A⁻¹ A' A'⁻¹, Matrix.mul_nonsing_inv _ hdet',
            Matrix.mul_one, hAA'', Matrix.one_mul]
      _ = (b - a) • (A⁻¹ * S * A'⁻¹) := by
          rw [h1, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  rw [key, gr_opNorm_smul]
  have h1 := gr_inv_opNorm S hS hs ha
  have h2 := gr_inv_opNorm S hS hs hb
  have h3 : opNorm (A⁻¹ * S * A'⁻¹) ≤ (1 / s) * opNorm S * (1 / s) :=
    (gr_opNorm_mul _ _).trans (mul_le_mul
      ((gr_opNorm_mul _ _).trans (mul_le_mul_of_nonneg_right h1 (pj_opNorm_nonneg _))) h2
      (pj_opNorm_nonneg _) (mul_nonneg (by positivity) (pj_opNorm_nonneg _)))
  calc |b - a| * opNorm (A⁻¹ * S * A'⁻¹) ≤ |b - a| * ((1 / s) * opNorm S * (1 / s)) :=
        mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    _ = opNorm S * |a - b| / s ^ 2 := by
        rw [abs_sub_comm]; field_simp

private lemma gr_abs_trace {m : ℕ} (K : Mat m m) : |K.trace| ≤ m * opNorm K := by
  calc |K.trace| ≤ ∑ i, |K i i| := by
        simpa [Matrix.trace] using Finset.abs_sum_le_sum_abs (fun i => K i i) Finset.univ
    _ ≤ ∑ _i : Fin m, opNorm K := Finset.sum_le_sum fun i _ => pj_abs_entry_le_opNorm K i i
    _ = m * opNorm K := by simp

open scoped Matrix.Norms.L2Operator in
private lemma gr_opNorm_sub {p q : ℕ} (K L : Mat p q) :
    opNorm (K - L) ≤ opNorm K + opNorm L := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact norm_sub_le K L

private lemma gr_side {m : ℕ} (S P : Mat m m) (hS : S.PosSemidef) {s a b ε : ℝ} (hs : 0 < s)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hE : opNorm ((1 : Mat m m) - s • P - a • (P * S)) ≤ ε) :
    opNorm (P - (s • (1 : Mat m m) + b • S)⁻¹) ≤ ε / s + opNorm S * |a - b| / s ^ 2 := by
  have h1 := gr_P_approx S P hS hs ha
  have h2 := gr_inv_diff S hS hs ha hb
  have h3 : P - (s • (1 : Mat m m) + b • S)⁻¹ =
      (P - (s • (1 : Mat m m) + a • S)⁻¹) +
        ((s • (1 : Mat m m) + a • S)⁻¹ - (s • (1 : Mat m m) + b • S)⁻¹) := by abel
  rw [h3]
  have h4 : opNorm ((1 : Mat m m) - s • P - a • (P * S)) / s ≤ ε / s :=
    div_le_div_of_nonneg_right hE hs.le
  linarith [gr_opNorm_add (P - (s • (1 : Mat m m) + a • S)⁻¹)
    ((s • (1 : Mat m m) + a • S)⁻¹ - (s • (1 : Mat m m) + b • S)⁻¹)]

private lemma gr_resid {m B : ℕ} (S P : Mat m m) (hS : S.PosSemidef) (hB : 0 < (B : ℝ))
    {s a CS γ ε : ℝ} (hs : 0 < s) (ha : 0 ≤ a) (hCS : opNorm S ≤ CS) (hm : (m : ℝ) ≤ γ * B)
    (hE : opNorm ((1 : Mat m m) - s • P - a • (P * S)) ≤ ε) :
    |(B : ℝ)⁻¹ * (S * P).trace - (B : ℝ)⁻¹ * (S * (a • S + s • (1 : Mat m m))⁻¹).trace| ≤
      γ * CS * ε / s := by
  have hε : 0 ≤ ε := (pj_opNorm_nonneg _).trans hE
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCS
  have hγ : 0 ≤ γ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_neg_of_pos hneg hB
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hadd : a • S + s • (1 : Mat m m) = s • (1 : Mat m m) + a • S := add_comm _ _
  rw [hadd, ← mul_sub, ← Matrix.trace_sub, ← Matrix.mul_sub, abs_mul, abs_of_pos (inv_pos.2 hB)]
  have h1 := gr_P_approx S P hS hs ha
  have h2 : opNorm (S * (P - (s • (1 : Mat m m) + a • S)⁻¹)) ≤ CS * (ε / s) :=
    (gr_opNorm_mul _ _).trans (mul_le_mul hCS (h1.trans (div_le_div_of_nonneg_right hE hs.le))
      (pj_opNorm_nonneg _) hCS0)
  have h3 := gr_abs_trace (S * (P - (s • (1 : Mat m m) + a • S)⁻¹))
  calc (B : ℝ)⁻¹ * |(S * (P - (s • (1 : Mat m m) + a • S)⁻¹)).trace|
      ≤ (B : ℝ)⁻¹ * (m * (CS * (ε / s))) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)))
          (inv_nonneg.2 hB.le)
    _ ≤ (B : ℝ)⁻¹ * ((γ * B) * (CS * (ε / s))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hm (by positivity))
          (inv_nonneg.2 hB.le)
    _ = γ * CS * ε / s := by field_simp

open scoped Matrix.Norms.L2Operator in
private lemma gr_glue {m : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (P : Mat m m) (Pj : ℕ → Mat m m)
    (S : Mat m m) {s τ q CS Cj Bv Γ : ℝ} (hs : 0 < s) (hτ0 : 0 ≤ τ) (hsτ : s * τ ≤ Γ)
    (hq : 0 ≤ q) (hCS : opNorm S ≤ CS) (hCj : 0 ≤ Cj) (hBv : 0 < Bv)
    (hPj : ∀ j, opNorm (P - Pj j) ≤ Cj * w j / Bv) :
    opNorm ((1 : Mat m m) - s • P - (s * τ * Fw w q) • (P * S)) ≤
      opNorm ((1 : Mat m m) - s • P - ∑' j, (s * w j ^ 2 * τ * J (w j ^ 2 * q)) • (Pj j * S)) +
        Γ * CS * Cj / Bv := by
  obtain ⟨⟨hw0, hwsum, -⟩, hw1, hwtot⟩ := hw
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCS
  have hsτ0 : 0 ≤ s * τ := by positivity
  have hw2 : Summable fun j => w j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by nlinarith [hw0 j, hw1 j]) hwsum
  have hw3 : Summable fun j => w j ^ 3 :=
    Summable.of_nonneg_of_le (fun j => pow_nonneg (hw0 j) 3)
      (fun j => by nlinarith [hw0 j, hw1 j, sq_nonneg (w j)]) hwsum
  set c : ℕ → ℝ := fun j => s * w j ^ 2 * τ * J (w j ^ 2 * q) with hc
  have hJ0 : ∀ j, 0 < J (w j ^ 2 * q) := fun j =>
    (lem_app_de_scalar_i.2.2.1 _ (by positivity)).1
  have hJ1 : ∀ j, J (w j ^ 2 * q) ≤ 1 := fun j =>
    (lem_app_de_scalar_i.2.2.1 _ (by positivity)).2
  have hc0 : ∀ j, 0 ≤ c j := fun j => by have := hJ0 j; positivity
  have hcle : ∀ j, c j ≤ s * τ * w j ^ 2 := fun j => by
    calc c j = (s * τ * w j ^ 2) * J (w j ^ 2 * q) := by rw [hc]; ring
      _ ≤ (s * τ * w j ^ 2) * 1 := mul_le_mul_of_nonneg_left (hJ1 j) (by positivity)
      _ = _ := mul_one _
  have hcs : Summable c :=
    Summable.of_nonneg_of_le hc0 hcle ((hw2.mul_left (s * τ)))
  have hFw : s * τ * Fw w q = ∑' j, c j := by
    unfold Fw
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [hc]; ring
  set D : ℕ → Mat m m := fun j => c j • ((Pj j - P) * S) with hD
  have hDn : ∀ j, ‖D j‖ ≤ s * τ * (Cj * CS / Bv) * w j ^ 3 := by
    intro j
    rw [hD, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hc0 j), ← opNorm_eq_norm]
    have h1 : opNorm ((Pj j - P) * S) ≤ (Cj * w j / Bv) * CS := by
      refine (gr_opNorm_mul _ _).trans (mul_le_mul ?_ hCS (pj_opNorm_nonneg _) (by
        have := hw0 j; positivity))
      have := hPj j
      rwa [← neg_sub, gr_opNorm_neg] at this
    calc c j * opNorm ((Pj j - P) * S) ≤ (s * τ * w j ^ 2) * ((Cj * w j / Bv) * CS) :=
          mul_le_mul (hcle j) h1 (pj_opNorm_nonneg _) (by positivity)
      _ = s * τ * (Cj * CS / Bv) * w j ^ 3 := by ring
  have hDs : Summable D :=
    Summable.of_norm_bounded (hw3.mul_left (s * τ * (Cj * CS / Bv))) hDn
  have hY : HasSum (fun j => c j • (P * S)) ((∑' j, c j) • (P * S)) := hcs.hasSum.smul_const _
  have hX : HasSum (fun j => c j • (Pj j * S)) ((∑' j, c j) • (P * S) + ∑' j, D j) := by
    have e : (fun j => c j • (Pj j * S)) = fun j => c j • (P * S) + D j := by
      funext j
      simp only [hD]
      rw [Matrix.sub_mul, smul_sub]
      abel
    rw [e]
    exact hY.add hDs.hasSum
  have hQ : (1 : Mat m m) - s • P - ∑' j, c j • (Pj j * S) =
      (1 : Mat m m) - s • P - (s * τ * Fw w q) • (P * S) - ∑' j, D j := by
    rw [hX.tsum_eq, hFw]; abel
  have hE : (1 : Mat m m) - s • P - (s * τ * Fw w q) • (P * S) =
      ((1 : Mat m m) - s • P - ∑' j, c j • (Pj j * S)) + ∑' j, D j := by
    rw [hQ]; abel
  rw [hE]
  refine (gr_opNorm_add _ _).trans (add_le_add le_rfl ?_)
  rw [opNorm_eq_norm]
  have hK0 : 0 ≤ s * τ * (Cj * CS / Bv) := by positivity
  calc ‖∑' j, D j‖ ≤ ∑' j, ‖D j‖ := norm_tsum_le_tsum_norm hDs.norm
    _ ≤ ∑' j, s * τ * (Cj * CS / Bv) * w j ^ 3 :=
        Summable.tsum_le_tsum hDn hDs.norm (hw3.mul_left _)
    _ = s * τ * (Cj * CS / Bv) * ∑' j, w j ^ 3 := tsum_mul_left
    _ ≤ s * τ * (Cj * CS / Bv) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ hK0
        calc ∑' j, w j ^ 3 ≤ ∑' j, w j :=
              Summable.tsum_le_tsum (fun j => by nlinarith [hw0 j, hw1 j, sq_nonneg (w j)]) hw3 hwsum
          _ ≤ 1 := hwtot
    _ ≤ Γ * CS * Cj / Bv := by
        rw [mul_one]
        calc s * τ * (Cj * CS / Bv) ≤ Γ * (Cj * CS / Bv) :=
              mul_le_mul_of_nonneg_right hsτ (by positivity)
          _ = Γ * CS * Cj / Bv := by ring

private lemma gram_reduce (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (hIII : ∀ 𝔟 : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ ν ν' : FiniteMeasure ℝ,
      (ν, ν') ∈ classK R.CSig (max R.γstar 1) →
      ∀ s ∈ I, ∀ u v a c : ℝ, u ∈ Icc 0 𝔟 → v ∈ Icc 0 𝔟 → a ∈ Icc 0 𝔟 → c ∈ Icc 0 𝔟 →
        |u - ∫ t, t / (s + a * t) ∂(ν : Measure ℝ)| ≤ δ →
        |v - ∫ t, t / (s + c * t) ∂(ν' : Measure ℝ)| ≤ δ →
        |a - s * v * Fw w (s * u * v)| ≤ δ →
        |c - s * u * Fw w (s * u * v)| ≤ δ →
        |u - (branchSol (Fw w) ν ν' s).1| + |v - (branchSol (Fw w) ν ν' s).2.1| +
          |a - (branchSol (Fw w) ν ν' s).2.2.1| + |c - (branchSol (Fw w) ν ν' s).2.2.2| ≤ ε)
    (hEo : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - (s * sigmaTildeB w (R.F k) (S k) t s * Fw w (qB w (R.F k) (S k) t s)) •
          (expRes w (R.F k) (S k) t s * (R.F k).C.Sout)) ≤ ε)
    (hEi : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.n k) (R.n k)) - s • expResT w (R.F k) (S k) t s
        - (s * sigmaB w (R.F k) (S k) t s * Fw w (qB w (R.F k) (S k) t s)) •
          (expResT w (R.F k) (S k) t s * (R.F k).C.Sin)) ≤ ε) :
    Tendsto (fun k => ⨆ s ∈ I,
      (opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)))
      atTop (𝓝 0) := by
  classical
  have hF : AdmissibleWeightFn (Fw w) := Fw_admissible hw.1
  set γ' : ℝ := max R.γstar 1 with hγ'
  have hγ'0 : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCs : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  have hK : ∀ k, (νo k, νi k) ∈ classK R.CSig γ' := by
    intro k
    obtain ⟨o1, o2⟩ := assum_app_setup_regime_nuOut R k
    obtain ⟨i1, i2⟩ := assum_app_setup_regime_nuIn R k
    have hle : ENNReal.ofReal R.γstar ≤ ENNReal.ofReal γ' :=
      ENNReal.ofReal_le_ofReal (le_max_left _ _)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [hνo k]; exact (measure_mono (Set.subset_univ _)).trans (o2.trans hle)
    · rw [hνo k]; exact o1
    · rw [hνi k]; exact (measure_mono (Set.subset_univ _)).trans (i2.trans hle)
    · rw [hνi k]; exact i1
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  set 𝔟 : ℝ := R.CSig * γ' / sm + R.CSig * γ' * Fw w 0 with h𝔟
  have hF0 : 0 < Fw w 0 := hF.pos 0 le_rfl
  have h𝔟1 : 0 ≤ R.CSig * γ' / sm := by positivity
  have h𝔟2 : 0 ≤ R.CSig * γ' * Fw w 0 := by positivity
  -- pointwise inputs
  have hq : ∀ k, ∀ s ∈ I, 0 ≤ sigmaB w (R.F k) (S k) t s ∧
      sigmaB w (R.F k) (S k) t s ≤ R.CSig * γ' / s ∧
      0 ≤ sigmaTildeB w (R.F k) (S k) t s ∧
      sigmaTildeB w (R.F k) (S k) t s ≤ R.CSig * γ' / s ∧
      0 ≤ qB w (R.F k) (S k) t s ∧ qB w (R.F k) (S k) t s ≤ (R.CSig * γ') ^ 2 / sm := by
    intro k s hs
    refine eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
      ⟨R.normOut k, R.normIn k⟩ ⟨?_, ?_⟩ s hs
    · exact (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
    · exact (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hBpos : ∀ k, (0 : ℝ) < (R.B k : ℝ) := fun k => by exact_mod_cast (R.F k).hB
  -- Rbar coefficients are nonnegative
  have hbs : ∀ k, ∀ s ∈ I, 0 ≤ (branchSol (Fw w) (νo k) (νi k) s).2.2.1 ∧
      0 ≤ (branchSol (Fw w) (νo k) (νi k) s).2.2.2 := by
    intro k s hs
    have h := branchSol_spec hF hCs hγ'0 (hK k) (hIpos hs)
    generalize branchSol (Fw w) (νo k) (νi k) s = x at h ⊢
    obtain ⟨σ, σ', a, c⟩ := x
    obtain ⟨-, -, h3, h4, -⟩ := h
    exact ⟨h3, h4⟩
  have hmain : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      (opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)) ≤ ε := by
    intro ε hε
    have hε1 : 0 < ε * sm ^ 2 / (4 * R.CSig) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := hIII 𝔟 (ε * sm ^ 2 / (4 * R.CSig)) hε1
    have hε2 : 0 < min (δ * sm / (γ' * R.CSig)) (ε * sm / 4) :=
      lt_min (by positivity) (by positivity)
    set ε₂ := min (δ * sm / (γ' * R.CSig)) (ε * sm / 4) with hε₂def
    have hε2a : ε₂ ≤ δ * sm / (γ' * R.CSig) := min_le_left _ _
    have hε2b : ε₂ ≤ ε * sm / 4 := min_le_right _ _
    filter_upwards [hEo ε₂ hε2, hEi ε₂ hε2] with k hEok hEik s hs
    have hEok := hEok s hs
    have hEik := hEik s hs
    have hs0 : 0 < s := hIpos hs
    have hsms : sm ≤ s := hsmI s hs
    obtain ⟨hu0, hu1, hv0, hv1, hq0, hq1⟩ := hq k s hs
    obtain ⟨hb1, hb2⟩ := hbs k s hs
    set u := sigmaB w (R.F k) (S k) t s with hu
    set v := sigmaTildeB w (R.F k) (S k) t s with hv
    have hqB : qB w (R.F k) (S k) t s = s * u * v := rfl
    have hFq0 : 0 < Fw w (s * u * v) := by rw [← hqB]; exact hF.pos _ hq0
    have hFqle : Fw w (s * u * v) ≤ Fw w 0 := by rw [← hqB]; exact hF.le_zero _ hq0
    rw [hqB] at hEok hEik
    set a := s * v * Fw w (s * u * v) with ha
    set c := s * u * Fw w (s * u * v) with hc
    have ha0 : 0 ≤ a := by positivity
    have hc0 : 0 ≤ c := by positivity
    have hCsγ : 0 ≤ R.CSig * γ' := by positivity
    have hu2 : u ≤ 𝔟 := by
      have : R.CSig * γ' / s ≤ R.CSig * γ' / sm :=
        div_le_div_of_nonneg_left hCsγ hsm hsms
      linarith
    have hv2 : v ≤ 𝔟 := by
      have : R.CSig * γ' / s ≤ R.CSig * γ' / sm :=
        div_le_div_of_nonneg_left hCsγ hsm hsms
      linarith
    have ha2 : a ≤ 𝔟 := by
      have h1 : s * v ≤ R.CSig * γ' := by
        calc s * v ≤ s * (R.CSig * γ' / s) := mul_le_mul_of_nonneg_left hv1 hs0.le
          _ = R.CSig * γ' := by field_simp
      calc a = (s * v) * Fw w (s * u * v) := by rw [ha]
        _ ≤ (R.CSig * γ') * Fw w 0 :=
            mul_le_mul h1 hFqle hFq0.le hCsγ
        _ ≤ 𝔟 := by linarith
    have hc2 : c ≤ 𝔟 := by
      have h1 : s * u ≤ R.CSig * γ' := by
        calc s * u ≤ s * (R.CSig * γ' / s) := mul_le_mul_of_nonneg_left hu1 hs0.le
          _ = R.CSig * γ' := by field_simp
      calc c = (s * u) * Fw w (s * u * v) := by rw [hc]
        _ ≤ (R.CSig * γ') * Fw w 0 :=
            mul_le_mul h1 hFqle hFq0.le hCsγ
        _ ≤ 𝔟 := by linarith
    have hres : γ' * R.CSig * ε₂ / s ≤ δ := by
      calc γ' * R.CSig * ε₂ / s ≤ γ' * R.CSig * ε₂ / sm :=
            div_le_div_of_nonneg_left (by positivity) hsm hsms
        _ ≤ γ' * R.CSig * (δ * sm / (γ' * R.CSig)) / sm := by
            gcongr
        _ = δ := by field_simp
    have hB := hBpos k
    -- residual 1
    have hr1 : |u - ∫ x, x / (s + a * x) ∂(νo k : Measure ℝ)| ≤ δ := by
      have hint : ∫ x, x / (s + a * x) ∂(νo k : Measure ℝ) =
          (R.B k : ℝ)⁻¹ * ((R.F k).C.Sout * (a • (R.F k).C.Sout + s • (1 : Mat (R.m k) (R.m k)))⁻¹).trace := by
        rw [hνo k, ← (def_app_de_branch_trace (R.F k).C (R.F k).hB hs0 ha0).1]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [add_comm s (a * x)]
      rw [hint]
      exact (gr_resid _ _ (R.F k).C.psdOut hB hs0 ha0 (R.normOut k) (hdm k) hEok).trans hres
    have hr2 : |v - ∫ x, x / (s + c * x) ∂(νi k : Measure ℝ)| ≤ δ := by
      have hint : ∫ x, x / (s + c * x) ∂(νi k : Measure ℝ) =
          (R.B k : ℝ)⁻¹ * ((R.F k).C.Sin * (c • (R.F k).C.Sin + s • (1 : Mat (R.n k) (R.n k)))⁻¹).trace := by
        rw [hνi k, ← (def_app_de_branch_trace (R.F k).C (R.F k).hB hs0 hc0).2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp only [add_comm s (c * x)]
      rw [hint]
      exact (gr_resid _ _ (R.F k).C.psdIn hB hs0 hc0 (R.normIn k) (hdn k) hEik).trans hres
    have hbr := hδ' (νo k) (νi k) (hK k) s hs u v a c ⟨hu0, hu2⟩ ⟨hv0, hv2⟩ ⟨ha0, ha2⟩ ⟨hc0, hc2⟩
      hr1 hr2 (by rw [ha, sub_self, abs_zero]; exact hδ.le) (by rw [hc, sub_self, abs_zero]; exact hδ.le)
    have hda : |a - (branchSol (Fw w) (νo k) (νi k) s).2.2.1| ≤ ε * sm ^ 2 / (4 * R.CSig) := by
      linarith [abs_nonneg (u - (branchSol (Fw w) (νo k) (νi k) s).1),
        abs_nonneg (v - (branchSol (Fw w) (νo k) (νi k) s).2.1),
        abs_nonneg (c - (branchSol (Fw w) (νo k) (νi k) s).2.2.2)]
    have hdc : |c - (branchSol (Fw w) (νo k) (νi k) s).2.2.2| ≤ ε * sm ^ 2 / (4 * R.CSig) := by
      linarith [abs_nonneg (u - (branchSol (Fw w) (νo k) (νi k) s).1),
        abs_nonneg (v - (branchSol (Fw w) (νo k) (νi k) s).2.1),
        abs_nonneg (a - (branchSol (Fw w) (νo k) (νi k) s).2.2.1)]
    have hside : ∀ {d x : ℝ}, 0 ≤ d → d ≤ R.CSig → 0 ≤ x → x ≤ ε * sm ^ 2 / (4 * R.CSig) →
        ε₂ / s + d * x / s ^ 2 ≤ ε / 2 := by
      intro d x hd0 hd hx0 hx
      have hε3 : ε₂ / s ≤ ε / 4 := by
        calc ε₂ / s ≤ ε₂ / sm := div_le_div_of_nonneg_left hε2.le hsm hsms
          _ ≤ (ε * sm / 4) / sm := div_le_div_of_nonneg_right hε2b hsm.le
          _ = ε / 4 := by field_simp
      have h1 : d * x ≤ R.CSig * (ε * sm ^ 2 / (4 * R.CSig)) :=
        mul_le_mul hd hx hx0 hCs.le
      have h2 : d * x / s ^ 2 ≤ ε / 4 := by
        calc d * x / s ^ 2 ≤ (R.CSig * (ε * sm ^ 2 / (4 * R.CSig))) / s ^ 2 :=
              div_le_div_of_nonneg_right h1 (by positivity)
          _ ≤ (R.CSig * (ε * sm ^ 2 / (4 * R.CSig))) / sm ^ 2 :=
              div_le_div_of_nonneg_left (by positivity) (by positivity)
                (pow_le_pow_left₀ hsm.le hsms 2)
          _ = ε / 4 := by field_simp
      linarith
    have hoc := gr_side (R.F k).C.Sout (expRes w (R.F k) (S k) t s) (R.F k).C.psdOut hs0 ha0 hb1 hEok
    have hic := gr_side (R.F k).C.Sin (expResT w (R.F k) (S k) t s) (R.F k).C.psdIn hs0 hc0 hb2 hEik
    have h1 := hside (pj_opNorm_nonneg (R.F k).C.Sout) (R.normOut k) (abs_nonneg _) hda
    have h2 := hside (pj_opNorm_nonneg (R.F k).C.Sin) (R.normIn k) (abs_nonneg _) hdc
    have e1 : opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ ε / 2 :=
      le_trans hoc h1
    have e2 : opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s) ≤ ε / 2 :=
      le_trans hic h2
    linarith
  rw [tendsto_order]
  refine ⟨fun a' ha' => Filter.Eventually.of_forall fun k => lt_of_lt_of_le ha' ?_, fun a' ha' => ?_⟩
  · exact Real.iSup_nonneg fun s => Real.iSup_nonneg fun _ =>
      add_nonneg (pj_opNorm_nonneg _) (pj_opNorm_nonneg _)
  · filter_upwards [hmain (a' / 2) (by positivity)] with k hk
    refine lt_of_le_of_lt (Real.iSup_le (fun s => Real.iSup_le (fun hs => hk s hs) (by positivity))
      (by positivity)) (by linarith)

private lemma gram_hEo (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (hS13 : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s * (R.F k).C.Sout)) ≤ ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - (s * sigmaTildeB w (R.F k) (S k) t s * Fw w (qB w (R.F k) (S k) t s)) •
          (expRes w (R.F k) (S k) t s * (R.F k).C.Sout)) ≤ ε := by
  set γ' : ℝ := max R.γstar 1 with hγ'
  have hγ'0 : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCs : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  obtain ⟨C, hC0, hCP⟩ := eqn_app_de_Pj_P I hI hIpos R.CSig γ'
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  intro ε hε
  set K0 : ℝ := R.CSig * γ' * R.CSig * C with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hBev : ∀ᶠ k in atTop, K0 / (ε / 2) ≤ (R.B k : ℝ) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp R.prop.B_top
    exact this.eventually_ge_atTop _
  filter_upwards [hS13 (ε / 2) (by positivity), hBev] with k hk hBk s hs
  have hBpos : (0 : ℝ) < (R.B k : ℝ) := by exact_mod_cast (R.F k).hB
  have hs0 : 0 < s := hIpos hs
  obtain ⟨-, -, -, hv1, hq0, -⟩ := eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
    ⟨R.normOut k, R.normIn k⟩ ⟨hdm k, hdn k⟩ s hs
  obtain ⟨-, -, hv0, -, -, -⟩ := eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
    ⟨R.normOut k, R.normIn k⟩ ⟨hdm k, hdn k⟩ s hs
  have hsτ : s * sigmaTildeB w (R.F k) (S k) t s ≤ R.CSig * γ' := by
    calc s * sigmaTildeB w (R.F k) (S k) t s ≤ s * (R.CSig * γ' / s) :=
          mul_le_mul_of_nonneg_left hv1 hs0.le
      _ = R.CSig * γ' := by field_simp
  have hglue := gr_glue w hw (expRes w (R.F k) (S k) t s)
    (fun j => expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s) (R.F k).C.Sout hs0 hv0 hsτ hq0
    (R.normOut k) hC0 hBpos (fun j => hCP (R.m k) (R.n k) (R.B k) w hw (Ω k) (P k) (R.F k) (S k) t
      (R.normOut k) (R.normIn k) (hdm k) (hdn k) j (slotOne (R.F k).hB) s hs)
  refine hglue.trans ?_
  have : R.CSig * γ' * R.CSig * C / (R.B k : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hBpos]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < ε / 2)).1 hBk
    linarith
  linarith [hk s hs]

private lemma gram_hEi (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (hPjT : ∃ C : ℝ, 0 ≤ C ∧ ∀ k (j : ℕ), ∀ s ∈ I,
      opNorm (expResT w (R.F k) (S k) t s - Muon.mean (P k) (fun ω =>
        Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s)) ≤
          C * w j / (R.B k : ℝ))
    (hS13 : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.n k) (R.n k)) - s • expResT w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (Muon.mean (P k) (fun ω =>
            Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s) *
            (R.F k).C.Sin)) ≤ ε) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.n k) (R.n k)) - s • expResT w (R.F k) (S k) t s
        - (s * sigmaB w (R.F k) (S k) t s * Fw w (qB w (R.F k) (S k) t s)) •
          (expResT w (R.F k) (S k) t s * (R.F k).C.Sin)) ≤ ε := by
  set γ' : ℝ := max R.γstar 1 with hγ'
  have hγ'0 : 0 < γ' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hCs : 0 < R.CSig := lt_of_lt_of_le one_pos R.hC
  obtain ⟨sm, hsm, hsmI⟩ : ∃ sm : ℝ, 0 < sm ∧ ∀ s ∈ I, sm ≤ s := by
    rcases I.eq_empty_or_nonempty with h | h
    · exact ⟨1, one_pos, by simp [h]⟩
    · exact ⟨sInf I, hIpos (hI.sInf_mem h), fun s hs => csInf_le hI.bddBelow hs⟩
  obtain ⟨C, hC0, hCP⟩ := hPjT
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  intro ε hε
  set K0 : ℝ := R.CSig * γ' * R.CSig * C with hK0
  have hK00 : 0 ≤ K0 := by positivity
  have hBev : ∀ᶠ k in atTop, K0 / (ε / 2) ≤ (R.B k : ℝ) := by
    have := (tendsto_natCast_atTop_atTop (R := ℝ)).comp R.prop.B_top
    exact this.eventually_ge_atTop _
  filter_upwards [hS13 (ε / 2) (by positivity), hBev] with k hk hBk s hs
  have hBpos : (0 : ℝ) < (R.B k : ℝ) := by exact_mod_cast (R.F k).hB
  have hs0 : 0 < s := hIpos hs
  obtain ⟨hv0, hv1, -, -, hq0, -⟩ := eqn_app_de_qI w hw (R.F k) (S k) t R.CSig γ' sm I hsm hsmI
    ⟨R.normOut k, R.normIn k⟩ ⟨hdm k, hdn k⟩ s hs
  have hsτ : s * sigmaB w (R.F k) (S k) t s ≤ R.CSig * γ' := by
    calc s * sigmaB w (R.F k) (S k) t s ≤ s * (R.CSig * γ' / s) :=
          mul_le_mul_of_nonneg_left hv1 hs0.le
      _ = R.CSig * γ' := by field_simp
  have hglue := gr_glue w hw (expResT w (R.F k) (S k) t s)
    (fun j => Muon.mean (P k) (fun ω =>
      Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s))
    (R.F k).C.Sin hs0 hv0 hsτ hq0 (R.normIn k) hC0 hBpos (fun j => hCP k j s hs)
  refine hglue.trans ?_
  have : R.CSig * γ' * R.CSig * C / (R.B k : ℝ) ≤ ε / 2 := by
    rw [div_le_iff₀ hBpos]
    have := (div_le_iff₀ (by positivity : (0:ℝ) < ε / 2)).1 hBk
    linarith
  linarith [hk s hs]

/-! ### Calculus of the replacement functions `ψ_x`, `f_x` -/

private lemma gc_den_pos {x : ℝ} (hx : 0 ≤ x) (d : ℝ) : 0 < 1 + x * d ^ 2 := by
  have := mul_nonneg hx (sq_nonneg d); linarith

private lemma gc_ratio {x : ℝ} (hx : 0 ≤ x) {N N' : ℝ → ℝ} (k : ℕ)
    (hN : ∀ d, HasDerivAt N (N' d) d) (d : ℝ) :
    HasDerivAt (fun d => N d / (1 + x * d ^ 2) ^ k)
      ((N' d * (1 + x * d ^ 2) - N d * (k * (2 * x * d))) / (1 + x * d ^ 2) ^ (k + 1)) d := by
  have hg := gc_den_pos hx d
  have h1 : HasDerivAt (fun d : ℝ => d ^ 2) (2 * d) d := by simpa using hasDerivAt_pow 2 d
  have h2 : HasDerivAt (fun d : ℝ => 1 + x * d ^ 2) (x * (2 * d)) d :=
    (h1.const_mul x).const_add 1
  have h3 := h2.pow k
  have h4 := (hN d).div h3 (pow_pos hg k).ne'
  refine h4.congr_deriv ?_
  simp only [Pi.pow_apply]
  generalize hG : 1 + x * d ^ 2 = G at *
  have hG0 : G ≠ 0 := hg.ne'
  rcases k with _ | k
  · simp
    field_simp
  · rw [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring

/-- ψ_x derivatives. -/
private lemma gc_psi_eq {x : ℝ} : psiX x = fun d => d ^ 2 / (1 + x * d ^ 2) ^ 1 := by
  funext d; simp [psiX]

private lemma gc_psi1 {x : ℝ} (hx : 0 ≤ x) : deriv (psiX x) = fun d => 2 * d / (1 + x * d ^ 2) ^ 2 := by
  funext d
  rw [gc_psi_eq]
  have := gc_ratio hx (N := fun d => d ^ 2) (N' := fun d => 2 * d) 1
    (fun d => by simpa using hasDerivAt_pow 2 d) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_psi2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (psiX x)) = fun d => (2 - 6 * x * d ^ 2) / (1 + x * d ^ 2) ^ 3 := by
  rw [gc_psi1 hx]
  funext d
  have := gc_ratio hx (N := fun d => 2 * d) (N' := fun d => 2) 2
    (fun d => by simpa using (hasDerivAt_id d).const_mul 2) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring


private lemma gc_f_eq {x : ℝ} : fX x = fun d => d / (1 + x * d ^ 2) ^ 1 := by
  funext d; simp [fX]

private lemma gc_f1 {x : ℝ} (hx : 0 ≤ x) :
    deriv (fX x) = fun d => (1 - x * d ^ 2) / (1 + x * d ^ 2) ^ 2 := by
  funext d
  rw [gc_f_eq]
  have := gc_ratio hx (N := fun d => d) (N' := fun d => 1) 1 (fun d => hasDerivAt_id d) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_f2 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (fX x)) = fun d => (-6 * x * d + 2 * x ^ 2 * d ^ 3) / (1 + x * d ^ 2) ^ 3 := by
  rw [gc_f1 hx]
  funext d
  have := gc_ratio hx (N := fun d => 1 - x * d ^ 2) (N' := fun d => -(2 * x * d)) 2
    (fun d => by
      have h1 : HasDerivAt (fun d : ℝ => d ^ 2) (2 * d) d := by simpa using hasDerivAt_pow 2 d
      have := ((h1.const_mul x).const_sub 1)
      convert this using 1; ring) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_f3 {x : ℝ} (hx : 0 ≤ x) :
    deriv (deriv (deriv (fX x))) =
      fun d => (-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) / (1 + x * d ^ 2) ^ 4 := by
  rw [gc_f2 hx]
  funext d
  have := gc_ratio hx (N := fun d => -6 * x * d + 2 * x ^ 2 * d ^ 3)
    (N' := fun d => -6 * x + 6 * x ^ 2 * d ^ 2) 3
    (fun d => by
      have h1 : HasDerivAt (fun d : ℝ => d ^ 3) (3 * d ^ 2) d := by simpa using hasDerivAt_pow 3 d
      have := ((hasDerivAt_id d).const_mul (-6 * x)).add (h1.const_mul (2 * x ^ 2))
      convert this using 1
      · funext y; simp
      · ring) d
  rw [this.deriv]
  have hg := gc_den_pos hx d
  field_simp
  ring

private lemma gc_psi_hyp {x : ℝ} (hx : 0 ≤ x) :
    ContDiff ℝ 2 (psiX x) ∧
      (∀ j : ℕ, j ≤ 2 → ∃ (K : ℝ) (k : ℕ), ∀ d : ℝ, |iteratedDeriv j (psiX x) d| ≤ K * (1 + |d| ^ k)) ∧
      ∀ d : ℝ, |iteratedDeriv 2 (psiX x) d| ≤ 6 := by
  have hcd : ContDiff ℝ 2 (psiX x) := by
    have : psiX x = fun d => d ^ 2 / (1 + x * d ^ 2) := by funext d; rfl
    rw [this]
    exact ContDiff.div (contDiff_id.pow 2) (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
      (fun d => (gc_den_pos hx d).ne')
  have hi2 : iteratedDeriv 2 (psiX x) = deriv (deriv (psiX x)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hb2 : ∀ d : ℝ, |iteratedDeriv 2 (psiX x) d| ≤ 6 := by
    intro d
    rw [hi2, gc_psi2 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    have e : 6 * x * d ^ 2 = 6 * y := by rw [hy]; ring
    show |(2 - 6 * x * d ^ 2) / (1 + y) ^ 3| ≤ 6
    rw [e, abs_div, abs_of_pos (pow_pos hg 3), div_le_iff₀ (pow_pos hg 3)]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg y, mul_nonneg hy0 (sq_nonneg y), pow_nonneg hy0 3]
  refine ⟨hcd, fun j hj => ?_, hb2⟩
  interval_cases j
  · refine ⟨1, 2, fun d => ?_⟩
    rw [iteratedDeriv_zero]
    have hg := gc_den_pos hx d
    show |d ^ 2 / (1 + x * d ^ 2)| ≤ _
    rw [abs_of_nonneg (by positivity), div_le_iff₀ hg]
    nlinarith [mul_nonneg hx (sq_nonneg d), sq_nonneg d, abs_nonneg d, sq_abs d,
      mul_nonneg (mul_nonneg hx (sq_nonneg d)) (sq_nonneg d)]
  · refine ⟨2, 1, fun d => ?_⟩
    rw [iteratedDeriv_one, gc_psi1 hx]
    have hg := gc_den_pos hx d
    show |2 * d / (1 + x * d ^ 2) ^ 2| ≤ _
    rw [abs_div, abs_of_pos (pow_pos hg 2), div_le_iff₀ (pow_pos hg 2), abs_mul]
    have h1 : 1 ≤ (1 + x * d ^ 2) ^ 2 := by nlinarith [mul_nonneg hx (sq_nonneg d)]
    simp only [abs_two, pow_one]
    nlinarith [abs_nonneg d]
  · exact ⟨6, 0, fun d => by simpa using (hb2 d).trans (by norm_num)⟩


private lemma gc_f_hyp {x : ℝ} (hx : 0 ≤ x) :
    ContDiff ℝ 3 (fX x) ∧
      (∀ j : ℕ, j ≤ 3 → ∃ (K : ℝ) (k : ℕ), ∀ d : ℝ, |iteratedDeriv j (fX x) d| ≤ K * (1 + |d| ^ k)) ∧
      (∀ d : ℝ, |deriv (fX x) d| ≤ 1) ∧ ∀ d : ℝ, |iteratedDeriv 3 (fX x) d| ≤ 36 * x := by
  have hcd : ContDiff ℝ 3 (fX x) := by
    have : fX x = fun d => d / (1 + x * d ^ 2) := by funext d; rfl
    rw [this]
    exact ContDiff.div contDiff_id (contDiff_const.add (contDiff_const.mul (contDiff_id.pow 2)))
      (fun d => (gc_den_pos hx d).ne')
  have hi2 : iteratedDeriv 2 (fX x) = deriv (deriv (fX x)) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hi3 : iteratedDeriv 3 (fX x) = deriv (deriv (deriv (fX x))) := by
    rw [iteratedDeriv_succ, hi2]
  have hb1 : ∀ d : ℝ, |deriv (fX x) d| ≤ 1 := by
    intro d
    rw [gc_f1 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    show |(1 - y) / (1 + y) ^ 2| ≤ 1
    rw [abs_div, abs_of_pos (pow_pos hg 2), div_le_iff₀ (pow_pos hg 2), one_mul, abs_le]
    constructor <;> nlinarith [sq_nonneg y]
  have hb3 : ∀ d : ℝ, |iteratedDeriv 3 (fX x) d| ≤ 36 * x := by
    intro d
    rw [hi3, gc_f3 hx]
    have hg := gc_den_pos hx d
    set y := x * d ^ 2 with hy
    have hy0 : 0 ≤ y := mul_nonneg hx (sq_nonneg d)
    have e : (-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) = x * (-6 + 36 * y - 6 * y ^ 2) := by
      rw [hy]; ring
    show |(-6 * x + 36 * x ^ 2 * d ^ 2 - 6 * x ^ 3 * d ^ 4) / (1 + y) ^ 4| ≤ 36 * x
    rw [e, abs_div, abs_of_pos (pow_pos hg 4), div_le_iff₀ (pow_pos hg 4), abs_mul,
      abs_of_nonneg hx]
    have h5 : |-6 + 36 * y - 6 * y ^ 2| ≤ 36 * (1 + y) ^ 4 := by
      rw [abs_le]
      constructor <;> nlinarith [sq_nonneg y, mul_nonneg hy0 (sq_nonneg y), pow_nonneg hy0 3,
        pow_nonneg hy0 4]
    nlinarith [mul_le_mul_of_nonneg_left h5 hx]
  refine ⟨hcd, fun j hj => ?_, hb1, hb3⟩
  interval_cases j
  · refine ⟨1, 1, fun d => ?_⟩
    rw [iteratedDeriv_zero]
    have hg := gc_den_pos hx d
    show |d / (1 + x * d ^ 2)| ≤ _
    rw [abs_div, abs_of_pos hg, div_le_iff₀ hg]
    nlinarith [abs_nonneg d, mul_nonneg hx (sq_nonneg d), mul_nonneg (abs_nonneg d) (mul_nonneg hx (sq_nonneg d))]
  · exact ⟨1, 0, fun d => by rw [iteratedDeriv_one]; have := hb1 d; simp; linarith⟩
  · refine ⟨6 * x + 2 * x ^ 2, 3, fun d => ?_⟩
    rw [hi2, gc_f2 hx]
    have hg := gc_den_pos hx d
    show |(-6 * x * d + 2 * x ^ 2 * d ^ 3) / (1 + x * d ^ 2) ^ 3| ≤ _
    have hg3 : 1 ≤ (1 + x * d ^ 2) ^ 3 := one_le_pow₀ (by nlinarith [mul_nonneg hx (sq_nonneg d)])
    rw [abs_div, abs_of_pos (pow_pos hg 3), div_le_iff₀ (pow_pos hg 3)]
    have a1 : |-6 * x * d| = 6 * x * |d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hx]; norm_num
    have a2 : |2 * x ^ 2 * d ^ 3| = 2 * x ^ 2 * |d| ^ 3 := by
      rw [abs_mul, abs_mul, abs_pow, abs_pow, abs_of_nonneg hx]; norm_num
    have h6 : |-6 * x * d + 2 * x ^ 2 * d ^ 3| ≤ 6 * x * |d| + 2 * x ^ 2 * |d| ^ 3 := by
      refine (abs_add_le _ _).trans ?_
      rw [a1, a2]
    have hd : |d| ≤ 1 + |d| ^ 3 := by
      have := abs_nonneg d
      nlinarith [sq_nonneg (|d| - 1), sq_nonneg |d|]
    have hK : 0 ≤ 6 * x + 2 * x ^ 2 := by positivity
    have hd3 : 0 ≤ |d| ^ 3 := by positivity
    calc |-6 * x * d + 2 * x ^ 2 * d ^ 3| ≤ 6 * x * |d| + 2 * x ^ 2 * |d| ^ 3 := h6
      _ ≤ (6 * x + 2 * x ^ 2) * (1 + |d| ^ 3) := by
          nlinarith [mul_nonneg hx hd3, mul_nonneg (sq_nonneg x) hd3, mul_le_mul_of_nonneg_left hd hx]
      _ ≤ (6 * x + 2 * x ^ 2) * (1 + |d| ^ 3) * (1 + x * d ^ 2) ^ 3 :=
          le_mul_of_one_le_right (by positivity) hg3
  · refine ⟨36 * x, 0, fun d => ?_⟩
    rw [pow_zero]
    nlinarith [hb3 d, hx]


/-! ### The Gaussian response in the Gram term (Step 2, main part) -/

private lemma gc_opNorm_le_fro {p q : ℕ} (K : Mat p q) : opNorm K ≤ fro K := by
  refine pj_opNorm_le_of_sq K (fro K) (Real.sqrt_nonneg _) fun y => ?_
  have hf : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
    unfold fro
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
    simp
  rw [hf, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => K i j) y
  simpa [Matrix.mulVec, dotProduct] using this

private lemma gc_resp {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1) {x CS : ℝ}
    (hx : 0 ≤ x) (hCS : opNorm C.Sout ≤ CS) (R0 : Mat m m) :
    opNorm (R0 * rOut C * Muon.mean (gaussPair m n)
        (fun p => psiX x (resid A p) • Muon.outer p.1 p.1) * rOut C - J x • (R0 * C.Sout)) ≤
      opNorm R0 * CS * (|∫ p, psiX x (resid A p) ∂(gaussPair m n) - J x| + 6 * opNorm A) := by
  obtain ⟨hcd, hpoly, hb2⟩ := gc_psi_hyp hx
  have hsq : rOut C * rOut C = C.Sout := by
    have h0 : 0 ≤ C.Sout := Matrix.nonneg_iff_posSemidef.mpr C.psdOut
    exact CFC.sqrt_mul_sqrt_self C.Sout h0
  set μ := gaussPair m n
  set c : ℝ := ∫ p, psiX x (resid A p) ∂μ with hc
  set G : Mat m m := Muon.mean μ (fun p => psiX x (resid A p) • (Muon.outer p.1 p.1 - 1)) with hG
  have hmean : Muon.mean μ (fun p => psiX x (resid A p) • Muon.outer p.1 p.1) = c • (1 : Mat m m) + G := by
    have hcont := (gram_psi_cont hx).comp (gram_resid_cont A)
    have hI0 : Integrable (fun p : Vec m × Vec n => psiX x (resid A p)) μ := by
      refine Integrable.mono' ((integrable_const (1 : ℝ)).add (gram_resid_pow4_int A hA))
        hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
      show ‖psiX x (resid A p)‖ ≤ 1 + resid A p ^ 4
      rw [Real.norm_eq_abs]
      have h1 := gram_psi_abs (x := x) (d := resid A p) hx
      nlinarith [sq_nonneg (resid A p ^ 2 - 1), sq_nonneg (resid A p)]
    have hI4 : ∀ i : Fin m, Integrable (fun p : Vec m × Vec n => p.1 i ^ 4) μ := by
      intro i
      have hm : MeasurePreserving (fun p : Vec m × Vec n => p.1 i) μ (gaussianReal 0 1) := by
        have h1 : MeasurePreserving (fun z : Vec m => z i) (Muon.Foundations.stdGaussianPi m)
            (gaussianReal 0 1) := by
          unfold Muon.Foundations.stdGaussianPi
          exact measurePreserving_eval _ i
        exact h1.comp measurePreserving_fst
      exact (hm.integrable_comp (g := fun x : ℝ => x ^ 4) (by fun_prop)).2
        (Muon.Foundations.gaussian_integrable_pow 4)
    have hIz : ∀ i k : Fin m, Integrable (fun p : Vec m × Vec n =>
        psiX x (resid A p) * (p.1 i * p.1 k)) μ := by
      intro i k
      refine Integrable.mono' (((gram_resid_pow4_int A hA).add
        (((hI4 i).add (hI4 k)).const_mul (1 / 2))).const_mul (1 / 2))
        (hcont.mul (by fun_prop : Continuous fun p : Vec m × Vec n => p.1 i * p.1 k)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      show ‖psiX x (resid A p) * (p.1 i * p.1 k)‖ ≤
        1 / 2 * (resid A p ^ 4 + 1 / 2 * (p.1 i ^ 4 + p.1 k ^ 4))
      rw [Real.norm_eq_abs, abs_mul]
      have h1 := gram_psi_abs (x := x) (d := resid A p) hx
      have h3 : |psiX x (resid A p)| * |p.1 i * p.1 k| ≤ resid A p ^ 2 * |p.1 i * p.1 k| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have h4 : resid A p ^ 2 * |p.1 i * p.1 k| ≤
          (resid A p ^ 4 + (p.1 i * p.1 k) ^ 2) / 2 := by
        have := sq_nonneg (resid A p ^ 2 - |p.1 i * p.1 k|)
        nlinarith [sq_abs (p.1 i * p.1 k)]
      have h5 : (p.1 i * p.1 k) ^ 2 ≤ (p.1 i ^ 4 + p.1 k ^ 4) / 2 := by
        nlinarith [sq_nonneg (p.1 i ^ 2 - p.1 k ^ 2)]
      nlinarith
    ext i k
    simp only [Muon.mean, hG, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Muon.outer, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply, Pi.smul_apply]
    have e : (fun ω : Vec m × Vec n => psiX x (resid A ω) *
        (ω.1 i * ω.1 k - if i = k then (1 : ℝ) else 0)) = fun ω =>
        psiX x (resid A ω) * (ω.1 i * ω.1 k) -
          (if i = k then (1 : ℝ) else 0) * psiX x (resid A ω) := by
      funext ω; ring
    rw [e, integral_sub (hIz i k) (hI0.const_mul _), integral_const_mul, hc]
    ring
  have hGn : opNorm G ≤ 6 * opNorm A := by
    have h := lem_app_de_stein_iv A (psiX x) hcd hpoly 6 hb2
    rw [hA, mul_one] at h
    exact (gc_opNorm_le_fro G).trans h
  have hE : R0 * rOut C * (c • (1 : Mat m m) + G) * rOut C - J x • (R0 * C.Sout) =
      (c - J x) • (R0 * C.Sout) + R0 * rOut C * G * rOut C := by
    rw [Matrix.mul_add, Matrix.add_mul, ← hsq]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.mul_assoc, sub_smul]
    abel
  rw [hmean, hE]
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCS
  have hrn : opNorm (rOut C) ≤ Real.sqrt CS := by
    refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCS y
  have hR0 := pj_opNorm_nonneg R0
  have h1 : opNorm ((c - J x) • (R0 * C.Sout)) ≤ |c - J x| * (opNorm R0 * CS) := by
    rw [gr_opNorm_smul]
    exact mul_le_mul_of_nonneg_left ((gr_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_left hCS hR0)) (abs_nonneg _)
  have h2 : opNorm (R0 * rOut C * G * rOut C) ≤ opNorm R0 * CS * (6 * opNorm A) := by
    have h3 : opNorm (rOut C * G * rOut C) ≤ CS * (6 * opNorm A) := by
      calc opNorm (rOut C * G * rOut C) ≤ opNorm (rOut C * G) * opNorm (rOut C) := gr_opNorm_mul _ _
        _ ≤ (opNorm (rOut C) * opNorm G) * opNorm (rOut C) :=
            mul_le_mul_of_nonneg_right (gr_opNorm_mul _ _) (pj_opNorm_nonneg _)
        _ ≤ (Real.sqrt CS * (6 * opNorm A)) * Real.sqrt CS :=
            mul_le_mul (mul_le_mul hrn hGn (pj_opNorm_nonneg _) (Real.sqrt_nonneg _)) hrn
              (pj_opNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
                (mul_nonneg (by norm_num) (pj_opNorm_nonneg _)))
        _ = (Real.sqrt CS * Real.sqrt CS) * (6 * opNorm A) := by ring
        _ = CS * (6 * opNorm A) := by rw [Real.mul_self_sqrt hCS0]
    have e : R0 * rOut C * G * rOut C = R0 * (rOut C * G * rOut C) := by
      simp only [Matrix.mul_assoc]
    rw [e]
    calc opNorm (R0 * (rOut C * G * rOut C)) ≤ opNorm R0 * opNorm (rOut C * G * rOut C) :=
          gr_opNorm_mul _ _
      _ ≤ opNorm R0 * (CS * (6 * opNorm A)) := mul_le_mul_of_nonneg_left h3 hR0
      _ = _ := by ring
  calc _ ≤ opNorm ((c - J x) • (R0 * C.Sout)) + opNorm (R0 * rOut C * G * rOut C) :=
        gr_opNorm_add _ _
    _ ≤ _ := by nlinarith [h1, h2]

/-! ### The Gaussian response in the mixed term (Step 3, main part) -/

private lemma gc_resp_f {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1)
    {x CS : ℝ} (hx : 0 ≤ x) (hCo : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS) (X0 : Mat m n) :
    opNorm (X0 * rIn C * Muon.mean (gaussPair m n)
        (fun p => fX x (resid A p) • Muon.outer p.2 p.1) * rOut C) ≤
      opNorm X0 * CS * (opNorm A + 36 * x * opNorm A ^ 2) := by
  obtain ⟨hcd, hpoly, hb1, hb3⟩ := gc_f_hyp hx
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  set μ := gaussPair m n
  set M1 : Mat m n := Muon.mean μ (fun p => fX x (resid A p) • Muon.outer p.1 p.2) with hM1
  have hT : Muon.mean μ (fun p => fX x (resid A p) • Muon.outer p.2 p.1) = M1ᵀ := by
    ext i k
    simp only [Muon.mean, hM1, Matrix.of_apply, Matrix.transpose_apply, Matrix.smul_apply,
      smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    ring
  have hst := lem_app_de_stein_ii A (fX x) hcd hpoly (36 * x) hb3
  rw [hA, mul_one] at hst
  have hint : |∫ p, deriv (fX x) (resid A p) ∂μ| ≤ 1 := by
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun p => deriv (fX x) (resid A p)) (C := 1)
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hb1 _)
    simpa using this
  have hM1n : opNorm M1 ≤ opNorm A + 36 * x * opNorm A ^ 2 := by
    have h0 : M1 = (∫ p, deriv (fX x) (resid A p) ∂μ) • A + (M1 - (∫ p, deriv (fX x) (resid A p) ∂μ) • A) := by
      abel
    calc opNorm M1 ≤ opNorm ((∫ p, deriv (fX x) (resid A p) ∂μ) • A) +
          opNorm (M1 - (∫ p, deriv (fX x) (resid A p) ∂μ) • A) := by
          conv_lhs => rw [h0]
          exact gr_opNorm_add _ _
      _ ≤ 1 * opNorm A + 36 * x * opNorm A ^ 2 := by
          rw [gr_opNorm_smul]
          exact add_le_add (mul_le_mul_of_nonneg_right hint (pj_opNorm_nonneg _))
            ((gc_opNorm_le_fro _).trans hst)
      _ = _ := by ring
  have hrn : ∀ {k : ℕ} (S : Matrix (Fin k) (Fin k) ℝ), S.PosSemidef → opNorm S ≤ CS →
      opNorm (CFC.sqrt S) ≤ Real.sqrt CS := by
    intro k S hS hSC
    refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le S hS CS hSC y
  have hro := hrn C.Sout C.psdOut hCo
  have hri := hrn C.Sin C.psdIn hCi
  rw [hT]
  have h3 : opNorm (rIn C * M1ᵀ * rOut C) ≤ CS * (opNorm A + 36 * x * opNorm A ^ 2) := by
    calc opNorm (rIn C * M1ᵀ * rOut C) ≤ opNorm (rIn C * M1ᵀ) * opNorm (rOut C) := gr_opNorm_mul _ _
      _ ≤ (opNorm (rIn C) * opNorm M1ᵀ) * opNorm (rOut C) :=
          mul_le_mul_of_nonneg_right (gr_opNorm_mul _ _) (pj_opNorm_nonneg _)
      _ ≤ (Real.sqrt CS * (opNorm A + 36 * x * opNorm A ^ 2)) * Real.sqrt CS := by
          rw [pj_opNorm_transpose]
          exact mul_le_mul (mul_le_mul hri hM1n (pj_opNorm_nonneg _) (Real.sqrt_nonneg _)) hro
            (pj_opNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _)
              ((pj_opNorm_nonneg _).trans hM1n))
      _ = (Real.sqrt CS * Real.sqrt CS) * (opNorm A + 36 * x * opNorm A ^ 2) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hCS0]
  have e : X0 * rIn C * M1ᵀ * rOut C = X0 * (rIn C * M1ᵀ * rOut C) := by
    simp only [Matrix.mul_assoc]
  rw [e]
  calc opNorm (X0 * (rIn C * M1ᵀ * rOut C)) ≤ opNorm X0 * opNorm (rIn C * M1ᵀ * rOut C) :=
        gr_opNorm_mul _ _
    _ ≤ opNorm X0 * (CS * (opNorm A + 36 * x * opNorm A ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 (pj_opNorm_nonneg _)
    _ = _ := by ring

/-! ### Replacement errors against a Gaussian rank-one factor (Steps 2 and 3, error parts) -/

/-- Cauchy-Schwarz bound for `E[e · N]`, where every bilinear form of `N` is a product of two
linear Gaussian forms with controlled fourth moments. -/
private lemma gc_repl_mat {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m : ℕ} (e : Ω' → ℝ) (hem : Measurable e) (K a b : ℝ) (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : eLpNorm e 2 P ≤ ENNReal.ofReal K) (N : Ω' → Mat m m)
    (hN : ∀ x y : Vec m, ∃ l1 l2 : Ω' → ℝ, Measurable l1 ∧ Measurable l2 ∧
      (∀ ω, dotProduct x (N ω *ᵥ y) = l1 ω * l2 ω) ∧
      ∫⁻ ω, ENNReal.ofReal (l1 ω ^ 4) ∂P ≤ ENNReal.ofReal (3 * (a * ∑ i, x i ^ 2) ^ 2) ∧
      ∫⁻ ω, ENNReal.ofReal (l2 ω ^ 4) ∂P ≤ ENNReal.ofReal (3 * (b * ∑ i, y i ^ 2) ^ 2)) :
    (∀ i k, Integrable (fun ω => (e ω • N ω) i k) P) ∧
      opNorm (Muon.mean P (fun ω => e ω • N ω)) ≤ K * Real.sqrt (3 * (a * b)) := by
  have he2 : ∫⁻ ω, ENNReal.ofReal (|e ω| ^ 2) ∂P ≤ ENNReal.ofReal (K ^ 2) :=
    pj_lint_pow P e hem 2 (by norm_num) K hK (by simpa using he)
  -- the key lintegral bound for each pair of vectors
  have key : ∀ x y : Vec m, ∃ l1 l2 : Ω' → ℝ, Measurable l1 ∧ Measurable l2 ∧
      (∀ ω, dotProduct x (N ω *ᵥ y) = l1 ω * l2 ω) ∧
      ∫⁻ ω, ENNReal.ofReal |e ω * dotProduct x (N ω *ᵥ y)| ∂P ≤
        ENNReal.ofReal (K * Real.sqrt (3 * (a * b)) * Real.sqrt (∑ i, x i ^ 2) *
          Real.sqrt (∑ i, y i ^ 2)) := by
    intro x y
    obtain ⟨l1, l2, h1, h2, heq, m1, m2⟩ := hN x y
    refine ⟨l1, l2, h1, h2, heq, ?_⟩
    have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hh := pj_holder P (fun ω => |e ω|) l1 l2 hem.abs h1 h2 (fun _ => abs_nonneg _) (K ^ 2)
      (a * ∑ i, x i ^ 2) (b * ∑ i, y i ^ 2) (by positivity) (by positivity) (by positivity)
      he2 m1 m2
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) (hh.trans (le_of_eq ?_))
    · rw [heq ω, abs_mul, abs_mul]
    · congr 1
      rw [Real.sqrt_sq hK, show 3 * ((a * ∑ i, x i ^ 2) * (b * ∑ i, y i ^ 2)) =
        3 * (a * b) * ((∑ i, x i ^ 2) * (∑ i, y i ^ 2)) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_mul hx0]
      ring
  have hDm : ∀ x y : Vec m, Measurable (fun ω => e ω * dotProduct x (N ω *ᵥ y)) := by
    intro x y
    obtain ⟨l1, l2, h1, h2, heq, -, -⟩ := hN x y
    have : (fun ω => e ω * dotProduct x (N ω *ᵥ y)) = fun ω => e ω * (l1 ω * l2 ω) := by
      funext ω; rw [heq ω]
    rw [this]
    exact hem.mul (h1.mul h2)
  have hint : ∀ x y : Vec m, Integrable (fun ω => e ω * dotProduct x (N ω *ᵥ y)) P := by
    intro x y
    obtain ⟨l1, l2, -, -, -, hl⟩ := key x y
    refine ⟨(hDm x y).aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := K * Real.sqrt (3 * (a * b)) *
      Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2)))
    refine le_trans (le_of_eq (lintegral_congr fun ω => ?_)) hl
    rw [← ofReal_norm, Real.norm_eq_abs]
  have hD : ∀ i k, Integrable (fun ω => (e ω • N ω) i k) P := by
    intro i k
    have := hint (Pi.single i 1) (Pi.single k 1)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨hD, pj_opNorm_of_bilin _ _ (by positivity) fun x y => ?_⟩
  rw [Muon.mean]
  rw [pj_bilin_int P (fun ω => e ω • N ω) hD x y]
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsm : ∀ ω, dotProduct x ((e ω • N ω) *ᵥ y) = e ω * dotProduct x (N ω *ᵥ y) := by
    intro ω
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  simp only [hsm]
  obtain ⟨l1, l2, -, -, -, hl⟩ := key x y
  calc |∫ ω, e ω * dotProduct x (N ω *ᵥ y) ∂P|
      ≤ ∫ ω, |e ω * dotProduct x (N ω *ᵥ y)| ∂P := abs_integral_le_integral_abs
    _ = (∫⁻ ω, ENNReal.ofReal |e ω * dotProduct x (N ω *ᵥ y)| ∂P).toReal := by
        refine integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun ω => abs_nonneg _) ?_
        exact (hDm x y).abs.aestronglyMeasurable
    _ ≤ (ENNReal.ofReal (K * Real.sqrt (3 * (a * b)) * Real.sqrt (∑ i, x i ^ 2) *
          Real.sqrt (∑ i, y i ^ 2))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hl
    _ = K * Real.sqrt (3 * (a * b)) * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) :=
        ENNReal.toReal_ofReal (by positivity)

private lemma gc_lint4 {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0)
    (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (G : Mat m n × (Vec m × Vec n) → ℝ) (hG : Measurable G) (q : ℝ)
    (hin : ∀ M : Mat m n, ∫⁻ x, ENNReal.ofReal (G (M, x)) ∂(gaussPair m n) ≤ ENNReal.ofReal q) :
    ∫⁻ ω, ENNReal.ofReal (G (M0 ω, zw ω)) ∂P ≤ ENNReal.ofReal q := by
  have hpair : Measurable (fun ω => (M0 ω, zw ω)) := hM0.prodMk hzw
  have hGm : Measurable (fun p : Mat m n × (Vec m × Vec n) => ENNReal.ofReal (G p)) :=
    ENNReal.measurable_ofReal.comp hG
  haveI : IsProbabilityMeasure (P.map M0) :=
    ⟨by rw [Measure.map_apply hM0 MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  calc ∫⁻ ω, ENNReal.ofReal (G (M0 ω, zw ω)) ∂P
      = ∫⁻ p, ENNReal.ofReal (G p) ∂(P.map (fun ω => (M0 ω, zw ω))) :=
        (lintegral_map hGm hpair).symm
    _ = ∫⁻ p, ENNReal.ofReal (G p) ∂((P.map M0).prod (gaussPair m n)) := by rw [hmap]
    _ = ∫⁻ m0, ∫⁻ x, ENNReal.ofReal (G (m0, x)) ∂(gaussPair m n) ∂(P.map M0) :=
        lintegral_prod _ hGm.aemeasurable
    _ ≤ ∫⁻ _m0, ENNReal.ofReal q ∂(P.map M0) := lintegral_mono fun m0 => hin m0
    _ = ENNReal.ofReal q := by rw [lintegral_const, measure_univ, mul_one]

private lemma gc_lint4_fst {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0)
    (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (c : Mat m n → Vec m) (hc : Measurable c) (q : ℝ) (hq : ∀ M, ∑ i, c M i ^ 2 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i, (zw ω).1 i * c (M0 ω) i) ^ 4) ∂P ≤ ENNReal.ofReal (3 * q ^ 2) := by
  refine gc_lint4 P M0 zw hM0 hzw hmap (fun p => (∑ i, p.2.1 i * c p.1 i) ^ 4) ?_ _ fun M => ?_
  · have : Measurable (fun p : Mat m n × (Vec m × Vec n) => ∑ i, p.2.1 i * c p.1 i) :=
      Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).mul
          ((measurable_pi_apply i).comp (hc.comp measurable_fst))
    exact this.pow_const 4
  · refine (pj_lint4_fst (n := n) (c M)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ ∑ i, c M i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [hq M]

private lemma gc_lint4_snd {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0)
    (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (c : Mat m n → Vec n) (hc : Measurable c) (q : ℝ) (hq : ∀ M, ∑ i, c M i ^ 2 ≤ q) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i, (zw ω).2 i * c (M0 ω) i) ^ 4) ∂P ≤ ENNReal.ofReal (3 * q ^ 2) := by
  refine gc_lint4 P M0 zw hM0 hzw hmap (fun p => (∑ i, p.2.2 i * c p.1 i) ^ 4) ?_ _ fun M => ?_
  · have : Measurable (fun p : Mat m n × (Vec m × Vec n) => ∑ i, p.2.2 i * c p.1 i) :=
      Finset.measurable_sum _ fun i _ =>
        ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd)).mul
          ((measurable_pi_apply i).comp (hc.comp measurable_fst))
    exact this.pow_const 4
  · refine (pj_lint4_snd (m := m) (c M)).trans (ENNReal.ofReal_le_ofReal ?_)
    have h0 : 0 ≤ ∑ i, c M i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    nlinarith [hq M]

private lemma gc_outer_mulVec {m : ℕ} (u y : Vec m) :
    (Muon.outer u u) *ᵥ y = (dotProduct u y) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Muon.outer, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm,
    mul_left_comm]

private lemma gc_dot_sym {m : ℕ} (A : Mat m m) (z y : Vec m) (hA : Aᵀ = A) :
    dotProduct (A *ᵥ z) y = ∑ i, z i * (A *ᵥ y) i := by
  calc dotProduct (A *ᵥ z) y = dotProduct y (A *ᵥ z) := dotProduct_comm _ _
    _ = dotProduct (y ᵥ* A) z := Matrix.dotProduct_mulVec _ _ _
    _ = dotProduct (A *ᵥ y) z := by rw [← Matrix.mulVec_transpose, hA]
    _ = _ := by simp [dotProduct, mul_comm]

private lemma gc_dot_T {m : ℕ} (T : Mat m m) (x z : Vec m) :
    dotProduct x (T *ᵥ z) = ∑ i, z i * ∑ j, x j * T j i := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma gc_repl_uu {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (M0 : Ω' → Mat m n)
    (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    {s CS : ℝ} (hs : 0 < s) (hCo : opNorm C.Sout ≤ CS) (e : Ω' → ℝ) (hem : Measurable e)
    (K : ℝ) (hK : 0 ≤ K) (he : eLpNorm e 2 P ≤ ENNReal.ofReal K) :
    (∀ i k, Integrable (fun ω => (e ω • ((B : ℝ) • (Rs (M0 ω) s *
      Muon.outer (momU C B (zw ω)) (momU C B (zw ω))))) i k) P) ∧
    opNorm (Muon.mean P (fun ω => e ω • ((B : ℝ) • (Rs (M0 ω) s *
      Muon.outer (momU C B (zw ω)) (momU C B (zw ω)))))) ≤
      K * Real.sqrt (3 * (CS / s ^ 2 * CS)) := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsym : (rOut C)ᵀ = rOut C := pj_sqrt_symm _
  have hrn : opNorm (rOut C) ≤ Real.sqrt CS := by
    refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCo y
  refine gc_repl_mat P e hem K (CS / s ^ 2) CS hK (by positivity) hCS0 he _ fun x y => ?_
  set c1 : Mat m n → Vec m := fun M i => ∑ j, x j * (Rs M s * rOut C) j i with hc1
  set c2 : Vec m := Matrix.mulVec (rOut C) y with hc2
  have hRm : Measurable (fun M : Mat m n => Rs M s) := pj_Rs_measurable s
  have hc1m : Measurable c1 := by
    refine measurable_pi_iff.2 fun i => Finset.measurable_sum _ fun j _ => ?_
    refine measurable_const.mul ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      (((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hRm))).mul measurable_const
  refine ⟨fun ω => ∑ i, (zw ω).1 i * c1 (M0 ω) i, fun ω => ∑ i, (zw ω).1 i * c2 i, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_fst.comp hzw)).mul
        ((measurable_pi_apply i).comp (hc1m.comp hM0))
  · exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_fst.comp hzw)).mul measurable_const
  · intro ω
    have hr : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ * (B : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hBr.le]; field_simp
    have h1 : dotProduct x (((B : ℝ) • (Rs (M0 ω) s * Muon.outer (momU C B (zw ω)) (momU C B (zw ω)))) *ᵥ y)
        = (B : ℝ) * (dotProduct (momU C B (zw ω)) y * dotProduct x (Rs (M0 ω) s *ᵥ momU C B (zw ω))) := by
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, gc_outer_mulVec,
        Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [h1]
    have h2 : dotProduct (momU C B (zw ω)) y =
        (Real.sqrt (B : ℝ))⁻¹ * ∑ i, (zw ω).1 i * c2 i := by
      unfold momU
      rw [smul_dotProduct, smul_eq_mul, gc_dot_sym _ _ _ hsym]
    have h3 : dotProduct x (Rs (M0 ω) s *ᵥ momU C B (zw ω)) =
        (Real.sqrt (B : ℝ))⁻¹ * ∑ i, (zw ω).1 i * c1 (M0 ω) i := by
      unfold momU
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, gc_dot_T]
    rw [h2, h3]
    linear_combination (∑ i, (zw ω).1 i * c2 i) * (∑ i, (zw ω).1 i * c1 (M0 ω) i) * hr
  · refine gc_lint4_fst P M0 zw hM0 hzw hmap c1 hc1m _ fun M => ?_
    have hc : c1 M = Matrix.mulVec (Rs M s * rOut C)ᵀ x := by
      ext i
      simp [hc1, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    have hop : opNorm (Rs M s * rOut C) ≤ (1 / s) * Real.sqrt CS :=
      (gr_opNorm_mul _ _).trans (mul_le_mul (lem_app_de_resolvent M s hs).1 hrn
        (pj_opNorm_nonneg _) (by positivity))
    have h := pj_sq_mulVec (Rs M s * rOut C)ᵀ x
    rw [pj_opNorm_transpose] at h
    rw [hc]
    refine h.trans ?_
    have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : opNorm (Rs M s * rOut C) ^ 2 ≤ ((1 / s) * Real.sqrt CS) ^ 2 :=
      pow_le_pow_left₀ (pj_opNorm_nonneg _) hop 2
    calc opNorm (Rs M s * rOut C) ^ 2 * ∑ i, x i ^ 2 ≤ ((1 / s) * Real.sqrt CS) ^ 2 * ∑ i, x i ^ 2 :=
          mul_le_mul_of_nonneg_right this h0
      _ = CS / s ^ 2 * ∑ i, x i ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hCS0]; field_simp
  · refine gc_lint4_fst P M0 zw hM0 hzw hmap (fun _ => c2) measurable_const _ fun M => ?_
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCo y

private lemma gc_outer_mulVec' {m n : ℕ} (u : Vec m) (v y : Vec n) :
    (Muon.outer u v) *ᵥ y = (dotProduct v y) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Muon.outer, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm,
    mul_left_comm]

private lemma gc_dot_T2 {m n : ℕ} (T : Mat m n) (x : Vec m) (z : Vec n) :
    dotProduct x (T *ᵥ z) = ∑ i, z i * ∑ j, x j * T j i := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma gc_repl_vu {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B) (M0 : Ω' → Mat m n)
    (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    {s CS : ℝ} (hs : 0 < s) (hCo : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS)
    (e : Ω' → ℝ) (hem : Measurable e)
    (K : ℝ) (hK : 0 ≤ K) (he : eLpNorm e 2 P ≤ ENNReal.ofReal K) :
    (∀ i k, Integrable (fun ω => (e ω • ((B : ℝ) • (Xs (M0 ω) s *
      Muon.outer (momV C B (zw ω)) (momU C B (zw ω))))) i k) P) ∧
    opNorm (Muon.mean P (fun ω => e ω • ((B : ℝ) • (Xs (M0 ω) s *
      Muon.outer (momV C B (zw ω)) (momU C B (zw ω)))))) ≤
      K * Real.sqrt (3 * (CS / (4 * s) * CS)) := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsym : (rOut C)ᵀ = rOut C := pj_sqrt_symm _
  have hrno : opNorm (rOut C) ≤ Real.sqrt CS := by
    refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCo y
  have hrni : opNorm (rIn C) ≤ Real.sqrt CS := by
    refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sin C.psdIn CS hCi y
  refine gc_repl_mat P e hem K (CS / (4 * s)) CS hK (by positivity) hCS0 he _ fun x y => ?_
  set c1 : Mat m n → Vec n := fun M i => ∑ j, x j * (Xs M s * rIn C) j i with hc1
  set c2 : Vec m := Matrix.mulVec (rOut C) y with hc2
  have hXm : Measurable (fun M : Mat m n => Xs M s) := by
    have hRm : Measurable (fun M : Mat m n => Rs M s) := pj_Rs_measurable s
    refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i => ?_
    simp only [Xs, Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hRm)).mul
        ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_id))
  have hc1m : Measurable c1 := by
    refine measurable_pi_iff.2 fun i => Finset.measurable_sum _ fun j _ => ?_
    refine measurable_const.mul ?_
    simp only [Matrix.mul_apply]
    exact Finset.measurable_sum _ fun k _ =>
      (((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hXm))).mul measurable_const
  refine ⟨fun ω => ∑ i, (zw ω).2 i * c1 (M0 ω) i, fun ω => ∑ i, (zw ω).1 i * c2 i, ?_, ?_, ?_, ?_, ?_⟩
  · exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_snd.comp hzw)).mul
        ((measurable_pi_apply i).comp (hc1m.comp hM0))
  · exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp (measurable_fst.comp hzw)).mul measurable_const
  · intro ω
    have hr : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ * (B : ℝ) = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hBr.le]; field_simp
    have h1 : dotProduct x (((B : ℝ) • (Xs (M0 ω) s * Muon.outer (momV C B (zw ω)) (momU C B (zw ω)))) *ᵥ y)
        = (B : ℝ) * (dotProduct (momU C B (zw ω)) y * dotProduct x (Xs (M0 ω) s *ᵥ momV C B (zw ω))) := by
      rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, gc_outer_mulVec',
        Matrix.mulVec_smul, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    rw [h1]
    have h2 : dotProduct (momU C B (zw ω)) y =
        (Real.sqrt (B : ℝ))⁻¹ * ∑ i, (zw ω).1 i * c2 i := by
      unfold momU
      rw [smul_dotProduct, smul_eq_mul, gc_dot_sym _ _ _ hsym]
    have h3 : dotProduct x (Xs (M0 ω) s *ᵥ momV C B (zw ω)) =
        (Real.sqrt (B : ℝ))⁻¹ * ∑ i, (zw ω).2 i * c1 (M0 ω) i := by
      unfold momV
      rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Matrix.mulVec_mulVec, gc_dot_T2]
    rw [h2, h3]
    linear_combination (∑ i, (zw ω).1 i * c2 i) * (∑ i, (zw ω).2 i * c1 (M0 ω) i) * hr
  · refine gc_lint4_snd P M0 zw hM0 hzw hmap c1 hc1m _ fun M => ?_
    have hc : c1 M = Matrix.mulVec (Xs M s * rIn C)ᵀ x := by
      ext i
      simp [hc1, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
    have hop : opNorm (Xs M s * rIn C) ≤ (1 / (2 * Real.sqrt s)) * Real.sqrt CS :=
      (gr_opNorm_mul _ _).trans (mul_le_mul (lem_app_de_resolvent M s hs).2.2.1 hrni
        (pj_opNorm_nonneg _) (by positivity))
    have h := pj_sq_mulVec (Xs M s * rIn C)ᵀ x
    rw [pj_opNorm_transpose] at h
    rw [hc]
    refine h.trans ?_
    have h0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have : opNorm (Xs M s * rIn C) ^ 2 ≤ ((1 / (2 * Real.sqrt s)) * Real.sqrt CS) ^ 2 :=
      pow_le_pow_left₀ (pj_opNorm_nonneg _) hop 2
    calc opNorm (Xs M s * rIn C) ^ 2 * ∑ i, x i ^ 2
        ≤ ((1 / (2 * Real.sqrt s)) * Real.sqrt CS) ^ 2 * ∑ i, x i ^ 2 :=
          mul_le_mul_of_nonneg_right this h0
      _ = CS / (4 * s) * ∑ i, x i ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hCS0, div_pow, mul_pow, Real.sq_sqrt hs.le]
          field_simp
          ring
  · refine gc_lint4_fst P M0 zw hM0 hzw hmap (fun _ => c2) measurable_const _ fun M => ?_
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCo y

/-! ### Step 1: the series identity for `1 - s R` -/

private lemma gs_age {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s' : ℤ) (j : ℕ) (ω : Ω') :
    w j • frozenBatchG F S s' ω = ∑ a : Fin B, (w j * resid F.A (S.zw s' a ω)) •
      Muon.outer (momU F.C B (S.zw s' a ω)) (momV F.C B (S.zw s' a ω)) := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  rw [frozenBatchG_eq_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold sampleTerm
  rw [pj_rOut_outer_rIn]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply,
    resid]
  rw [← hcc]
  ring

private lemma gs_series {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ)
    (hs : 0 < s) (ω : Ω')
    (hsum : Summable fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :
    HasSum (fun j : ℕ => ∑ a : Fin B, Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
      ((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) := by
  set M := WeightedBuf w F S t ω with hM
  have hMs : HasSum (fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) M :=
    hsum.hasSum
  have hT := hMs.matrix_transpose
  let f : Matrix (Fin n) (Fin m) ℝ →+ Matrix (Fin m) (Fin m) ℝ :=
    { toFun := fun X => (Rs M s * M) * X, map_zero' := Matrix.mul_zero _,
      map_add' := fun X Y => Matrix.mul_add _ _ _ }
  have hmul := hT.map f (continuous_const.matrix_mul continuous_id)
  have h6 := (lem_app_de_resolvent M s hs).2.2.2.2.2.1
  have e1 : Rs M s * M * Mᵀ = (1 : Mat m m) - s • Rs M s := by
    rw [Matrix.mul_assoc, h6]
  have hmul' : HasSum (fun j : ℕ => (Rs M s * M) * (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)ᵀ)
      ((1 : Mat m m) - s • Rs M s) := by
    rw [← e1]; exact hmul
  have hterm : ∀ j : ℕ, (Rs M s * M) * (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)ᵀ =
      ∑ a : Fin B, Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs M s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
    intro j
    rw [gs_age, Matrix.transpose_sum, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.transpose_smul, Muon.outer, Matrix.transpose_vecMulVec, Matrix.mul_smul,
      Matrix.mul_vecMulVec]
    ext i k
    simp [Matrix.vecMulVec_apply, Xs, Matrix.mulVec_mulVec, Muon.outer]
    ring
  simpa only [hterm] using hmul'

private lemma gs_L1 {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig) (s' : ℤ) (a : Fin B) :
    Integrable (fun ω => |resid F.A (S.zw s' a ω)| * eucNorm (momU F.C B (S.zw s' a ω)) *
      eucNorm (momV F.C B (S.zw s' a ω))) P ∧
    ∫ ω, |resid F.A (S.zw s' a ω)| * eucNorm (momU F.C B (S.zw s' a ω)) *
      eucNorm (momV F.C B (S.zw s' a ω)) ∂P ≤ 7 * CSig * γ := by
  set q : Vec m × Vec n → ℝ := fun x => |resid F.A x| * eucNorm (momU F.C B x) *
    eucNorm (momV F.C B x) with hq
  have hqm : Measurable q := by
    simp only [hq, resid, eucNorm, momU, momV]
    fun_prop
  have hq2 := lem_app_de_moments_iii F.C B γ CSig hdim hγ hC F.A F.hA
  have hmem : MemLp q 2 (gaussPair m n) := lt_of_le_of_lt hq2.1 ENNReal.ofReal_lt_top
  have hzw : P.map (S.zw s' a) = gaussPair m n := S.law s' a
  have hqz : MemLp (fun ω => q (S.zw s' a ω)) 2 P := by
    exact MemLp.comp_of_map (g := q) (by rw [hzw]; exact hmem) (S.meas s' a).aemeasurable
  have hint : Integrable (fun ω => q (S.zw s' a ω)) P := hqz.integrable one_le_two
  refine ⟨hint, ?_⟩
  have h1 : ∫ ω, q (S.zw s' a ω) ∂P = ∫ x, q x ∂(gaussPair m n) := by
    rw [← hzw, integral_map (S.meas s' a).aemeasurable hqm.aestronglyMeasurable]
  show ∫ ω, q (S.zw s' a ω) ∂P ≤ _
  rw [h1]
  have hq0 : ∀ x, 0 ≤ q x := fun x =>
    mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hl1 : eLpNorm q 1 (gaussPair m n) ≤ ENNReal.ofReal (7 * CSig * γ) := by
    refine (eLpNorm_le_eLpNorm_of_exponent_le one_le_two).trans ?_
    exact hq2.1.trans (ENNReal.ofReal_le_ofReal hq2.2)
  have hCS0 : 0 ≤ CSig := (pj_opNorm_nonneg _).trans hC.1
  have hnn : 0 ≤ 7 * CSig * γ := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hq0) hqm.aestronglyMeasurable]
  have h2 : ∫⁻ x, ENNReal.ofReal (q x) ∂(gaussPair m n) = eLpNorm q 1 (gaussPair m n) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hq0 x)]
    all_goals exact hqm.aestronglyMeasurable
  rw [h2]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl1).trans_eq (ENNReal.toReal_ofReal hnn)

private lemma gs_entry_le {a b : ℕ} (K : Mat a b) (x : Vec b) (i : Fin a) :
    |(K *ᵥ x) i| ≤ opNorm K * eucNorm x := by
  have h := pj_sq_mulVec K x
  have h1 : (K *ᵥ x) i ^ 2 ≤ ∑ k, (K *ᵥ x) k ^ 2 :=
    Finset.single_le_sum (f := fun k => (K *ᵥ x) k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := Real.abs_le_sqrt (h1.trans h)
  refine h2.trans ?_
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pj_opNorm_nonneg _)]
  rfl

private lemma gs_coord_le {b : ℕ} (x : Vec b) (i : Fin b) : |x i| ≤ eucNorm x := by
  have h1 : x i ^ 2 ≤ ∑ k, x k ^ 2 :=
    Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  exact Real.abs_le_sqrt h1

private lemma gs_Xs_meas {m n : ℕ} (s : ℝ) : Measurable (fun M : Mat m n => Xs M s) := by
  have hRm : Measurable (fun M : Mat m n => Rs M s) := pj_Rs_measurable s
  refine measurable_pi_iff.2 fun j => measurable_pi_iff.2 fun i => ?_
  simp only [Xs, Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp hRm)).mul
      ((measurable_pi_apply i).comp ((measurable_pi_apply k).comp measurable_id))

private lemma gs_mean {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig) (i k : Fin m) :
    ∫ ω, ((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) i k ∂P =
      ∑' j : ℕ, ∫ ω, (∑ a : Fin B, Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k ∂P := by
  have hWB := pj_meas_WB w F S t
  have hXm : Measurable (fun ω => Xs (WeightedBuf w F S t ω) s) := (gs_Xs_meas s).comp hWB
  have hw0 := hw.1.1
  have hCS0 : 0 ≤ CSig := (pj_opNorm_nonneg _).trans hC.1
  set Fj : ℕ → Ω' → ℝ := fun j ω => (∑ a : Fin B, Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k with hFj
  set qa : ℕ → Fin B → Ω' → ℝ := fun j a ω =>
    |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * eucNorm (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) *
      eucNorm (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) with hqa
  have hL1 := fun j a => gs_L1 P F S γ CSig hdim hγ hC (t + 1 - (j : ℤ)) a
  have hbd : ∀ j ω, |Fj j ω| ≤ ∑ a : Fin B, w j * qa j a ω / (2 * Real.sqrt s) := by
    intro j ω
    simp only [hFj, Matrix.sum_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, hqa]
    set X := Xs (WeightedBuf w F S t ω) s
    set v := momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)
    set u := momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)
    have h1 := gs_entry_le X v i
    have h2 := gs_coord_le u k
    have h3 : opNorm X ≤ 1 / (2 * Real.sqrt s) := (lem_app_de_resolvent _ s hs).2.2.1
    have hs2 : 0 < 2 * Real.sqrt s := by positivity
    have hX0 := pj_opNorm_nonneg X
    have hv0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
    have hu0 : 0 ≤ eucNorm u := Real.sqrt_nonneg _
    rw [abs_mul, abs_mul, abs_mul]
    have hwj := hw0 j
    rw [abs_of_nonneg hwj]
    calc w j * |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * |(X *ᵥ v) i| * |u k|
        ≤ w j * |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * (1 / (2 * Real.sqrt s) * eucNorm v) *
            eucNorm u := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans
            (mul_le_mul_of_nonneg_right h3 hv0)) (by positivity)) h2 (abs_nonneg _) (by positivity)
      _ = w j * (|resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * eucNorm u * eucNorm v) /
            (2 * Real.sqrt s) := by
          field_simp
  have hdm : ∀ j a, Measurable (fun ω => resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) := fun j a =>
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp (S.meas _ _)
  have hum : ∀ j a, Measurable (fun ω => momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := fun j a =>
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp (S.meas _ _)
  have hvm : ∀ j a, Measurable (fun ω => momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := fun j a =>
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp (S.meas _ _)
  have hFm : ∀ j, Measurable (Fj j) := by
    intro j
    simp only [hFj, Matrix.sum_apply]
    refine Finset.measurable_sum _ fun a _ => ?_
    simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    refine (measurable_const.mul (hdm j a)).mul ?_ |>.mul ((measurable_pi_apply k).comp (hum j a))
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hXm)).mul
        ((measurable_pi_apply l).comp (hvm j a))
  have hgi : ∀ j, Integrable (fun ω => ∑ a : Fin B, w j * qa j a ω / (2 * Real.sqrt s)) P := by
    intro j
    exact integrable_finsetSum _ fun a _ => (((hL1 j a).1).const_mul (w j)).div_const _
  have hint : ∀ j, Integrable (Fj j) P := fun j =>
    (hgi j).mono' (hFm j).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hbd j ω)
  have hnormle : ∀ j, ∫ ω, ‖Fj j ω‖ ∂P ≤ (B * (7 * CSig * γ) / (2 * Real.sqrt s)) * w j := by
    intro j
    calc ∫ ω, ‖Fj j ω‖ ∂P ≤ ∫ ω, ∑ a : Fin B, w j * qa j a ω / (2 * Real.sqrt s) ∂P :=
          integral_mono (hint j).norm (hgi j) fun ω => by
            rw [Real.norm_eq_abs]; exact hbd j ω
      _ = ∑ a : Fin B, w j * (∫ ω, qa j a ω ∂P) / (2 * Real.sqrt s) := by
          rw [integral_finsetSum _ fun a _ => (((hL1 j a).1).const_mul (w j)).div_const _]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_div, integral_const_mul]
      _ ≤ ∑ a : Fin B, w j * (7 * CSig * γ) / (2 * Real.sqrt s) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hL1 j a).2 (hw0 j))
            (by positivity)
      _ = (B * (7 * CSig * γ) / (2 * Real.sqrt s)) * w j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsum : Summable fun j => ∫ ω, ‖Fj j ω‖ ∂P :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => norm_nonneg _) hnormle
      (hw.1.2.1.mul_left _)
  rw [integral_tsum_of_summable_integral_norm hint hsum]
  refine integral_congr_ae ?_
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := gs_series w F S t s hs ω (hω t)
  have h' : HasSum (fun j => Fj j ω) (((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) i k) := by
    let f : Mat m m →+ ℝ := { toFun := fun X => X i k, map_zero' := rfl, map_add' := fun _ _ => rfl }
    exact h.map f ((continuous_apply k).comp (continuous_apply i))
  exact h'.tsum_eq.symm

private lemma gs_T_int {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig) (i k : Fin m) (j : ℕ) (a : Fin B) :
    Integrable (fun ω => (Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k) P := by
  have hWB := pj_meas_WB w F S t
  have hXm : Measurable (fun ω => Xs (WeightedBuf w F S t ω) s) := (gs_Xs_meas s).comp hWB
  have hw0 := hw.1.1
  have hL1 := (gs_L1 P F S γ CSig hdim hγ hC (t + 1 - (j : ℤ)) a).1
  have hdm : Measurable (fun ω => resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp (S.meas _ _)
  have hum : Measurable (fun ω => momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp (S.meas _ _)
  have hvm : Measurable (fun ω => momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp (S.meas _ _)
  have hm : Measurable (fun ω => (Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k) := by
    simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    refine (measurable_const.mul hdm).mul ?_ |>.mul ((measurable_pi_apply k).comp hum)
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hXm)).mul
        ((measurable_pi_apply l).comp hvm)
  refine (hL1.const_mul (w j / (2 * Real.sqrt s))).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  set X := Xs (WeightedBuf w F S t ω) s
  set v := momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)
  set u := momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)
  have h1 := gs_entry_le X v i
  have h2 := gs_coord_le u k
  have h3 : opNorm X ≤ 1 / (2 * Real.sqrt s) := (lem_app_de_resolvent _ s hs).2.2.1
  have hs2 : 0 < 2 * Real.sqrt s := by positivity
  have hX0 := pj_opNorm_nonneg X
  have hv0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
  have hu0 : 0 ≤ eucNorm u := Real.sqrt_nonneg _
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (hw0 j)]
  calc w j * |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * |(X *ᵥ v) i| * |u k|
      ≤ w j * |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * (1 / (2 * Real.sqrt s) * eucNorm v) *
          eucNorm u := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (h1.trans
          (mul_le_mul_of_nonneg_right h3 hv0)) (by have := hw0 j; positivity)) h2 (abs_nonneg _)
          (by have := hw0 j; positivity)
    _ = w j / (2 * Real.sqrt s) * (|resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * eucNorm u * eucNorm v) := by
        field_simp

private lemma gs_slot {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) (j : ℕ)
    (G : Mat m n × (Vec m × Vec n) → Mat m m)
    (hGm : ∀ i k, Measurable fun q => G q i k)
    (hG : ∀ M0 p, G (M0, p) = Muon.outer
      ((-(alpha3 M0 (w j * resid F.A p) (momU F.C B p) (momV F.C B p) s)) •
          (Rs M0 s *ᵥ momU F.C B p) +
        (alpha1 M0 (w j * resid F.A p) (momU F.C B p) (momV F.C B p) s) •
          (Xs M0 s *ᵥ momV F.C B p)) (momU F.C B p)) (a : Fin B) (i k : Fin m) :
    ∫ ω, (Muon.outer
        ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k ∂P =
      ∫ ω, G (WeightedBufDel w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) ω,
        S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) i k ∂P := by
  set s' : ℤ := t + 1 - (j : ℤ) with hs'
  have hpair : ∀ b : Fin B, Measurable (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω)) :=
    fun b => (pj_meas_del w F S t s' b).prodMk (S.meas _ _)
  have step1 : ∀ b : Fin B, ∫ ω, (Muon.outer
        ((w j * resid F.A (S.zw s' b ω)) •
          (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw s' b ω)))
        (momU F.C B (S.zw s' b ω))) i k ∂P =
      ∫ ω, G (WeightedBufDel w F S t s' b ω, S.zw s' b ω) i k ∂P := by
    intro b
    refine integral_congr_ae ?_
    filter_upwards [pj_decomp w hw F S t j b] with ω hω
    rw [hG]
    obtain ⟨-, -, h3, -, -⟩ := lem_app_de_deletion (WeightedBufDel w F S t s' b ω)
      (w j * resid F.A (S.zw s' b ω)) (momU F.C B (S.zw s' b ω)) (momV F.C B (S.zw s' b ω))
      (WeightedBuf w F S t ω) s hω hs
    have e : (w j * resid F.A (S.zw s' b ω)) •
        (Xs (WeightedBuf w F S t ω) s *ᵥ momV F.C B (S.zw s' b ω)) =
        (-(alpha3 (WeightedBufDel w F S t s' b ω) (w j * resid F.A (S.zw s' b ω))
          (momU F.C B (S.zw s' b ω)) (momV F.C B (S.zw s' b ω)) s)) •
          (Rs (WeightedBufDel w F S t s' b ω) s *ᵥ momU F.C B (S.zw s' b ω)) +
        (alpha1 (WeightedBufDel w F S t s' b ω) (w j * resid F.A (S.zw s' b ω))
          (momU F.C B (S.zw s' b ω)) (momV F.C B (S.zw s' b ω)) s) •
          (Xs (WeightedBufDel w F S t s' b ω) s *ᵥ momV F.C B (S.zw s' b ω)) := by
      rw [← h3, Xs, ← Matrix.mulVec_mulVec]
    rw [e]
  have step2 : ∀ b : Fin B, ∫ ω, G (WeightedBufDel w F S t s' b ω, S.zw s' b ω) i k ∂P =
      ∫ q, G q i k ∂(P.map (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω))) := by
    intro b
    rw [integral_map (hpair b).aemeasurable (hGm i k).aestronglyMeasurable]
  rw [step1 a, step2 a, weightedBufDel_law_slot_invariant w hw F S t s' a (slotOne F.hB),
    ← step2 (slotOne F.hB)]

private lemma gs_step1 {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig)
    (G : ℕ → Mat m n × (Vec m × Vec n) → Mat m m)
    (hGm : ∀ j i k, Measurable fun q => G j q i k)
    (hG : ∀ j M0 p, G j (M0, p) = Muon.outer
      ((-(alpha3 M0 (w j * resid F.A p) (momU F.C B p) (momV F.C B p) s)) •
          (Rs M0 s *ᵥ momU F.C B p) +
        (alpha1 M0 (w j * resid F.A p) (momU F.C B p) (momV F.C B p) s) •
          (Xs M0 s *ᵥ momV F.C B p)) (momU F.C B p)) (i k : Fin m) :
    ∫ ω, ((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) i k ∂P =
      ∑' j : ℕ, (B : ℝ) * ∫ ω, G j (WeightedBufDel w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) ω,
        S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) i k ∂P := by
  rw [gs_mean P w hw F S t hs γ CSig hdim hγ hC i k]
  refine tsum_congr fun j => ?_
  simp only [Matrix.sum_apply]
  rw [integral_finsetSum _ fun a _ => gs_T_int P w hw F S t hs γ CSig hdim hγ hC i k j a]
  rw [Finset.sum_congr rfl fun a _ => gs_slot P w hw F S t hs j (G j) (hGm j) (hG j) a i k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

private lemma gs_G_meas {m n B : ℕ} (C : Covariances m n) (A : Mat m n) (s hj : ℝ) :
    ∀ i k : Fin m, Measurable fun q : Mat m n × (Vec m × Vec n) => (Muon.outer
      ((-(alpha3 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s)) •
          (Rs q.1 s *ᵥ momU C B q.2) +
        (alpha1 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) •
          (Xs q.1 s *ᵥ momV C B q.2)) (momU C B q.2)) i k := by
  intro i k
  have hR : Measurable (fun q : Mat m n × (Vec m × Vec n) => Rs q.1 s) :=
    (pj_Rs_measurable s).comp measurable_fst
  have hRt : Measurable (fun q : Mat m n × (Vec m × Vec n) => Rts q.1 s) := by
    have hc : Continuous (fun M : Mat m n => Mᵀ * M + s • (1 : Mat n n)) := by fun_prop
    exact (pj_inv_measurable (a := n)).comp (hc.measurable.comp measurable_fst)
  have hX : Measurable (fun q : Mat m n × (Vec m × Vec n) => Xs q.1 s) :=
    (gs_Xs_meas s).comp measurable_fst
  have hu : Measurable (fun q : Mat m n × (Vec m × Vec n) => momU C B q.2) :=
    (by unfold momU; fun_prop : Measurable (momU C B)).comp measurable_snd
  have hv : Measurable (fun q : Mat m n × (Vec m × Vec n) => momV C B q.2) :=
    (by unfold momV; fun_prop : Measurable (momV C B)).comp measurable_snd
  have hd : Measurable (fun q : Mat m n × (Vec m × Vec n) => hj * resid A q.2) :=
    measurable_const.mul ((by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid A x).comp measurable_snd)
  have hmv : ∀ {a b : ℕ} (K : Mat m n × (Vec m × Vec n) → Mat a b) (x : Mat m n × (Vec m × Vec n) → Vec b),
      Measurable K → Measurable x → Measurable (fun q => K q *ᵥ x q) := by
    intro a b K x hK hx
    refine measurable_pi_iff.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hK)).mul
        ((measurable_pi_apply l).comp hx)
  have hdot : ∀ {a : ℕ} (x y : Mat m n × (Vec m × Vec n) → Vec a), Measurable x → Measurable y →
      Measurable (fun q => dotProduct (x q) (y q)) := by
    intro a x y hx hy
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp hx).mul ((measurable_pi_apply l).comp hy)
  have hU : Measurable (fun q : Mat m n × (Vec m × Vec n) => delU q.1 (momU C B q.2) s) :=
    hdot _ _ hu (hmv _ _ hR hu)
  have hV : Measurable (fun q : Mat m n × (Vec m × Vec n) => delV q.1 (momV C B q.2) s) :=
    hdot _ _ hv (hmv _ _ hRt hv)
  have hCc : Measurable (fun q : Mat m n × (Vec m × Vec n) => delC q.1 (momU C B q.2) (momV C B q.2) s) :=
    hdot _ _ hu (hmv _ _ hX hv)
  have hL : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      delLambda q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) := by
    unfold delLambda
    exact ((measurable_const.add (hd.mul hCc)).pow_const 2).add
      (((measurable_const.mul (hd.pow_const 2)).mul hU).mul hV)
  have h1 : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      alpha1 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) := by
    unfold alpha1
    exact (hd.mul (measurable_const.add (hd.mul hCc))).div hL
  have h3 : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      alpha3 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) := by
    unfold alpha3
    exact (((measurable_const.mul (hd.pow_const 2)).mul hV).neg).div hL
  simp only [Muon.outer, Matrix.vecMulVec_apply]
  refine Measurable.mul ?_ ((measurable_pi_apply k).comp hu)
  have hsum : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      (-(alpha3 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s)) •
          (Rs q.1 s *ᵥ momU C B q.2) +
        (alpha1 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) •
          (Xs q.1 s *ᵥ momV C B q.2)) :=
    (h3.neg.smul (hmv _ _ hR hu)).add (h1.smul (hmv _ _ hX hv))
  exact (measurable_pi_apply i).comp hsum

/-! ### Independence factorization and the algebra of the deleted-sample term -/

private lemma gc_fact_scalar {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {m n : ℕ} (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n)
    (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (f : Mat m n → ℝ) (g : Vec m × Vec n → ℝ) (hf : Measurable f) (hg : Measurable g) :
    ∫ ω, f (M0 ω) * g (zw ω) ∂P = (∫ ω, f (M0 ω) ∂P) * ∫ p, g p ∂(gaussPair m n) := by
  have hpair : Measurable (fun ω => (M0 ω, zw ω)) := hM0.prodMk hzw
  have h1 : ∫ ω, f (M0 ω) * g (zw ω) ∂P =
      ∫ q, f q.1 * g q.2 ∂((P.map M0).prod (gaussPair m n)) := by
    rw [← hmap, integral_map hpair.aemeasurable]
    exact ((hf.comp measurable_fst).mul (hg.comp measurable_snd)).aestronglyMeasurable
  have h2 : ∫ ω, f (M0 ω) ∂P = ∫ x, f x ∂(P.map M0) := by
    rw [integral_map hM0.aemeasurable hf.aestronglyMeasurable]
  rw [h1, h2]
  haveI : IsProbabilityMeasure (P.map M0) :=
    ⟨by rw [Measure.map_apply hM0 MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩
  exact integral_prod_mul f g

private lemma gs_G_alg {m n : ℕ} (R : Mat m m) (X' : Mat m n) (c3 c1 : ℝ) (u : Vec m) (v : Vec n) :
    Muon.outer (c3 • (R *ᵥ u) + c1 • (X' *ᵥ v)) u =
      c3 • (R * Muon.outer u u) + c1 • (X' * Muon.outer v u) := by
  ext i k
  simp only [Muon.outer, Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.add_apply, Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [add_mul, Finset.sum_mul, Finset.sum_mul]
  congr 1 <;> exact Finset.sum_congr rfl fun _ _ => by ring

/-! ### The transposed model (input side) -/

private lemma gt_fro_transpose {m n : ℕ} (A : Mat m n) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  rw [Finset.sum_comm]
  simp

private lemma gt_exists {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    ∃ (F' : FrozenParams n m B) (S' : FrozenSamples P n m B),
      F'.C.Sout = F.C.Sin ∧ F'.C.Sin = F.C.Sout ∧ F'.A = F.Aᵀ ∧ F'.β = F.β ∧
      (∀ s a ω, (S'.zw s a ω) = ((S.zw s a ω).2, (S.zw s a ω).1)) ∧
      (∀ (w : ℕ → ℝ) (t : ℤ) ω, WeightedBuf w F' S' t ω = (WeightedBuf w F S t ω)ᵀ) ∧
      (∀ (w : ℕ → ℝ) (t s : ℤ) (a : Fin B) ω,
        WeightedBufDel w F' S' t s a ω = (WeightedBufDel w F S t s a ω)ᵀ) := by
  have hsym : ∀ {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ), (CFC.sqrt X)ᵀ = CFC.sqrt X :=
    fun X => pj_sqrt_symm X
  let F' : FrozenParams n m B :=
    ⟨⟨F.C.Sin, F.C.Sout, F.C.psdIn, F.C.psdOut⟩, F.Aᵀ, by rw [gt_fro_transpose]; exact F.hA,
      F.β, F.hβ, F.hB⟩
  let S' : FrozenSamples P n m B :=
    ⟨fun s a ω => ((S.zw s a ω).2, (S.zw s a ω).1),
      fun s a => measurable_swap.comp (S.meas s a),
      S.indep.comp (fun _ => Prod.swap) (fun _ => measurable_swap),
      fun s a => by
        have h1 : (fun ω => ((S.zw s a ω).2, (S.zw s a ω).1)) = Prod.swap ∘ S.zw s a := rfl
        rw [h1, ← Measure.map_map measurable_swap (S.meas s a), S.law, Measure.prod_swap]⟩
  have hT : ∀ s a ω, sampleTerm F' S' s a ω = (sampleTerm F S s a ω)ᵀ := by
    intro s a ω
    unfold sampleTerm
    rw [Matrix.transpose_smul]
    have hd : dotProduct (S'.zw s a ω).1 (Matrix.mulVec F'.A (S'.zw s a ω).2) =
        dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2) := by
      change dotProduct (S.zw s a ω).2 (Matrix.mulVec F.Aᵀ (S.zw s a ω).1) = _
      rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec]
    rw [hd]
    congr 1
    change rOut F'.C * outer (S.zw s a ω).2 (S.zw s a ω).1 * rIn F'.C =
      (rOut F.C * outer (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C)ᵀ
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_vecMulVec]
    have e1 : (rIn F.C)ᵀ = rIn F.C := hsym _
    have e2 : (rOut F.C)ᵀ = rOut F.C := hsym _
    rw [e1, e2, Matrix.mul_assoc]
    rfl
  have hG : ∀ s ω, frozenBatchG F' S' s ω = (frozenBatchG F S s ω)ᵀ := by
    intro s ω
    rw [frozenBatchG_eq_sum, frozenBatchG_eq_sum, Matrix.transpose_smul, Matrix.transpose_sum]
    congr 1
    exact Finset.sum_congr rfl fun a _ => hT s a ω
  refine ⟨F', S', rfl, rfl, rfl, rfl, fun _ _ _ => rfl, ?_, ?_⟩
  · intro w t ω
    unfold WeightedBuf
    rw [Matrix.transpose_tsum]
    refine tsum_congr fun j => ?_
    rw [hG, Matrix.transpose_smul]
  · intro w t s a ω
    unfold WeightedBufDel
    rw [Matrix.transpose_tsum]
    refine tsum_congr fun j => ?_
    rw [Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_sum]
    congr 2
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · simp
    · exact hT _ b ω

private lemma gt_Rs {m n : ℕ} (M : Mat m n) (s : ℝ) : Rs Mᵀ s = Rts M s := by
  unfold Rs Rts
  rw [Matrix.transpose_transpose]

private lemma gram_hPjT (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k (j : ℕ), ∀ s ∈ I,
      opNorm (expResT w (R.F k) (S k) t s - Muon.mean (P k) (fun ω =>
        Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s)) ≤
          C * w j / (R.B k : ℝ) := by
  set γ' : ℝ := max R.γstar 1 with hγ'
  obtain ⟨C, hC0, hCP⟩ := eqn_app_de_Pj_P I hI hIpos R.CSig γ'
  have hdm : ∀ k, (R.m k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_left _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  have hdn : ∀ k, (R.n k : ℝ) ≤ γ' * (R.B k : ℝ) := fun k =>
    (le_trans (Nat.cast_le.mpr (le_max_right _ _)) (R.dims k)).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Nat.cast_nonneg _))
  choose F' S' hSo hSi hA hβ hz hWB hWD using fun k => gt_exists (R.F k) (S k)
  refine ⟨C, hC0, fun k j s hs => ?_⟩
  have h := hCP (R.n k) (R.m k) (R.B k) w hw (Ω k) (P k) (F' k) (S' k) t
    (by rw [hSo k]; exact R.normIn k) (by rw [hSi k]; exact R.normOut k) (hdn k) (hdm k) j
    (slotOne (R.F k).hB) s hs
  have e1 : expRes w (F' k) (S' k) t s = expResT w (R.F k) (S k) t s := by
    unfold expRes expResT
    congr 1
    funext ω
    rw [hWB, gt_Rs]
  have e2 : expDelRes w (F' k) (S' k) t j (slotOne (R.F k).hB) s = Muon.mean (P k) (fun ω =>
        Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s) := by
    unfold expDelRes
    congr 1
    funext ω
    rw [hWD, gt_Rs]
  rw [e1, e2] at h
  exact h

private lemma gt_Rts {m n : ℕ} (M : Mat m n) (s : ℝ) : Rts Mᵀ s = Rs M s := by
  unfold Rs Rts
  rw [Matrix.transpose_transpose]

private lemma gt_scalars {Ω' : Type} [MeasurableSpace Ω'] {P : Measure Ω'} {m n B : ℕ}
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (F' : FrozenParams n m B) (S' : FrozenSamples P n m B) (t : ℤ) (s : ℝ)
    (hSo : F'.C.Sout = F.C.Sin) (hSi : F'.C.Sin = F.C.Sout)
    (hWB : ∀ ω, WeightedBuf w F' S' t ω = (WeightedBuf w F S t ω)ᵀ) :
    expRes w F' S' t s = expResT w F S t s ∧ sigmaTildeB w F' S' t s = sigmaB w F S t s ∧
      sigmaB w F' S' t s = sigmaTildeB w F S t s ∧ qB w F' S' t s = qB w F S t s := by
  have e1 : expRes w F' S' t s = expResT w F S t s := by
    unfold expRes expResT
    congr 1
    funext ω
    rw [hWB, gt_Rs]
  have e2 : expResT w F' S' t s = expRes w F S t s := by
    unfold expRes expResT
    congr 1
    funext ω
    rw [hWB, gt_Rts]
  have e3 : sigmaTildeB w F' S' t s = sigmaB w F S t s := by
    unfold sigmaTildeB sigmaB
    rw [e2, hSi]
  have e4 : sigmaB w F' S' t s = sigmaTildeB w F S t s := by
    unfold sigmaTildeB sigmaB
    rw [e1, hSo]
  refine ⟨e1, e3, e4, ?_⟩
  unfold qB
  rw [e3, e4]
  ring

private lemma gram_hIII (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w) (I : Set ℝ)
    (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    ∀ 𝔟 : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ ν ν' : FiniteMeasure ℝ,
      (ν, ν') ∈ classK R.CSig (max R.γstar 1) →
      ∀ s ∈ I, ∀ u v a c : ℝ, u ∈ Icc 0 𝔟 → v ∈ Icc 0 𝔟 → a ∈ Icc 0 𝔟 → c ∈ Icc 0 𝔟 →
        |u - ∫ t, t / (s + a * t) ∂(ν : Measure ℝ)| ≤ δ →
        |v - ∫ t, t / (s + c * t) ∂(ν' : Measure ℝ)| ≤ δ →
        |a - s * v * Fw w (s * u * v)| ≤ δ →
        |c - s * u * Fw w (s * u * v)| ≤ δ →
        |u - (branchSol (Fw w) ν ν' s).1| + |v - (branchSol (Fw w) ν ν' s).2.1| +
          |a - (branchSol (Fw w) ν ν' s).2.2.1| + |c - (branchSol (Fw w) ν ν' s).2.2.2| ≤ ε :=
  fun 𝔟 => thm_app_de_branch_iii (Fw_admissible hw.1) (lt_of_lt_of_le one_pos R.hC)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) hI hIpos (𝔟 := 𝔟)

private lemma gram_hS13i (w : ℕ → ℝ) (t : ℤ) (I : Set ℝ)
    (H : ∀ (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)),
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s * (R.F k).C.Sout)) ≤ ε)
    (R : SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) :
    ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.n k) (R.n k)) - s • expResT w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (Muon.mean (P k) (fun ω =>
            Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s) *
            (R.F k).C.Sin)) ≤ ε := by
  choose F' S' hSo hSi hAF hβF hz hWB hWD using fun k => gt_exists (R.F k) (S k)
  let R' : SetupRegime :=
    { m := R.n, n := R.m, B := R.B, F := F'
      prop :=
        { γin := R.prop.γout, γout := R.prop.γin, γin_pos := R.prop.γout_pos,
          γout_pos := R.prop.γin_pos, B_top := R.prop.B_top,
          ratio_in := R.prop.ratio_out, ratio_out := R.prop.ratio_in,
          bdd := by
            obtain ⟨c, hc, h⟩ := R.prop.bdd
            exact ⟨c, hc, fun k => by
              show opNorm (F' k).C.Sin ≤ c ∧ opNorm (F' k).C.Sout ≤ c
              rw [hSo k, hSi k]; exact ⟨(h k).2, (h k).1⟩⟩ }
      γstar := R.γstar, CSig := R.CSig, hC := R.hC
      dims := fun k => by rw [max_comm]; exact R.dims k
      normOut := fun k => by
        show opNorm (F' k).C.Sout ≤ R.CSig
        rw [hSo k]; exact R.normIn k
      normIn := fun k => by
        show opNorm (F' k).C.Sin ≤ R.CSig
        rw [hSi k]; exact R.normOut k
      β := R.β
      hβ := fun k => by
        show (F' k).β = R.β
        rw [hβF k]; exact R.hβ k
      ϱlo := R.ϱlo, ϱhi := R.ϱhi, hϱ := R.hϱ
      diffuse := by
        have : (fun k => opNorm (F' k).A) = fun k => opNorm (R.F k).A := by
          funext k; rw [hAF k, pj_opNorm_transpose]
        show Tendsto (fun k => opNorm (F' k).A) atTop (𝓝 0)
        rw [this]; exact R.diffuse }
  intro ε hε
  filter_upwards [H R' Ω P S' ε hε] with k hk s hs
  have h := hk s hs
  obtain ⟨e1, e3, e4, e5⟩ := gt_scalars w (R.F k) (S k) (F' k) (S' k) t s (hSo k) (hSi k) (hWB k w t)
  have e2 : ∀ j, expDelRes w (F' k) (S' k) t j (slotOne (R.F k).hB) s = Muon.mean (P k) (fun ω =>
        Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s) := by
    intro j
    unfold expDelRes
    congr 1
    funext ω
    rw [hWD, gt_Rs]
  have h' := h
  change opNorm ((1 : Mat (R.n k) (R.n k)) - s • expRes w (F' k) (S' k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (F' k) (S' k) t s *
            J (w j ^ 2 * qB w (F' k) (S' k) t s)) •
          (expDelRes w (F' k) (S' k) t j (slotOne (R.F k).hB) s * (F' k).C.Sout)) ≤ ε at h'
  simp only [e1, e3, e5, e2, hSo k] at h'
  exact h'

/-- Assembly of the Step 4 glue and the Step 5 reduction: the theorem follows from the branch
stability `thm_app_de_branch_iii` (`hIII`), the input-side replacement `P̃_j → P̃` (`hPjT`) and
the Step 1–3 closure bounds `hS13o`, `hS13i` (with `P_j` and the series over ages). -/
private lemma gram_of_step13 (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0)
    (hIII : ∀ 𝔟 : ℝ, ∀ ε > 0, ∃ δ > 0, ∀ ν ν' : FiniteMeasure ℝ,
      (ν, ν') ∈ classK R.CSig (max R.γstar 1) →
      ∀ s ∈ I, ∀ u v a c : ℝ, u ∈ Icc 0 𝔟 → v ∈ Icc 0 𝔟 → a ∈ Icc 0 𝔟 → c ∈ Icc 0 𝔟 →
        |u - ∫ t, t / (s + a * t) ∂(ν : Measure ℝ)| ≤ δ →
        |v - ∫ t, t / (s + c * t) ∂(ν' : Measure ℝ)| ≤ δ →
        |a - s * v * Fw w (s * u * v)| ≤ δ →
        |c - s * u * Fw w (s * u * v)| ≤ δ →
        |u - (branchSol (Fw w) ν ν' s).1| + |v - (branchSol (Fw w) ν ν' s).2.1| +
          |a - (branchSol (Fw w) ν ν' s).2.2.1| + |c - (branchSol (Fw w) ν ν' s).2.2.2| ≤ ε)
    (hPjT : ∃ C : ℝ, 0 ≤ C ∧ ∀ k (j : ℕ), ∀ s ∈ I,
      opNorm (expResT w (R.F k) (S k) t s - Muon.mean (P k) (fun ω =>
        Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s)) ≤
          C * w j / (R.B k : ℝ))
    (hS13o : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s * (R.F k).C.Sout)) ≤ ε)
    (hS13i : ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.n k) (R.n k)) - s • expResT w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (Muon.mean (P k) (fun ω =>
            Rts (WeightedBufDel w (R.F k) (S k) t (t + 1 - (j : ℤ)) (slotOne (R.F k).hB) ω) s) *
            (R.F k).C.Sin)) ≤ ε) :
    Tendsto (fun k => ⨆ s ∈ I,
      (opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)))
      atTop (𝓝 0) :=
  gram_reduce R w hw P S νo νi hνo hνi t I hI hIpos hIII
    (gram_hEo R w hw P S t I hI hIpos hS13o) (gram_hEi R w hw P S t I hI hIpos hPjT hS13i)

/-- The theorem from the single remaining statement `H` (Steps 1-3 of the paper's proof, output
side, for every regime): everything else (input side by transposition, Step 4 glue, Step 5) is
proved above. -/
private lemma gram_of_H (w : ℕ → ℝ) (hw : WeightClass w) (t : ℤ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0)
    (H : ∀ (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)),
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s * (R.F k).C.Sout)) ≤ ε)
    (R : SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k)) :
    Tendsto (fun k => ⨆ s ∈ I,
      (opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)))
      atTop (𝓝 0) :=
  gram_of_step13 R w hw P S νo νi hνo hνi t I hI hIpos (gram_hIII R w hw I hI hIpos)
    (gram_hPjT R w hw P S t I hI hIpos) (H R Ω P S) (gram_hS13i w t I H R P S)

/-! ### Per-age assembly of Steps 2-3 -/

private lemma gh_bilin_le {a b : ℕ} (K : Mat a b) (x : Vec a) (y : Vec b) :
    |dotProduct x (K *ᵥ y)| ≤
      opNorm K * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2) := by
  have hS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x (fun i => (K *ᵥ y) i)
  have h2 := pj_sq_mulVec K y
  have hn := pj_opNorm_nonneg K
  have hx0 : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ i, y i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hd : (dotProduct x (K *ᵥ y)) ^ 2 ≤ (∑ i, x i ^ 2) * (opNorm K ^ 2 * ∑ i, y i ^ 2) := by
    refine le_trans (by simpa [dotProduct] using hS) ?_
    exact mul_le_mul_of_nonneg_left h2 hx0
  calc |dotProduct x (K *ᵥ y)| = Real.sqrt ((dotProduct x (K *ᵥ y)) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, x i ^ 2) * (opNorm K ^ 2 * ∑ i, y i ^ 2)) := Real.sqrt_le_sqrt hd
    _ = _ := by
        rw [Real.sqrt_mul hx0, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hn]; ring

private lemma gh_bilin_int {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {a b : ℕ} (D : Ω' → Mat a b)
    (hint : ∀ i k, Integrable (fun ω => D ω i k) P) (xv : Vec a) (yv : Vec b) :
    dotProduct xv ((Matrix.of fun i k => ∫ ω, D ω i k ∂P) *ᵥ yv)
      = ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P := by
  have hin : ∀ i, Integrable (fun ω => xv i * ∑ k, D ω i k * yv k) P := fun i =>
    ((integrable_finsetSum _ fun k _ => (hint i k).mul_const (yv k))).const_mul (xv i)
  have h1 : ∫ ω, dotProduct xv (D ω *ᵥ yv) ∂P = ∑ i, ∫ ω, xv i * ∑ k, D ω i k * yv k ∂P := by
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct]
    exact integral_finsetSum _ fun i _ => hin i
  rw [h1]
  unfold dotProduct Matrix.mulVec
  simp only [Matrix.of_apply, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, integral_finsetSum _ fun k _ => (hint i k).mul_const (yv k)]
  congr 1
  exact Finset.sum_congr rfl fun k _ => (integral_mul_const (yv k) _).symm

private lemma gh_opNorm_mean {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω')
    [IsProbabilityMeasure P] {a b : ℕ} (D : Ω' → Mat a b)
    (hint : ∀ i k, Integrable (fun ω => D ω i k) P) (c : ℝ) (hc : 0 ≤ c)
    (hD : ∀ ω, opNorm (D ω) ≤ c) : opNorm (Muon.mean P D) ≤ c := by
  refine pj_opNorm_of_bilin _ c hc fun x y => ?_
  have e : Muon.mean P D = Matrix.of fun i k => ∫ ω, D ω i k ∂P := rfl
  rw [e, gh_bilin_int P D hint x y]
  have hnorm := norm_integral_le_of_norm_le_const (μ := P)
    (f := fun ω => dotProduct x (D ω *ᵥ y))
    (C := c * Real.sqrt (∑ i, x i ^ 2) * Real.sqrt (∑ i, y i ^ 2))
    (ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs]
      refine (gh_bilin_le (D ω) x y).trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD ω) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _))
  simp only [probReal_univ, mul_one] at hnorm
  rwa [Real.norm_eq_abs] at hnorm

private lemma gh_I4_fst {m n : ℕ} (i : Fin m) :
    Integrable (fun p : Vec m × Vec n => p.1 i ^ 4) (gaussPair m n) := by
  have hm : MeasurePreserving (fun p : Vec m × Vec n => p.1 i) (gaussPair m n) (gaussianReal 0 1) := by
    have h1 : MeasurePreserving (fun z : Vec m => z i) (Muon.Foundations.stdGaussianPi m)
        (gaussianReal 0 1) := by
      unfold Muon.Foundations.stdGaussianPi
      exact measurePreserving_eval _ i
    exact h1.comp measurePreserving_fst
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 4) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 4)

private lemma gh_I4_snd {m n : ℕ} (i : Fin n) :
    Integrable (fun p : Vec m × Vec n => p.2 i ^ 4) (gaussPair m n) := by
  have hm : MeasurePreserving (fun p : Vec m × Vec n => p.2 i) (gaussPair m n) (gaussianReal 0 1) := by
    have h1 : MeasurePreserving (fun z : Vec n => z i) (Muon.Foundations.stdGaussianPi n)
        (gaussianReal 0 1) := by
      unfold Muon.Foundations.stdGaussianPi
      exact measurePreserving_eval _ i
    exact h1.comp measurePreserving_snd
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 4) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 4)

private lemma gh_int_zz {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {x : ℝ} (hx : 0 ≤ x)
    (i k : Fin m) :
    Integrable (fun p : Vec m × Vec n => psiX x (resid A p) * (p.1 i * p.1 k)) (gaussPair m n) := by
  have hcont := (gram_psi_cont hx).comp (gram_resid_cont A)
  refine Integrable.mono' (((gram_resid_pow4_int A hA).add
    (((gh_I4_fst i).add (gh_I4_fst k)).const_mul (1 / 2))).const_mul (1 / 2))
    (hcont.mul (by fun_prop : Continuous fun p : Vec m × Vec n => p.1 i * p.1 k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  show ‖psiX x (resid A p) * (p.1 i * p.1 k)‖ ≤
    1 / 2 * (resid A p ^ 4 + 1 / 2 * (p.1 i ^ 4 + p.1 k ^ 4))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := gram_psi_abs (x := x) (d := resid A p) hx
  have h3 : |psiX x (resid A p)| * |p.1 i * p.1 k| ≤ resid A p ^ 2 * |p.1 i * p.1 k| :=
    mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have h4 : resid A p ^ 2 * |p.1 i * p.1 k| ≤
      (resid A p ^ 4 + (p.1 i * p.1 k) ^ 2) / 2 := by
    have := sq_nonneg (resid A p ^ 2 - |p.1 i * p.1 k|)
    nlinarith [sq_abs (p.1 i * p.1 k)]
  have h5 : (p.1 i * p.1 k) ^ 2 ≤ (p.1 i ^ 4 + p.1 k ^ 4) / 2 := by
    nlinarith [sq_nonneg (p.1 i ^ 2 - p.1 k ^ 2)]
  nlinarith

private lemma gh_f_abs {x d : ℝ} (hx : 0 ≤ x) : |fX x d| ≤ |d| := by
  unfold fX
  rw [abs_div, abs_of_pos (gc_den_pos hx d)]
  have : 1 ≤ 1 + x * d ^ 2 := by nlinarith [mul_nonneg hx (sq_nonneg d)]
  exact div_le_self (abs_nonneg _) this

private lemma gh_f_cont {x : ℝ} (hx : 0 ≤ x) : Continuous (fX x) := by
  unfold fX
  refine Continuous.div (by fun_prop) (by fun_prop) (fun d => (gc_den_pos hx d).ne')

private lemma gh_int_wz {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {x : ℝ} (hx : 0 ≤ x)
    (i : Fin n) (k : Fin m) :
    Integrable (fun p : Vec m × Vec n => fX x (resid A p) * (p.2 i * p.1 k)) (gaussPair m n) := by
  have hcont := (gh_f_cont hx).comp (gram_resid_cont A)
  refine Integrable.mono' (((((integrable_const (1 : ℝ)).add (gram_resid_pow4_int A hA)).const_mul (1 / 2)).add
    (((gh_I4_snd i).add (gh_I4_fst k)).const_mul (1 / 2))).const_mul (1 / 2))
    (hcont.mul (by fun_prop : Continuous fun p : Vec m × Vec n => p.2 i * p.1 k)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  show ‖fX x (resid A p) * (p.2 i * p.1 k)‖ ≤
    1 / 2 * (1 / 2 * (1 + resid A p ^ 4) + 1 / 2 * (p.2 i ^ 4 + p.1 k ^ 4))
  rw [Real.norm_eq_abs, abs_mul]
  have h1 := gh_f_abs (x := x) (d := resid A p) hx
  have h3 : |fX x (resid A p)| * |p.2 i * p.1 k| ≤ |resid A p| * |p.2 i * p.1 k| :=
    mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
  have h4 : |resid A p| * |p.2 i * p.1 k| ≤
      (resid A p ^ 2 + (p.2 i * p.1 k) ^ 2) / 2 := by
    have := sq_nonneg (|resid A p| - |p.2 i * p.1 k|)
    nlinarith [sq_abs (p.2 i * p.1 k), sq_abs (resid A p)]
  have h5 : (p.2 i * p.1 k) ^ 2 ≤ (p.2 i ^ 4 + p.1 k ^ 4) / 2 := by
    nlinarith [sq_nonneg (p.2 i ^ 2 - p.1 k ^ 2)]
  have h6 : resid A p ^ 2 ≤ (1 + resid A p ^ 4) / 2 := by
    nlinarith [sq_nonneg (resid A p ^ 2 - 1)]
  nlinarith

private lemma gh_fact {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n a b c : ℕ} (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0)
    (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (hlaw : P.map zw = gaussPair m n)
    (Φ : Mat m n → Mat a b) (Ψ : Vec m × Vec n → Mat b c) (K : ℝ)
    (hΦm : ∀ i l, Measurable fun M => Φ M i l) (hΦb : ∀ M i l, |Φ M i l| ≤ K)
    (hΨm : ∀ l k, Measurable fun p => Ψ p l k)
    (hΨi : ∀ l k, Integrable (fun p => Ψ p l k) (gaussPair m n)) :
    (∀ i k, Integrable (fun ω => (Φ (M0 ω) * Ψ (zw ω)) i k) P) ∧
    Muon.mean P (fun ω => Φ (M0 ω) * Ψ (zw ω)) =
      Muon.mean P (fun ω => Φ (M0 ω)) * Muon.mean (gaussPair m n) Ψ := by
  have hterm : ∀ i l k, Integrable (fun ω => Φ (M0 ω) i l * Ψ (zw ω) l k) P := by
    intro i l k
    have h1 : Integrable (fun ω => Ψ (zw ω) l k) P := by
      refine (integrable_map_measure (hΨm l k).aestronglyMeasurable hzw.aemeasurable).1 ?_
      rw [hlaw]; exact hΨi l k
    exact h1.bdd_mul (c := K) (((hΦm i l).comp hM0).aestronglyMeasurable)
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hΦb _ _ _)
  refine ⟨fun i k => ?_, ?_⟩
  · simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ => hterm i l k
  · ext i k
    simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply]
    rw [integral_finsetSum _ fun l _ => hterm i l k]
    refine Finset.sum_congr rfl fun l _ => ?_
    exact gc_fact_scalar P M0 zw hM0 hzw hmap (fun M => Φ M i l) (fun p => Ψ p l k)
      (hΦm i l) (hΨm l k)


private lemma gh_mean_add {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') {a b : ℕ}
    (f g : Ω' → Mat a b) (hf : ∀ i k, Integrable (fun ω => f ω i k) P)
    (hg : ∀ i k, Integrable (fun ω => g ω i k) P) :
    Muon.mean P (fun ω => f ω + g ω) = Muon.mean P f + Muon.mean P g := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hf i k) (hg i k)

private lemma gh_mean_smul {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') {a b : ℕ}
    (c : ℝ) (f : Ω' → Mat a b) :
    Muon.mean P (fun ω => c • f ω) = c • Muon.mean P f := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul c _

private lemma gh_mean_mulR {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') {a b c : ℕ}
    (X : Ω' → Mat a b) (hX : ∀ i k, Integrable (fun ω => X ω i k) P) (L : Mat b c) :
    Muon.mean P (fun ω => X ω * L) = Muon.mean P X * L := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ fun l _ => (hX i l).mul_const (L l k)]
  exact Finset.sum_congr rfl fun l _ => integral_mul_const (L l k) _

private lemma gh_conj_outer {a b : ℕ} (L : Mat a a) (R : Mat b b) (hL : Lᵀ = L) (hR : Rᵀ = R)
    (z : Vec a) (w : Vec b) :
    L * Muon.outer z w * R = Muon.outer (Matrix.mulVec L z) (Matrix.mulVec R w) := by
  have hv : Matrix.vecMul w R = Matrix.mulVec R w := by
    rw [← Matrix.vecMul_transpose, hR]
  rw [Muon.outer, Muon.outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]

private lemma gh_B_outer {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B)
    (p : Vec m × Vec n) :
    (B : ℝ) • Muon.outer (momU C B p) (momU C B p) =
      rOut C * Muon.outer p.1 p.1 * rOut C ∧
    (B : ℝ) • Muon.outer (momV C B p) (momU C B p) =
      rIn C * Muon.outer p.2 p.1 * rOut C := by
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hsO : (rOut C)ᵀ = rOut C := pj_sqrt_symm _
  have hsI : (rIn C)ᵀ = rIn C := pj_sqrt_symm _
  have hr : (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hBr.le]; field_simp
  constructor
  · rw [gh_conj_outer _ _ hsO hsO]
    unfold momU
    ext i k
    simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
    linear_combination (Matrix.mulVec (rOut C) p.1 i * Matrix.mulVec (rOut C) p.1 k) * hr
  · rw [gh_conj_outer _ _ hsI hsO]
    unfold momU momV
    ext i k
    simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
    linear_combination (Matrix.mulVec (rIn C) p.2 i * Matrix.mulVec (rOut C) p.1 k) * hr

private lemma gh_int_Xs {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (K : Ω' → Mat m n) (hK : Measurable K) (s : ℝ) (hs : 0 < s) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => Xs (K ω) s i k) P := by
  refine Integrable.of_bound (C := 1 / (2 * Real.sqrt s))
    (((measurable_pi_apply k).comp ((measurable_pi_apply i).comp
      ((gs_Xs_meas s).comp hK))).aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun ω => ?_
  rw [Real.norm_eq_abs]
  exact (pj_abs_entry_le_opNorm _ i k).trans (lem_app_de_resolvent (K ω) s hs).2.2.1

private lemma gh_meas_mulR {X : Type} [MeasurableSpace X] {a b c : ℕ} (F : X → Mat a b)
    (hF : Measurable F) (L : Mat b c) (i : Fin a) (k : Fin c) :
    Measurable (fun x => (F x * L) i k) := by
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hF)).mul measurable_const


private lemma gh_sqrt_norm {m n : ℕ} (C : Covariances m n) {CS : ℝ} (hCo : opNorm C.Sout ≤ CS)
    (hCi : opNorm C.Sin ≤ CS) :
    opNorm (rOut C) ≤ Real.sqrt CS ∧ opNorm (rIn C) ≤ Real.sqrt CS := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  constructor
  · refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sout C.psdOut CS hCo y
  · refine pj_opNorm_le_of_sq _ _ (Real.sqrt_nonneg _) fun y => ?_
    rw [Real.sq_sqrt hCS0]
    exact pj_sqrt_quad_le C.Sin C.psdIn CS hCi y

/-- Gram part of the per-age identity: mean of `ψ(d) · B R₀ (u⊗u)` factorizes. -/
private lemma gh_gram_main {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1) (B : ℕ) (hB : 0 < B)
    (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (hlaw : P.map zw = gaussPair m n) {s CS x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hCo : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS) :
    (∀ i k, Integrable (fun ω => (psiX x (resid A (zw ω)) • ((B : ℝ) • (Rs (M0 ω) s *
      Muon.outer (momU C B (zw ω)) (momU C B (zw ω))))) i k) P) ∧
    Muon.mean P (fun ω => psiX x (resid A (zw ω)) • ((B : ℝ) • (Rs (M0 ω) s *
      Muon.outer (momU C B (zw ω)) (momU C B (zw ω))))) =
      Muon.mean P (fun ω => Rs (M0 ω) s) * rOut C *
        Muon.mean (gaussPair m n) (fun p => psiX x (resid A p) • Muon.outer p.1 p.1) * rOut C := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  obtain ⟨hrn, -⟩ := gh_sqrt_norm C hCo hCi
  have hRm : Measurable (fun M : Mat m n => Rs M s) := pj_Rs_measurable s
  have hcontψ : Continuous (fun p : Vec m × Vec n => psiX x (resid A p)) :=
    (gram_psi_cont hx).comp (gram_resid_cont A)
  set X : Vec m × Vec n → Mat m m := fun p => psiX x (resid A p) • Muon.outer p.1 p.1 with hXdef
  have hXi : ∀ i k, Integrable (fun p => X p i k) (gaussPair m n) := by
    intro i k
    simpa [hXdef, Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, mul_assoc] using
      gh_int_zz A hA hx i k
  set Φ : Mat m n → Mat m m := fun M => Rs M s * rOut C with hΦ
  set Ψ : Vec m × Vec n → Mat m m := fun p => X p * rOut C with hΨ
  have hΦm : ∀ i l, Measurable fun M => Φ M i l := fun i l => gh_meas_mulR _ hRm _ i l
  have hΦb : ∀ M i l, |Φ M i l| ≤ (1 / s) * Real.sqrt CS := fun M i l =>
    (pj_abs_entry_le_opNorm _ i l).trans ((gr_opNorm_mul _ _).trans
      (mul_le_mul (lem_app_de_resolvent M s hs).1 hrn (pj_opNorm_nonneg _) (by positivity)))
  have hΨc : ∀ l k, Continuous fun p => Ψ p l k := by
    intro l k
    simp only [hΨ, hXdef, Matrix.mul_apply, Matrix.smul_apply, Muon.outer, Matrix.vecMulVec_apply,
      smul_eq_mul]
    fun_prop
  have hΨi : ∀ l k, Integrable (fun p => Ψ p l k) (gaussPair m n) := by
    intro l k
    simp only [hΨ, Matrix.mul_apply]
    exact integrable_finsetSum _ fun a _ => (hXi l a).mul_const _
  obtain ⟨hint, hmean⟩ := gh_fact P M0 zw hM0 hzw hmap hlaw Φ Ψ _ hΦm hΦb
    (fun l k => (hΨc l k).measurable) hΨi
  have hpt : ∀ ω, psiX x (resid A (zw ω)) • ((B : ℝ) • (Rs (M0 ω) s *
      Muon.outer (momU C B (zw ω)) (momU C B (zw ω)))) = Φ (M0 ω) * Ψ (zw ω) := by
    intro ω
    have := (gh_B_outer C B hB (zw ω)).1
    rw [← Matrix.mul_smul, this]
    simp only [hΦ, hΨ, hXdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  simp only [hpt]
  refine ⟨hint, ?_⟩
  rw [hmean]
  have e1 : Muon.mean P (fun ω => Φ (M0 ω)) = Muon.mean P (fun ω => Rs (M0 ω) s) * rOut C :=
    gh_mean_mulR P _ (fun i k => pj_int_Rs P M0 hM0 s hs i k) _
  have e2 : Muon.mean (gaussPair m n) Ψ = Muon.mean (gaussPair m n) X * rOut C :=
    gh_mean_mulR _ _ hXi _
  rw [e1, e2]
  simp only [Matrix.mul_assoc]


private lemma gh_mixed_main {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1) (B : ℕ) (hB : 0 < B)
    (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (hlaw : P.map zw = gaussPair m n) {s CS x : ℝ} (hs : 0 < s) (hx : 0 ≤ x)
    (hCo : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS) :
    (∀ i k, Integrable (fun ω => (fX x (resid A (zw ω)) • ((B : ℝ) • (Xs (M0 ω) s *
      Muon.outer (momV C B (zw ω)) (momU C B (zw ω))))) i k) P) ∧
    Muon.mean P (fun ω => fX x (resid A (zw ω)) • ((B : ℝ) • (Xs (M0 ω) s *
      Muon.outer (momV C B (zw ω)) (momU C B (zw ω))))) =
      Muon.mean P (fun ω => Xs (M0 ω) s) * rIn C *
        Muon.mean (gaussPair m n) (fun p => fX x (resid A p) • Muon.outer p.2 p.1) * rOut C := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  obtain ⟨-, hrn⟩ := gh_sqrt_norm C hCo hCi
  have hXm : Measurable (fun M : Mat m n => Xs M s) := gs_Xs_meas s
  have hcontf : Continuous (fun p : Vec m × Vec n => fX x (resid A p)) :=
    (gh_f_cont hx).comp (gram_resid_cont A)
  set X : Vec m × Vec n → Mat n m := fun p => fX x (resid A p) • Muon.outer p.2 p.1 with hXdef
  have hXi : ∀ i k, Integrable (fun p => X p i k) (gaussPair m n) := by
    intro i k
    simpa [hXdef, Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, mul_assoc] using
      gh_int_wz A hA hx i k
  set Φ : Mat m n → Mat m n := fun M => Xs M s * rIn C with hΦ
  set Ψ : Vec m × Vec n → Mat n m := fun p => X p * rOut C with hΨ
  have hΦm : ∀ i l, Measurable fun M => Φ M i l := fun i l => gh_meas_mulR _ hXm _ i l
  have hΦb : ∀ M i l, |Φ M i l| ≤ (1 / (2 * Real.sqrt s)) * Real.sqrt CS := fun M i l =>
    (pj_abs_entry_le_opNorm _ i l).trans ((gr_opNorm_mul _ _).trans
      (mul_le_mul (lem_app_de_resolvent M s hs).2.2.1 hrn (pj_opNorm_nonneg _) (by positivity)))
  have hΨc : ∀ l k, Continuous fun p => Ψ p l k := by
    intro l k
    simp only [hΨ, hXdef, Matrix.mul_apply, Matrix.smul_apply, Muon.outer, Matrix.vecMulVec_apply,
      smul_eq_mul]
    fun_prop
  have hΨi : ∀ l k, Integrable (fun p => Ψ p l k) (gaussPair m n) := by
    intro l k
    simp only [hΨ, Matrix.mul_apply]
    exact integrable_finsetSum _ fun a _ => (hXi l a).mul_const _
  obtain ⟨hint, hmean⟩ := gh_fact P M0 zw hM0 hzw hmap hlaw Φ Ψ _ hΦm hΦb
    (fun l k => (hΨc l k).measurable) hΨi
  have hpt : ∀ ω, fX x (resid A (zw ω)) • ((B : ℝ) • (Xs (M0 ω) s *
      Muon.outer (momV C B (zw ω)) (momU C B (zw ω)))) = Φ (M0 ω) * Ψ (zw ω) := by
    intro ω
    have := (gh_B_outer C B hB (zw ω)).2
    rw [← Matrix.mul_smul, this]
    simp only [hΦ, hΨ, hXdef, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_assoc]
  simp only [hpt]
  refine ⟨hint, ?_⟩
  rw [hmean]
  have e1 : Muon.mean P (fun ω => Φ (M0 ω)) = Muon.mean P (fun ω => Xs (M0 ω) s) * rIn C :=
    gh_mean_mulR P _ (fun i k => gh_int_Xs P M0 hM0 s hs i k) _
  have e2 : Muon.mean (gaussPair m n) Ψ = Muon.mean (gaussPair m n) X * rOut C :=
    gh_mean_mulR _ _ hXi _
  rw [e1, e2]
  simp only [Matrix.mul_assoc]


private lemma gh_assemble {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') {m : ℕ}
    (Gm N1 N2 : Ω' → Mat m m) (e3 e1 ψ f : Ω' → ℝ) (κ wj : ℝ)
    (hG : ∀ ω, Gm ω = e3 ω • N1 ω + κ • (ψ ω • N1 ω) + e1 ω • N2 ω + wj • (f ω • N2 ω))
    (hI1 : ∀ i k, Integrable (fun ω => (e3 ω • N1 ω) i k) P)
    (hIG : ∀ i k, Integrable (fun ω => (ψ ω • N1 ω) i k) P)
    (hI2 : ∀ i k, Integrable (fun ω => (e1 ω • N2 ω) i k) P)
    (hIM : ∀ i k, Integrable (fun ω => (f ω • N2 ω) i k) P) :
    Muon.mean P Gm = Muon.mean P (fun ω => e3 ω • N1 ω) +
      κ • Muon.mean P (fun ω => ψ ω • N1 ω) + Muon.mean P (fun ω => e1 ω • N2 ω) +
      wj • Muon.mean P (fun ω => f ω • N2 ω) := by
  have hb : ∀ i k, Integrable (fun ω => (κ • (ψ ω • N1 ω)) i k) P := fun i k =>
    (hIG i k).const_mul κ
  have hd : ∀ i k, Integrable (fun ω => (wj • (f ω • N2 ω)) i k) P := fun i k =>
    (hIM i k).const_mul wj
  have hab : ∀ i k, Integrable (fun ω => (e3 ω • N1 ω + κ • (ψ ω • N1 ω)) i k) P := fun i k =>
    (hI1 i k).add (hb i k)
  have habc : ∀ i k, Integrable (fun ω => (e3 ω • N1 ω + κ • (ψ ω • N1 ω) + e1 ω • N2 ω) i k) P :=
    fun i k => (hab i k).add (hI2 i k)
  have e : Gm = fun ω => e3 ω • N1 ω + κ • (ψ ω • N1 ω) + e1 ω • N2 ω + wj • (f ω • N2 ω) :=
    funext hG
  rw [e, gh_mean_add P _ _ habc hd, gh_mean_add P _ _ hab (hI2), gh_mean_add P _ _ (hI1) hb,
    gh_mean_smul, gh_mean_smul]

private lemma gh_final {m : ℕ} (M1 M2 MG MM P0 S : Mat m m) (κ wj Jx c b1 b2 b3 b4 : ℝ)
    (hκ : 0 ≤ κ) (hwj : 0 ≤ wj) (hc : c = κ * Jx)
    (h1 : opNorm M1 ≤ b1) (h2 : opNorm (MG - Jx • (P0 * S)) ≤ b2) (h3 : opNorm M2 ≤ b3)
    (h4 : opNorm MM ≤ b4) :
    opNorm (M1 + κ • MG + M2 + wj • MM - c • (P0 * S)) ≤ b1 + κ * b2 + b3 + wj * b4 := by
  have e : M1 + κ • MG + M2 + wj • MM - c • (P0 * S) =
      M1 + κ • (MG - Jx • (P0 * S)) + M2 + wj • MM := by
    rw [hc]; module
  rw [e]
  have k2 : opNorm (κ • (MG - Jx • (P0 * S))) ≤ κ * b2 := by
    rw [gr_opNorm_smul, abs_of_nonneg hκ]
    exact mul_le_mul_of_nonneg_left h2 hκ
  have k4 : opNorm (wj • MM) ≤ wj * b4 := by
    rw [gr_opNorm_smul, abs_of_nonneg hwj]
    exact mul_le_mul_of_nonneg_left h4 hwj
  calc opNorm (M1 + κ • (MG - Jx • (P0 * S)) + M2 + wj • MM)
      ≤ opNorm (M1 + κ • (MG - Jx • (P0 * S)) + M2) + opNorm (wj • MM) := gr_opNorm_add _ _
    _ ≤ (opNorm (M1 + κ • (MG - Jx • (P0 * S))) + opNorm M2) + opNorm (wj • MM) :=
        add_le_add_left (gr_opNorm_add _ _) _
    _ ≤ ((opNorm M1 + opNorm (κ • (MG - Jx • (P0 * S)))) + opNorm M2) + opNorm (wj • MM) :=
        add_le_add_left (add_le_add_left (gr_opNorm_add _ _) _) _
    _ ≤ _ := by linarith

private lemma gh_alpha_meas {m n : ℕ} (C : Covariances m n) (A : Mat m n) (s hj : ℝ) (B : ℕ) :
    Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      alpha1 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) ∧
    Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      alpha3 q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) := by
  have hR : Measurable (fun q : Mat m n × (Vec m × Vec n) => Rs q.1 s) :=
    (pj_Rs_measurable s).comp measurable_fst
  have hRt : Measurable (fun q : Mat m n × (Vec m × Vec n) => Rts q.1 s) := by
    have hc : Continuous (fun M : Mat m n => Mᵀ * M + s • (1 : Mat n n)) := by fun_prop
    exact (pj_inv_measurable (a := n)).comp (hc.measurable.comp measurable_fst)
  have hX : Measurable (fun q : Mat m n × (Vec m × Vec n) => Xs q.1 s) :=
    (gs_Xs_meas s).comp measurable_fst
  have hu : Measurable (fun q : Mat m n × (Vec m × Vec n) => momU C B q.2) :=
    (by unfold momU; fun_prop : Measurable (momU C B)).comp measurable_snd
  have hv : Measurable (fun q : Mat m n × (Vec m × Vec n) => momV C B q.2) :=
    (by unfold momV; fun_prop : Measurable (momV C B)).comp measurable_snd
  have hd : Measurable (fun q : Mat m n × (Vec m × Vec n) => hj * resid A q.2) :=
    measurable_const.mul ((by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid A x).comp measurable_snd)
  have hmv : ∀ {a b : ℕ} (K : Mat m n × (Vec m × Vec n) → Mat a b) (x : Mat m n × (Vec m × Vec n) → Vec b),
      Measurable K → Measurable x → Measurable (fun q => K q *ᵥ x q) := by
    intro a b K x hK hx
    refine measurable_pi_iff.2 fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hK)).mul
        ((measurable_pi_apply l).comp hx)
  have hdot : ∀ {a : ℕ} (x y : Mat m n × (Vec m × Vec n) → Vec a), Measurable x → Measurable y →
      Measurable (fun q => dotProduct (x q) (y q)) := by
    intro a x y hx hy
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp hx).mul ((measurable_pi_apply l).comp hy)
  have hU : Measurable (fun q : Mat m n × (Vec m × Vec n) => delU q.1 (momU C B q.2) s) :=
    hdot _ _ hu (hmv _ _ hR hu)
  have hV : Measurable (fun q : Mat m n × (Vec m × Vec n) => delV q.1 (momV C B q.2) s) :=
    hdot _ _ hv (hmv _ _ hRt hv)
  have hCc : Measurable (fun q : Mat m n × (Vec m × Vec n) => delC q.1 (momU C B q.2) (momV C B q.2) s) :=
    hdot _ _ hu (hmv _ _ hX hv)
  have hL : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      delLambda q.1 (hj * resid A q.2) (momU C B q.2) (momV C B q.2) s) := by
    unfold delLambda
    exact ((measurable_const.add (hd.mul hCc)).pow_const 2).add
      (((measurable_const.mul (hd.pow_const 2)).mul hU).mul hV)
  constructor
  · unfold alpha1
    exact (hd.mul (measurable_const.add (hd.mul hCc))).div hL
  · unfold alpha3
    exact (((measurable_const.mul (hd.pow_const 2)).mul hV).neg).div hL


private lemma gh_split {m n : ℕ} (R : Mat m m) (X : Mat m n) (u : Vec m) (v : Vec n)
    (B c3 c1 e3 e1 κ ψ f wj : ℝ) (h3 : c3 = e3 + κ * ψ) (h1 : c1 = e1 + wj * f) :
    B • Muon.outer (c3 • (R *ᵥ u) + c1 • (X *ᵥ v)) u =
      e3 • (B • (R * Muon.outer u u)) + κ • (ψ • (B • (R * Muon.outer u u))) +
        e1 • (B • (X * Muon.outer v u)) + wj • (f • (B • (X * Muon.outer v u))) := by
  rw [gs_G_alg, h3, h1]
  module

private lemma gh_age {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1) (B : ℕ) (hB : 0 < B)
    (M0 : Ω' → Mat m n) (zw : Ω' → Vec m × Vec n) (hM0 : Measurable M0) (hzw : Measurable zw)
    (hmap : P.map (fun ω => (M0 ω, zw ω)) = (P.map M0).prod (gaussPair m n))
    (hlaw : P.map zw = gaussPair m n) {s CS : ℝ} (hs : 0 < s)
    (hCo : opNorm C.Sout ≤ CS) (hCi : opNorm C.Sin ≤ CS)
    (wj x τ eB rB : ℝ) (hx : 0 ≤ x) (hwj : 0 ≤ wj) (hτ : 0 ≤ τ) (heB : 0 ≤ eB)
    (hrb : |∫ p, psiX x (resid A p) ∂(gaussPair m n) - J x| ≤ rB)
    (he1 : eLpNorm (fun ω => alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
        (momV C B (zw ω)) s - wj * fX x (resid A (zw ω))) 2 P ≤ ENNReal.ofReal (wj * eB))
    (he3 : eLpNorm (fun ω => alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
        (momV C B (zw ω)) s - (-(s * (wj ^ 2 * τ * psiX x (resid A (zw ω)))))) 2 P ≤
        ENNReal.ofReal (wj ^ 2 * eB)) :
    opNorm ((B : ℝ) • Muon.mean P (fun ω => Muon.outer
        ((-(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s)) •
            (Rs (M0 ω) s *ᵥ momU C B (zw ω)) +
          (alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s) •
            (Xs (M0 ω) s *ᵥ momV C B (zw ω))) (momU C B (zw ω)))
        - (s * wj ^ 2 * τ * J x) • (Muon.mean P (fun ω => Rs (M0 ω) s) * C.Sout)) ≤
      wj ^ 2 * eB * Real.sqrt (3 * (CS / s ^ 2 * CS)) +
        (s * (wj ^ 2 * τ)) * ((1 / s) * CS * (rB + 6 * opNorm A)) +
        wj * eB * Real.sqrt (3 * (CS / (4 * s) * CS)) +
        wj * ((1 / (2 * Real.sqrt s)) * CS * (opNorm A + 36 * x * opNorm A ^ 2)) := by
  have hCS0 : 0 ≤ CS := (pj_opNorm_nonneg _).trans hCo
  have hpair : Measurable (fun ω => (M0 ω, zw ω)) := hM0.prodMk hzw
  have hcontψ : Continuous (fun p : Vec m × Vec n => psiX x (resid A p)) :=
    (gram_psi_cont hx).comp (gram_resid_cont A)
  have hcontf : Continuous (fun p : Vec m × Vec n => fX x (resid A p)) :=
    (gh_f_cont hx).comp (gram_resid_cont A)
  have hψm : Measurable (fun ω => psiX x (resid A (zw ω))) := hcontψ.measurable.comp hzw
  have hfm : Measurable (fun ω => fX x (resid A (zw ω))) := hcontf.measurable.comp hzw
  have ha3 : Measurable (fun ω => alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
      (momV C B (zw ω)) s) := Measurable.comp (g := fun q : Mat m n × (Vec m × Vec n) => alpha3 q.1 (wj * resid A q.2) (momU C B q.2) (momV C B q.2) s) (f := fun ω => (M0 ω, zw ω)) (gh_alpha_meas C A s wj B).2 hpair
  have ha1 : Measurable (fun ω => alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
      (momV C B (zw ω)) s) := Measurable.comp (g := fun q : Mat m n × (Vec m × Vec n) => alpha1 q.1 (wj * resid A q.2) (momU C B q.2) (momV C B q.2) s) (f := fun ω => (M0 ω, zw ω)) (gh_alpha_meas C A s wj B).1 hpair
  have hem3 : Measurable (fun ω => -(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
      (momV C B (zw ω)) s) - (s * (wj ^ 2 * τ)) * psiX x (resid A (zw ω))) :=
    ha3.neg.sub (measurable_const.mul hψm)
  have hem1 : Measurable (fun ω => alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
      (momV C B (zw ω)) s - wj * fX x (resid A (zw ω))) :=
    ha1.sub (measurable_const.mul hfm)
  have he3' : eLpNorm (fun ω => -(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
      (momV C B (zw ω)) s) - (s * (wj ^ 2 * τ)) * psiX x (resid A (zw ω))) 2 P ≤
      ENNReal.ofReal (wj ^ 2 * eB) := by
    have e : (fun ω => -(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
        (momV C B (zw ω)) s) - (s * (wj ^ 2 * τ)) * psiX x (resid A (zw ω))) =
        -(fun ω => alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω))
          (momV C B (zw ω)) s - (-(s * (wj ^ 2 * τ * psiX x (resid A (zw ω)))))) := by
      funext ω; simp only [Pi.neg_apply]; ring
    rw [e, eLpNorm_neg]; exact he3
  obtain ⟨hint3, hnorm3⟩ := gc_repl_uu P C B hB M0 zw hM0 hzw hmap hs hCo
    (fun ω => -(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s)
      - (s * (wj ^ 2 * τ)) * psiX x (resid A (zw ω))) hem3 (wj ^ 2 * eB) (by positivity) he3'
  obtain ⟨hint1, hnorm1⟩ := gc_repl_vu P C B hB M0 zw hM0 hzw hmap hs hCo hCi
    (fun ω => alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s
      - wj * fX x (resid A (zw ω))) hem1 (wj * eB) (by positivity) he1
  obtain ⟨hintG, hmeanG⟩ := gh_gram_main P C A hA B hB M0 zw hM0 hzw hmap hlaw hs hx hCo hCi
  obtain ⟨hintM, hmeanM⟩ := gh_mixed_main P C A hA B hB M0 zw hM0 hzw hmap hlaw hs hx hCo hCi
  have hP0 : opNorm (Muon.mean P (fun ω => Rs (M0 ω) s)) ≤ 1 / s :=
    gh_opNorm_mean P _ (fun i k => pj_int_Rs P M0 hM0 s hs i k) (1 / s) (by positivity)
      (fun ω => (lem_app_de_resolvent _ s hs).1)
  have hX0 : opNorm (Muon.mean P (fun ω => Xs (M0 ω) s)) ≤ 1 / (2 * Real.sqrt s) :=
    gh_opNorm_mean P _ (fun i k => gh_int_Xs P M0 hM0 s hs i k) _ (by positivity)
      (fun ω => (lem_app_de_resolvent _ s hs).2.2.1)
  have hmain := gh_assemble P
    (fun ω => (B : ℝ) • Muon.outer
      ((-(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s)) •
          (Rs (M0 ω) s *ᵥ momU C B (zw ω)) +
        (alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s) •
          (Xs (M0 ω) s *ᵥ momV C B (zw ω))) (momU C B (zw ω)))
    (fun ω => (B : ℝ) • (Rs (M0 ω) s * Muon.outer (momU C B (zw ω)) (momU C B (zw ω))))
    (fun ω => (B : ℝ) • (Xs (M0 ω) s * Muon.outer (momV C B (zw ω)) (momU C B (zw ω))))
    (fun ω => -(alpha3 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s)
      - (s * (wj ^ 2 * τ)) * psiX x (resid A (zw ω)))
    (fun ω => alpha1 (M0 ω) (wj * resid A (zw ω)) (momU C B (zw ω)) (momV C B (zw ω)) s
      - wj * fX x (resid A (zw ω)))
    (fun ω => psiX x (resid A (zw ω))) (fun ω => fX x (resid A (zw ω))) (s * (wj ^ 2 * τ)) wj
    (fun ω => gh_split (Rs (M0 ω) s) (Xs (M0 ω) s) (momU C B (zw ω)) (momV C B (zw ω)) (B : ℝ)
      _ _ _ _ _ _ _ _ (by ring) (by ring))
    hint3 hintG hint1 hintM
  have hsm : ∀ f : Ω' → Mat m m, (B : ℝ) • Muon.mean P f = Muon.mean P (fun ω => (B : ℝ) • f ω) :=
    fun f => (gh_mean_smul P (B : ℝ) f).symm
  rw [hsm, hmain]
  beta_reduce
  rw [hmeanG, hmeanM]
  have hresp := gc_resp C A hA hx hCo (Muon.mean P (fun ω => Rs (M0 ω) s))
  have hrespf := gc_resp_f C A hA hx hCo hCi (Muon.mean P (fun ω => Xs (M0 ω) s))
  have hn0 := pj_opNorm_nonneg A
  have b2 : opNorm (Muon.mean P (fun ω => Rs (M0 ω) s) * rOut C *
        Muon.mean (gaussPair m n) (fun p => psiX x (resid A p) • Muon.outer p.1 p.1) * rOut C
        - J x • (Muon.mean P (fun ω => Rs (M0 ω) s) * C.Sout)) ≤
      (1 / s) * CS * (rB + 6 * opNorm A) := by
    refine hresp.trans ?_
    have := pj_opNorm_nonneg (Muon.mean P (fun ω => Rs (M0 ω) s))
    calc _ ≤ (1 / s) * CS * (|∫ p, psiX x (resid A p) ∂(gaussPair m n) - J x| + 6 * opNorm A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hP0 hCS0) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have b4 : opNorm (Muon.mean P (fun ω => Xs (M0 ω) s) * rIn C *
        Muon.mean (gaussPair m n) (fun p => fX x (resid A p) • Muon.outer p.2 p.1) * rOut C) ≤
      (1 / (2 * Real.sqrt s)) * CS * (opNorm A + 36 * x * opNorm A ^ 2) := by
    refine hrespf.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX0 hCS0) (by positivity)
  exact gh_final _ _ _ _ _ _ _ _ _ _ _ _ _ _ (by positivity) hwj (by ring) hnorm3 b2 hnorm1 b4


open scoped Matrix.Norms.L2Operator in
private lemma gh_tsum {m : ℕ} (Z : Mat m m) (T Y : ℕ → Mat m m) (b : ℕ → ℝ) (hb : Summable b)
    (hd : ∀ j, opNorm (T j - Y j) ≤ b j) (hY : Summable fun j => opNorm (Y j))
    (hZ : ∀ i k : Fin m, Z i k = ∑' j, T j i k) :
    opNorm (Z - ∑' j, Y j) ≤ ∑' j, b j := by
  have hYs : Summable Y := by
    refine Summable.of_norm_bounded hY fun j => ?_
    rw [opNorm_eq_norm]
  have hDs : Summable fun j => T j - Y j := by
    refine Summable.of_norm_bounded hb fun j => ?_
    rw [← opNorm_eq_norm]; exact hd j
  have hTs : Summable T := by
    have := hDs.add hYs
    simpa using this
  have hZe : Z = ∑' j, T j := by
    ext i k
    have h1 : (∑' j, T j) i = ∑' j, T j i := Pi.tsum_apply hTs
    have h2 : (∑' j, T j i) k = ∑' j, T j i k := Pi.tsum_apply (Pi.summable.1 hTs i)
    rw [hZ i k]
    show _ = (∑' j, T j) i k
    rw [h1, h2]
  rw [hZe, ← Summable.tsum_sub hTs hYs, opNorm_eq_norm]
  calc ‖∑' j, (T j - Y j)‖ ≤ ∑' j, ‖T j - Y j‖ := norm_tsum_le_tsum_norm hDs.norm
    _ ≤ ∑' j, b j := by
        refine Summable.tsum_le_tsum (fun j => ?_) hDs.norm hb
        rw [← opNorm_eq_norm]; exact hd j


private lemma gh_alg (wj eB rB a x τ s sm CS Γ qI K c1 c3 : ℝ) (hwj0 : 0 ≤ wj) (heB : 0 ≤ eB)
    (hrB : 0 ≤ rB) (ha : 0 ≤ a) (hx0 : 0 ≤ x) (hxq : x ≤ qI) (hτ0 : 0 ≤ τ) (hτ : τ ≤ Γ / sm)
    (hsm : 0 < sm) (hs : sm ≤ s) (hCS : 0 ≤ CS)
    (hc1 : c1 ≤ K) (hc3 : c3 ≤ K) (hK2 : 6 * (Γ * CS / sm) ≤ K)
    (hK4 : CS / (2 * Real.sqrt sm) ≤ K) (hK5 : 36 * qI * (CS / (2 * Real.sqrt sm)) ≤ K)
    (hinv : 1 / (2 * Real.sqrt s) ≤ 1 / (2 * Real.sqrt sm)) :
    wj ^ 2 * eB * c1 + (s * (wj ^ 2 * τ)) * ((1 / s) * CS * (rB + 6 * a)) + wj * eB * c3 +
      wj * ((1 / (2 * Real.sqrt s)) * CS * (a + 36 * x * a ^ 2)) ≤
    K * (wj ^ 2 * (eB + rB + a) + wj * (eB + a + a ^ 2)) := by
  have hs0 : 0 < s := lt_of_lt_of_le hsm hs
  have hsq : 0 < Real.sqrt sm := Real.sqrt_pos.2 hsm
  have hw2 : 0 ≤ wj ^ 2 := sq_nonneg _
  have hΓ : 0 ≤ Γ / sm := le_trans hτ0 hτ
  have t1 : wj ^ 2 * eB * c1 ≤ wj ^ 2 * eB * K :=
    mul_le_mul_of_nonneg_left hc1 (by positivity)
  have t3 : wj * eB * c3 ≤ wj * eB * K := mul_le_mul_of_nonneg_left hc3 (by positivity)
  have t2 : (s * (wj ^ 2 * τ)) * ((1 / s) * CS * (rB + 6 * a)) ≤ wj ^ 2 * K * (rB + a) := by
    have e : (s * (wj ^ 2 * τ)) * ((1 / s) * CS * (rB + 6 * a)) =
        wj ^ 2 * (τ * CS * (rB + 6 * a)) := by field_simp
    rw [e]
    have h1 : τ * CS * (rB + 6 * a) ≤ (Γ / sm) * CS * (6 * (rB + a)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hτ hCS) (by linarith) (by positivity)
        (by positivity)
    have h2 : (Γ / sm) * CS * (6 * (rB + a)) = (6 * (Γ * CS / sm)) * (rB + a) := by ring
    calc wj ^ 2 * (τ * CS * (rB + 6 * a)) ≤ wj ^ 2 * ((6 * (Γ * CS / sm)) * (rB + a)) :=
          mul_le_mul_of_nonneg_left (h1.trans h2.le) hw2
      _ ≤ wj ^ 2 * (K * (rB + a)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK2 (by positivity)) hw2
      _ = _ := by ring
  have t4 : wj * ((1 / (2 * Real.sqrt s)) * CS * (a + 36 * x * a ^ 2)) ≤ wj * (K * (a + a ^ 2)) := by
    refine mul_le_mul_of_nonneg_left ?_ hwj0
    have h1 : (1 / (2 * Real.sqrt s)) * CS * (a + 36 * x * a ^ 2) ≤
        (1 / (2 * Real.sqrt sm)) * CS * (a + 36 * qI * a ^ 2) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_right hinv hCS) ?_ (by positivity) (by positivity)
      have : 36 * x * a ^ 2 ≤ 36 * qI * a ^ 2 := by
        have := mul_le_mul_of_nonneg_left hxq (by norm_num : (0 : ℝ) ≤ 36)
        exact mul_le_mul_of_nonneg_right this (sq_nonneg a)
      linarith
    have h2 : (1 / (2 * Real.sqrt sm)) * CS * (a + 36 * qI * a ^ 2) =
        (CS / (2 * Real.sqrt sm)) * a + (36 * qI * (CS / (2 * Real.sqrt sm))) * a ^ 2 := by
      field_simp
    refine h1.trans (h2.le.trans ?_)
    nlinarith [mul_le_mul_of_nonneg_right hK4 ha, mul_le_mul_of_nonneg_right hK5 (sq_nonneg a)]
  nlinarith [t1, t2, t3, t4]


private lemma gh_fixed {Ω' : Type} [MeasurableSpace Ω'] (P : Measure Ω') [IsProbabilityMeasure P]
    {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (I : Set ℝ) (sm : ℝ) (hsm : 0 < sm)
    (hI : ∀ s ∈ I, sm ≤ s) {s : ℝ} (hs : s ∈ I) (γ CSig : ℝ)
    (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig)
    (K eB rB : ℝ) (heB : 0 ≤ eB)
    (hK1 : Real.sqrt (3 * (CSig / sm ^ 2 * CSig)) ≤ K)
    (hK2 : 6 * ((CSig * γ) * CSig / sm) ≤ K)
    (hK3 : Real.sqrt (3 * (CSig / (4 * sm) * CSig)) ≤ K)
    (hK4 : CSig / (2 * Real.sqrt sm) ≤ K)
    (hK5 : 36 * ((CSig * γ) ^ 2 / sm) * (CSig / (2 * Real.sqrt sm)) ≤ K)
    (hrb : ∀ x ∈ Icc (0 : ℝ) ((CSig * γ) ^ 2 / sm),
      |∫ p, psiX x (resid F.A p) ∂(gaussPair m n) - J x| ≤ rB)
    (hrep : ∀ j : ℕ,
      eLpNorm (fun ω => delAlpha1 w F S t j s ω - checkAlpha1 w F S t j s ω) 2 P ≤
        ENNReal.ofReal (w j * eB) ∧
      eLpNorm (fun ω => delAlpha3 w F S t j s ω - checkAlpha3 w F S t j s ω) 2 P ≤
        ENNReal.ofReal (w j ^ 2 * eB)) :
    opNorm ((1 : Mat m m) - s • expRes w F S t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w F S t s * J (w j ^ 2 * qB w F S t s)) •
          (expDelRes w F S t j (slotOne F.hB) s * F.C.Sout)) ≤
      K * ((eB + rB + opNorm F.A) + (eB + opNorm F.A + opNorm F.A ^ 2)) := by
  have hB : 0 < B := F.hB
  have hs0 : 0 < s := lt_of_lt_of_le hsm (hI s hs)
  have hsms : sm ≤ s := hI s hs
  have hCS0 : 0 ≤ CSig := (pj_opNorm_nonneg _).trans hC.1
  obtain ⟨-, -, hτ0, hτ1, hq0, hqI⟩ := eqn_app_de_qI w hw F S t CSig γ sm I hsm hI hC hdim s hs
  have hΓ0 : 0 ≤ CSig * γ := mul_nonneg hCS0 hγ
  have hτ : sigmaTildeB w F S t s ≤ (CSig * γ) / sm :=
    hτ1.trans (div_le_div_of_nonneg_left hΓ0 hsm hsms)
  have hrB0 : 0 ≤ rB :=
    (abs_nonneg _).trans (hrb 0 ⟨le_rfl, by positivity⟩)
  have ha0 := pj_opNorm_nonneg F.A
  obtain ⟨hwnn, hwsum, -⟩ := hw.1
  have hw1 := hw.2.1
  have hw2s : Summable fun j => w j ^ 2 :=
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by nlinarith [hwnn j, hw1 j]) hwsum
  have hw2le : ∑' j, w j ^ 2 ≤ 1 :=
    (Summable.tsum_le_tsum (fun j => by nlinarith [hwnn j, hw1 j]) hw2s hwsum).trans hw.2.2
  set Gf : ℕ → Mat m n × (Vec m × Vec n) → Mat m m := fun j q => Muon.outer
      ((-(alpha3 q.1 (w j * resid F.A q.2) (momU F.C B q.2) (momV F.C B q.2) s)) •
          (Rs q.1 s *ᵥ momU F.C B q.2) +
        (alpha1 q.1 (w j * resid F.A q.2) (momU F.C B q.2) (momV F.C B q.2) s) •
          (Xs q.1 s *ᵥ momV F.C B q.2)) (momU F.C B q.2) with hGf
  set T : ℕ → Mat m m := fun j => (B : ℝ) • Muon.mean P (fun ω =>
      Gf j (WeightedBufDel w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) ω,
        S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)) with hT
  set Y : ℕ → Mat m m := fun j =>
    (s * w j ^ 2 * sigmaTildeB w F S t s * J (w j ^ 2 * qB w F S t s)) •
      (expDelRes w F S t j (slotOne F.hB) s * F.C.Sout) with hY
  set b : ℕ → ℝ := fun j => K * (w j ^ 2 * (eB + rB + opNorm F.A) +
      w j * (eB + opNorm F.A + opNorm F.A ^ 2)) with hb
  have hd : ∀ j, opNorm (T j - Y j) ≤ b j := by
    intro j
    set s' : ℤ := t + 1 - (j : ℤ) with hs'
    have hM0 := pj_meas_del w F S t s' (slotOne F.hB)
    have hzw := S.meas s' (slotOne F.hB)
    have hind := weightedBufDel_indep w F S t s' (slotOne F.hB)
    have hmap : P.map (fun ω => (WeightedBufDel w F S t s' (slotOne F.hB) ω,
        S.zw s' (slotOne F.hB) ω)) =
        (P.map (WeightedBufDel w F S t s' (slotOne F.hB))).prod (gaussPair m n) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hM0.aemeasurable hzw.aemeasurable).1 hind]
      congr 1
      exact S.law _ _
    have hlaw : P.map (S.zw s' (slotOne F.hB)) = gaussPair m n := S.law _ _
    have hwj1 : w j ^ 2 ≤ 1 := by nlinarith [hwnn j, hw1 j]
    have hx0 : 0 ≤ w j ^ 2 * qB w F S t s := mul_nonneg (sq_nonneg _) hq0
    have hxq : w j ^ 2 * qB w F S t s ≤ (CSig * γ) ^ 2 / sm := by
      calc w j ^ 2 * qB w F S t s ≤ 1 * qB w F S t s := mul_le_mul_of_nonneg_right hwj1 hq0
        _ ≤ _ := by rw [one_mul]; exact hqI
    have h := gh_age P F.C F.A F.hA B hB (WeightedBufDel w F S t s' (slotOne F.hB))
      (S.zw s' (slotOne F.hB)) hM0 hzw hmap hlaw hs0 hC.1 hC.2 (w j)
      (w j ^ 2 * qB w F S t s) (sigmaTildeB w F S t s) eB rB hx0 (hwnn j) hτ0 heB
      (hrb _ ⟨hx0, hxq⟩) (hrep j).1 (hrep j).2
    refine h.trans ?_
    refine gh_alg (w j) eB rB (opNorm F.A) (w j ^ 2 * qB w F S t s) (sigmaTildeB w F S t s) s sm
      CSig (CSig * γ) ((CSig * γ) ^ 2 / sm) K _ _ (hwnn j) heB hrB0 ha0 hx0 hxq hτ0 hτ hsm hsms
      hCS0 ?_ ?_ hK2 hK4 hK5 ?_
    · refine le_trans (Real.sqrt_le_sqrt ?_) hK1
      have : CSig / s ^ 2 ≤ CSig / sm ^ 2 :=
        div_le_div_of_nonneg_left hCS0 (by positivity) (pow_le_pow_left₀ hsm.le hsms 2)
      nlinarith
    · refine le_trans (Real.sqrt_le_sqrt ?_) hK3
      have : CSig / (4 * s) ≤ CSig / (4 * sm) :=
        div_le_div_of_nonneg_left hCS0 (by positivity) (by linarith)
      nlinarith
    · exact one_div_le_one_div_of_le (by positivity)
        (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsms) (by norm_num))
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hK1
  have hbs : Summable b := by
    have e : b = fun j => K * (eB + rB + opNorm F.A) * w j ^ 2 +
        K * (eB + opNorm F.A + opNorm F.A ^ 2) * w j := by
      funext j; simp only [hb]; ring
    rw [e]; exact (hw2s.mul_left _).add (hwsum.mul_left _)
  have hPj : ∀ j, opNorm (expDelRes w F S t j (slotOne F.hB) s) ≤ 1 / s := by
    intro j
    exact gh_opNorm_mean P _ (fun i k => pj_int_Rs P _ (pj_meas_del w F S t _ (slotOne F.hB)) s hs0 i k)
      (1 / s) (by positivity) (fun ω => (lem_app_de_resolvent _ s hs0).1)
  have hY' : Summable fun j => opNorm (Y j) := by
    refine Summable.of_nonneg_of_le (fun j => pj_opNorm_nonneg _) (fun j => ?_)
      (hw2s.mul_left ((CSig * γ) * ((1 / s) * CSig)))
    have hJ := lem_app_de_scalar_i.2.2.1 (w j ^ 2 * qB w F S t s) (mul_nonneg (sq_nonneg _) hq0)
    have hτs : sigmaTildeB w F S t s * s ≤ CSig * γ := (le_div_iff₀ hs0).1 hτ1
    have hc : s * w j ^ 2 * sigmaTildeB w F S t s * J (w j ^ 2 * qB w F S t s) ≤
        w j ^ 2 * (CSig * γ) := by
      have h1 : s * w j ^ 2 * sigmaTildeB w F S t s = w j ^ 2 * (sigmaTildeB w F S t s * s) := by ring
      have h2 : 0 ≤ s * w j ^ 2 * sigmaTildeB w F S t s := by positivity
      calc _ ≤ s * w j ^ 2 * sigmaTildeB w F S t s * 1 :=
            mul_le_mul_of_nonneg_left hJ.2 h2
        _ = w j ^ 2 * (sigmaTildeB w F S t s * s) := by rw [mul_one, h1]
        _ ≤ w j ^ 2 * (CSig * γ) := mul_le_mul_of_nonneg_left hτs (sq_nonneg _)
    have hc0 : 0 ≤ s * w j ^ 2 * sigmaTildeB w F S t s * J (w j ^ 2 * qB w F S t s) := by
      have := hJ.1; positivity
    simp only [hY]
    rw [gr_opNorm_smul, abs_of_nonneg hc0]
    have hm : opNorm (expDelRes w F S t j (slotOne F.hB) s * F.C.Sout) ≤ (1 / s) * CSig :=
      (gr_opNorm_mul _ _).trans (mul_le_mul (hPj j) hC.1 (pj_opNorm_nonneg _) (by positivity))
    calc _ ≤ (w j ^ 2 * (CSig * γ)) * ((1 / s) * CSig) :=
          mul_le_mul hc hm (pj_opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  have hZ : ∀ i k : Fin m, ((1 : Mat m m) - s • expRes w F S t s) i k = ∑' j, T j i k := by
    intro i k
    have hGm : ∀ j i k, Measurable fun q => Gf j q i k := fun j i k =>
      gs_G_meas F.C F.A s (w j) i k
    have h1 := gs_step1 P w hw F S t hs0 γ CSig hdim hγ hC Gf hGm (fun j M0 p => rfl) i k
    have hint : Integrable (fun ω => Rs (WeightedBuf w F S t ω) s i k) P :=
      pj_int_Rs P _ (pj_meas_WB w F S t) s hs0 i k
    have h2 : ∫ ω, ((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) i k ∂P =
        (1 : Mat m m) i k - s * ∫ ω, Rs (WeightedBuf w F S t ω) s i k ∂P := by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      rw [integral_sub (integrable_const _) (hint.const_mul s), integral_const, integral_const_mul]
      simp
    calc ((1 : Mat m m) - s • expRes w F S t s) i k
        = (1 : Mat m m) i k - s * ∫ ω, Rs (WeightedBuf w F S t ω) s i k ∂P := by
          simp [expRes, Muon.mean]
      _ = ∫ ω, ((1 : Mat m m) - s • Rs (WeightedBuf w F S t ω) s) i k ∂P := h2.symm
      _ = ∑' j : ℕ, (B : ℝ) * ∫ ω, Gf j (WeightedBufDel w F S t (t + 1 - (j : ℤ)) (slotOne F.hB) ω,
          S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω) i k ∂P := h1
      _ = ∑' j, T j i k := by
          refine tsum_congr fun j => ?_
          simp [hT, Muon.mean]
  have key := gh_tsum ((1 : Mat m m) - s • expRes w F S t s) T Y b hbs hd hY' hZ
  refine key.trans ?_
  have e : b = fun j => K * (eB + rB + opNorm F.A) * w j ^ 2 +
      K * (eB + opNorm F.A + opNorm F.A ^ 2) * w j := by
    funext j; simp only [hb]; ring
  rw [e, Summable.tsum_add (hw2s.mul_left _) (hwsum.mul_left _), tsum_mul_left, tsum_mul_left]
  have hp1 : 0 ≤ K * (eB + rB + opNorm F.A) := by positivity
  have hp2 : 0 ≤ K * (eB + opNorm F.A + opNorm F.A ^ 2) := by positivity
  calc _ ≤ K * (eB + rB + opNorm F.A) * 1 + K * (eB + opNorm F.A + opNorm F.A ^ 2) * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hw2le hp1) (mul_le_mul_of_nonneg_left hw.2.2 hp2)
    _ = _ := by ring


private lemma gh_a_bound {m n : ℕ} (A : Mat m n) (hA : fro A = 1) {x : ℝ} (hx : 0 ≤ x) :
    |∫ p, psiX x (resid A p) ∂(gaussPair m n) - J x| ≤ 1 := by
  have h2 := (lem_app_setup_residual_i A hA).2.1
  have hint2 : Integrable (fun p : Vec m × Vec n => resid A p ^ 2) (gaussPair m n) := by
    by_contra h
    rw [integral_undef h] at h2
    norm_num at h2
  have hcont := (gram_psi_cont hx).comp (gram_resid_cont A)
  have hint : Integrable (fun p : Vec m × Vec n => psiX x (resid A p)) (gaussPair m n) := by
    refine hint2.mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    show ‖psiX x (resid A p)‖ ≤ resid A p ^ 2
    rw [Real.norm_eq_abs]; exact gram_psi_abs hx
  have hle : ∫ p, psiX x (resid A p) ∂(gaussPair m n) ≤ 1 := by
    rw [← h2]
    refine integral_mono hint hint2 fun p => ?_
    exact (le_abs_self _).trans (gram_psi_abs hx)
  have hge : 0 ≤ ∫ p, psiX x (resid A p) ∂(gaussPair m n) := by
    refine integral_nonneg fun p => ?_
    unfold psiX
    exact div_nonneg (sq_nonneg _) (gc_den_pos hx _).le
  have hJ := lem_app_de_scalar_i.2.2.1 x hx
  rw [abs_le]
  constructor <;> linarith [hJ.1, hJ.2]

private lemma gh_le_biSup {f : ℝ → ℝ} {S : Set ℝ} (hb : ∀ x ∈ S, f x ≤ 1) {x : ℝ} (hx : x ∈ S) :
    f x ≤ ⨆ y ∈ S, f y := by
  have hbdd : BddAbove (Set.range fun y => ⨆ (_ : y ∈ S), f y) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact Real.iSup_le (fun hy => hb y hy) zero_le_one
  calc f x = ⨆ (_ : x ∈ S), f x := (ciSup_pos (f := fun _ : x ∈ S => f x) hx).symm
    _ ≤ ⨆ y, ⨆ (_ : y ∈ S), f y := le_ciSup (f := fun y => ⨆ (_ : y ∈ S), f y) hbdd x


private lemma gh_H (w : ℕ → ℝ) (hw : WeightClass w) (t : ℤ) (I : Set ℝ) (hI : IsCompact I)
    (hIpos : I ⊆ Set.Ioi 0) :
    ∀ (R : SetupRegime) (Ω : ℕ → Type) [∀ k, MeasurableSpace (Ω k)]
      (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
      (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)),
      ∀ ε > 0, ∀ᶠ k in atTop, ∀ s ∈ I,
      opNorm ((1 : Mat (R.m k) (R.m k)) - s • expRes w (R.F k) (S k) t s
        - ∑' j, (s * w j ^ 2 * sigmaTildeB w (R.F k) (S k) t s *
            J (w j ^ 2 * qB w (R.F k) (S k) t s)) •
          (expDelRes w (R.F k) (S k) t j (slotOne (R.F k).hB) s * (R.F k).C.Sout)) ≤ ε := by
  intro R Ω _ P _ S ε hε
  rcases I.eq_empty_or_nonempty with hI0 | hne
  · exact Filter.Eventually.of_forall fun k s hs => absurd (hI0 ▸ hs) (Set.notMem_empty s)
  have hsmI : sInf I ∈ I := hI.sInf_mem hne
  have hsm : 0 < sInf I := hIpos hsmI
  have hIsm : ∀ s ∈ I, sInf I ≤ s := fun s hs => csInf_le hI.bddBelow hs
  have hCS0 : 0 ≤ R.CSig := le_trans zero_le_one R.hC
  have hγ : 0 ≤ R.γstar := by
    have h := R.dims 0
    have hB : (0 : ℝ) < R.B 0 := by exact_mod_cast (R.F 0).hB
    by_contra hneg
    push Not at hneg
    have h1 := mul_neg_of_neg_of_pos hneg hB
    have h2 := (Nat.cast_nonneg (max (R.m 0) (R.n 0)) : (0 : ℝ) ≤ _)
    linarith
  obtain ⟨e, he, Hrep⟩ := lem_app_de_replace I hI hIpos R.CSig R.γstar
  have hr := lem_app_de_gaussian (m := R.m) (n := R.n)
    (Ω := fun k => Vec (R.m k) × Vec (R.n k)) (fun k => gaussPair (R.m k) (R.n k))
    (fun k => (R.F k).A) (fun k ω => ω.1) (fun k ω => ω.2) (fun k => by simp)
    (fun k => (R.F k).hA) R.diffuse ((R.CSig * R.γstar) ^ 2 / sInf I)
  have hr' : Tendsto (fun k => ⨆ x ∈ Icc (0 : ℝ) ((R.CSig * R.γstar) ^ 2 / sInf I),
      |∫ p, psiX x (resid (R.F k).A p) ∂(gaussPair (R.m k) (R.n k)) - J x|) atTop (𝓝 0) := by
    simpa using hr
  have he' : Tendsto (fun k => |e (R.B k)|) atTop (𝓝 0) := by
    have := (continuous_abs.tendsto 0).comp (he.comp R.prop.B_top)
    simpa [Function.comp_def] using this
  have hg := ((((he'.add hr').add R.diffuse).add ((he'.add R.diffuse).add (R.diffuse.pow 2))).const_mul
    (Real.sqrt (3 * (R.CSig / sInf I ^ 2 * R.CSig)) + 6 * ((R.CSig * R.γstar) * R.CSig / sInf I) +
      Real.sqrt (3 * (R.CSig / (4 * sInf I) * R.CSig)) + R.CSig / (2 * Real.sqrt (sInf I)) +
      36 * ((R.CSig * R.γstar) ^ 2 / sInf I) * (R.CSig / (2 * Real.sqrt (sInf I)))))
  simp only [add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hg
  filter_upwards [hg.eventually (gt_mem_nhds hε)] with k hk s hs
  have hs0 : 0 < s := hIpos hs
  have h1 : 0 ≤ Real.sqrt (3 * (R.CSig / sInf I ^ 2 * R.CSig)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ 6 * ((R.CSig * R.γstar) * R.CSig / sInf I) := by positivity
  have h3 : 0 ≤ Real.sqrt (3 * (R.CSig / (4 * sInf I) * R.CSig)) := Real.sqrt_nonneg _
  have h4 : 0 ≤ R.CSig / (2 * Real.sqrt (sInf I)) := by positivity
  have h5 : 0 ≤ 36 * ((R.CSig * R.γstar) ^ 2 / sInf I) * (R.CSig / (2 * Real.sqrt (sInf I))) := by
    positivity
  have hdim : ((R.m k : ℕ) : ℝ) ≤ R.γstar * (R.B k : ℝ) ∧ ((R.n k : ℕ) : ℝ) ≤ R.γstar * (R.B k : ℝ) :=
    ⟨(Nat.cast_le.2 (le_max_left _ _)).trans (R.dims k),
      (Nat.cast_le.2 (le_max_right _ _)).trans (R.dims k)⟩
  have hrep := Hrep (R.m k) (R.n k) (R.B k) w hw (Ω k) (P k) (R.F k) (S k) t (R.normOut k)
    (R.normIn k) hdim.1 hdim.2
  refine le_trans (gh_fixed (P k) w hw (R.F k) (S k) t I (sInf I) hsm hIsm hs R.γstar R.CSig hdim hγ
    ⟨R.normOut k, R.normIn k⟩ _ (|e (R.B k)|) _ (abs_nonneg _) (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) ?_ ?_) hk.le
  · intro x hx
    exact gh_le_biSup (f := fun x => |∫ p, psiX x (resid (R.F k).A p) ∂(gaussPair (R.m k) (R.n k)) - J x|)
      (fun y hy => gh_a_bound _ (R.F k).hA hy.1) hx
  · intro j
    obtain ⟨a1, -, a3⟩ := hrep j s hs
    refine ⟨a1.trans (ENNReal.ofReal_le_ofReal ?_), a3.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) (hw.1.1 j)
    · exact mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)



/-- `thm:app-de-gram`, snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.1150–1161):
\begin{theorem}[Gram closure]\label{thm:app-de-gram}
Under \cref{assum:app-setup-regime}, in the frozen-state model with a weight
sequence $w$ satisfying \cref{eqn:app-de-weightclass}, let
$(\sigma,\tilde\sigma,\tilde s_1,s_1)(z)$ be the solution of the weighted
system \cref{eqn:app-de-system} for the weights $w$ and the spectral
measures \cref{eqn:app-setup-spectral-measures}, and let
$\Rbar,\Rtbar$ be as in \cref{eqn:app-de-Rbar}. Then for every compact
$I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-de-gram-closure}
\sup_{s\in I}\Big(\norm{\EE R(-s)-\Rbar(-s)}+\norm{\EE\widetilde R(-s)-\Rtbar(-s)}\Big)\longrightarrow0 .
\end{equation}
\end{theorem}
-/
theorem thm_app_de_gram (R : SetupRegime) (w : ℕ → ℝ) (hw : WeightClass w)
    {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)] (P : ∀ k, Measure (Ω k))
    [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k))
    (νo νi : ∀ k, FiniteMeasure ℝ)
    (hνo : ∀ k, (νo k : Measure ℝ) = nuOut (R.F k).C (R.B k))
    (hνi : ∀ k, (νi k : Measure ℝ) = nuIn (R.F k).C (R.B k))
    (t : ℤ) (I : Set ℝ) (hI : IsCompact I) (hIpos : I ⊆ Set.Ioi 0) :
    Tendsto (fun k => ⨆ s ∈ I,
      (opNorm (expRes w (R.F k) (S k) t s - Rbar (Fw w) (νo k) (νi k) (R.F k).C s) +
        opNorm (expResT w (R.F k) (S k) t s - Rtbar (Fw w) (νo k) (νi k) (R.F k).C s)))
      atTop (𝓝 0) :=
  gram_of_H w hw t I hI hIpos (gh_H w hw t I hI hIpos) R P S νo νi hνo hνi

end Muon.DetEquiv

end
