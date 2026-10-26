import Muon.Setup.Frozen
import Muon.DetEquiv.Scalar
import Muon.DetEquiv.Resolvent

/-!
# Appendix B: frozen sample model for a general weight sequence (task L-B.7)

Snapshot `cr-2026-10-23`. Source: `sections/02-deterministic-equivalents/section.tex`:
the sample representation `eqn:app-de-M-samples` (l.1126–1129), the sample series and
the expected resolvents `eqn:app-de-expected` (l.1193–1201), the bounds `eqn:app-de-qI`
(l.1202–1204), and the infinite-sample and deletion facts used by the Gram closure
(l.1125–1131, l.1486–1504, l.1655–1674, l.1240–1262).

This is a helper module: CARD §5 WP L-B.7 owns no label of its own. It reuses A's frozen
model (`Muon.Setup.FrozenParams`, `FrozenSamples`, `frozenBatchG`, `frozenBuf`, `frozenVB`,
`eucNorm`), the weight class `Muon.DetEquiv.WeightClass` and the resolvents
`Muon.DetEquiv.Rs`, `Muon.DetEquiv.Rts`. Nothing is redefined.

Representation choices:
* A's `frozenBuf` is hard-wired to the EMA weights `emaW F.β`. `WeightedBuf w` is the same series
  for an arbitrary weight sequence; `frozenBuf` is its EMA case (`weightedBuf_emaW_eq_frozenBuf`).
* Samples are indexed by time `s : ℤ` and by slot `a : Fin B`, as in A. The age-`j` sample of
  `M_t` sits at time `t + 1 - j`. Deleted buffers are indexed by the time and slot of the deleted
  sample, not by its age, so that independence and exchangeability read directly.
* `tsum` is junk off the summable set. Each statement that needs convergence carries it as a
  hypothesis, or is an a.s. statement (`weightedBuf_summable_ae`).
* Stage 1 (finitely supported weights) needs no probability. Stage 2 (the weight class, the
  infinite product of A's `FrozenSamples`, a.s. summability, `L²` truncation) is the list of
  `sorry`ed statements below.
-/

set_option linter.style.longLine false

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology Set
open Muon Muon.Setup

noncomputable section

namespace Muon.DetEquiv

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

/-! ## Sample terms and the general-weight buffer -/

/-- Summand of `frozenBatchG` for the slot `(s, a)`, before the factor `1/B`:
`(zᵀ Â w) Σout^{1/2} (z ⊗ w) Σin^{1/2}` (`def:app-setup-frozen`). -/
def sampleTerm (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B)
    (ω : Ω) : Mat m n :=
  (dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) •
    (rOut F.C * Muon.outer (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C)

/-- The batch is the normalized sum of its slot terms (`def:app-setup-frozen`). -/
theorem frozenBatchG_eq_sum (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
    (ω : Ω) :
    frozenBatchG F S s ω = ((B : ℝ))⁻¹ • ∑ a : Fin B, sampleTerm F S s a ω :=
  rfl

/-- General-weight buffer `M^w_t = ∑_{j ≥ 0} w_j G_{t+1-j}`: the buffer of
`def:app-setup-frozen` with `emaW β` replaced by an arbitrary weight sequence `w`. -/
def WeightedBuf (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ω : Ω) : Mat m n :=
  ∑' j : ℕ, w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω

/-- The EMA case of `WeightedBuf` is A's `frozenBuf`. -/
theorem weightedBuf_emaW_eq_frozenBuf (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (ω : Ω) :
    WeightedBuf (Muon.emaW F.β) F S t ω = frozenBuf F S t ω :=
  rfl

/-- Truncated buffer `M^{(J)}_t = ∑_{j ≤ J} w_j G_{t+1-j}` (the paper's `M^{(J)}`). -/
def WeightedBufTrunc (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (J : ℕ) (ω : Ω) : Mat m n :=
  ∑ j ∈ Finset.range (J + 1), w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω

/-- Buffer with the sample in slot `(s, a)` deleted: `M_0^{(s,a)}` of the Gram closure, i.e.
`WeightedBuf` minus the single term `w_j B^{-1} sampleTerm s a` for the age `j` with
`t + 1 - j = s`. It is a function of the samples other than `(s, a)` only. -/
def WeightedBufDel (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t s : ℤ)
    (a : Fin B) (ω : Ω) : Mat m n :=
  ∑' j : ℕ, w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if t + 1 - (j : ℤ) = s ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω)

/-- Finite support of a weight sequence: `w_j = 0` for all large `j`. -/
def FiniteSupport (w : ℕ → ℝ) : Prop := ∃ J : ℕ, ∀ j : ℕ, J < j → w j = 0

/-! ## Expected resolvents and traces (`eqn:app-de-expected`) -/

/-- Expected output-side resolvent `𝒫(s) = 𝔼 R(-s)` of the buffer `M^w_t`, with
`R(-s) = R_s(M^w_t)` (`eqn:app-de-RXdef`). Source (`section.tex` l.1193–1201):
```latex
\begin{equation}\label{eqn:app-de-expected}
\begin{gathered}
\mathcal P(s)\defeq\EE R(-s),\qquad \mathcal P_j(s)\defeq\EE R_0^{(j1)},\\
\sigma_B(s)\defeq\frac1B\Tr\big(\Sigmaout\mathcal P(s)\big),\qquad
\tilde\sigma_B(s)\defeq\frac1B\Tr\big(\Sigmain\,\EE\widetilde R(-s)\big),
\end{gathered}
\end{equation}
and $q_B(s)\defeq s\sigma_B(s)\tilde\sigma_B(s)$.
```
-/
def expRes (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    Mat m m :=
  Muon.mean P (fun ω => Rs (WeightedBuf w F S t ω) s)

/-- Expected input-side resolvent `𝔼 R̃(-s)` of `M^w_t` (`eqn:app-de-expected`). -/
def expResT (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    Mat n n :=
  Muon.mean P (fun ω => Rts (WeightedBuf w F S t ω) s)

/-- `𝒫_j(s) = 𝔼 R_0^{(j,a)}`: expected resolvent of the buffer with the sample of age `j`
in slot `a` deleted (`eqn:app-de-expected`; the paper takes `a = 1`, i.e. slot `0`). -/
def expDelRes (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ)
    (a : Fin B) (s : ℝ) : Mat m m :=
  Muon.mean P (fun ω => Rs (WeightedBufDel w F S t (t + 1 - (j : ℤ)) a ω) s)

/-- `σ_B(s) = (1/B) Tr(Σout 𝒫(s))` (`eqn:app-de-expected`). -/
def sigmaB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    ℝ :=
  ((B : ℝ))⁻¹ * (F.C.Sout * expRes w F S t s).trace

/-- `σ̃_B(s) = (1/B) Tr(Σin 𝔼 R̃(-s))` (`eqn:app-de-expected`). -/
def sigmaTildeB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (s : ℝ) : ℝ :=
  ((B : ℝ))⁻¹ * (F.C.Sin * expResT w F S t s).trace

/-- `q_B(s) = s σ_B(s) σ̃_B(s)` (`eqn:app-de-expected`). -/
def qB (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) : ℝ :=
  s * sigmaB w F S t s * sigmaTildeB w F S t s

/-! ## Stage 1: finitely supported weights (no probability) -/

/-- Finitely supported weights: the buffer series is a finite sum, so `tsum` is an honest sum.
Stage 1 of CARD §5 (L-B.7). -/
theorem weightedBuf_eq_trunc_of_finiteSupport (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) (hJ : ∀ j : ℕ, J < j → w j = 0) (ω : Ω) :
    WeightedBuf w F S t ω = WeightedBufTrunc w F S t J ω := by
  unfold WeightedBuf WeightedBufTrunc
  apply tsum_eq_sum
  intro j hj
  rw [Finset.mem_range] at hj
  simp [hJ j (by omega)]

/-- Private: `r_out (z ⊗ w) r_in = (r_out z) ⊗ (r_in w)`, using `r_in` symmetric. -/
private lemma rOut_outer_rIn_eq (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
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

/-- Private: scaling both factors of an outer product by `c`. -/
private lemma outer_smul_smul_eq (c : ℝ) (x : Vec m) (y : Vec n) :
    outer (c • x) (c • y) = (c * c) • outer x y := by
  ext i j
  simp only [outer, Matrix.vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Sample-series form of the buffer (`eqn:app-de-M-samples`): with `h_{ja} = w_j d_{ja}`,
`u_{ja} = Σout^{1/2} z_{ja}/√B`, `v_{ja} = Σin^{1/2} w_{ja}/√B`, the buffer is
`∑_j ∑_a h_{ja} u_{ja} ⊗ v_{ja}`. The sample of age `j` is at time `t + 1 - j`. Holds at every
`ω`, with the iterated `tsum` on the right. Source (`section.tex` l.1126–1129):
\begin{equation}\label{eqn:app-de-M-samples}
\Mt=\sum_{j\ge0}\sum_{a=1}^B\mathsf h_{ja}\,\mathsf u_{ja}\tensor\mathsf v_{ja},\qquad
\mathsf h_{ja}\defeq\emaw{j}d_{ja},\quad
\mathsf u_{ja}\defeq\frac{\Sigmaout^{1/2}z_{ja}}{\sqrt B},\quad
-/
theorem eqn_app_de_M_samples (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (ω : Ω) :
    WeightedBuf w F S t ω =
      ∑' j : ℕ, ∑ a : Fin B,
        (w j * dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1
            (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
          Muon.outer ((Real.sqrt (B : ℝ))⁻¹ • Matrix.mulVec (rOut F.C) (S.zw (t + 1 - (j : ℤ)) a ω).1)
            ((Real.sqrt (B : ℝ))⁻¹ • Matrix.mulVec (rIn F.C) (S.zw (t + 1 - (j : ℤ)) a ω).2) := by
  have hB : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt (Nat.cast_nonneg B)]
  unfold WeightedBuf
  refine tsum_congr (fun j => ?_)
  rw [frozenBatchG_eq_sum, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  unfold sampleTerm
  rw [rOut_outer_rIn_eq, outer_smul_smul_eq, hB]
  simp only [smul_smul]
  congr 1
  ring

/-! ## Stage 2: the weight class, a.s. summability and sample deletion -/

/-! ### Helpers for the a.s. summability (Tonelli over the samples) -/

private lemma sq_coord_integrable' (n : ℕ) (i : Fin n) :
    Integrable (fun z : Fin n → ℝ => z i ^ 2) (Muon.Foundations.stdGaussianPi n) := by
  have hm : MeasurePreserving (fun z : Fin n → ℝ => z i) (Muon.Foundations.stdGaussianPi n)
      (gaussianReal 0 1) := measurePreserving_eval _ i
  exact (hm.integrable_comp (g := fun x : ℝ => x ^ 2) (by fun_prop)).2
    (Muon.Foundations.gaussian_integrable_pow 2)

private lemma sum_sq_integrable' (n : ℕ) :
    Integrable (fun z : Fin n → ℝ => ∑ i, z i ^ 2) (Muon.Foundations.stdGaussianPi n) :=
  integrable_finsetSum _ (fun i _ => sq_coord_integrable' n i)

private lemma prod_sq_lintegral_lt_top (m n : ℕ) :
    ∫⁻ x, ENNReal.ofReal ((∑ i, x.1 i ^ 2) * (∑ k, x.2 k ^ 2))
      ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) < ⊤ :=
  ((sum_sq_integrable' m).mul_prod (sum_sq_integrable' n)).lintegral_lt_top

private lemma eucNorm_sq' {k : ℕ} (z : Vec k) : eucNorm z ^ 2 = ∑ i, z i ^ 2 := by
  unfold eucNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

private lemma eucNorm_nonneg' {k : ℕ} (z : Vec k) : 0 ≤ eucNorm z := by
  unfold eucNorm
  exact Real.sqrt_nonneg _

/-- Cauchy-Schwarz: `|zᵀ A v| ≤ ‖z‖ ‖v‖` when `‖A‖_F = 1`. -/
private lemma abs_dot_le_eucNorm {m n : ℕ} (A : Mat m n) (hA : fro A = 1) (z : Vec m) (v : Vec n) :
    |dotProduct z (Matrix.mulVec A v)| ≤ eucNorm z * eucNorm v := by
  have hfro : ∑ i, ∑ k, A i k ^ 2 = 1 := by
    have h2 := (Real.sqrt_eq_one).1 hA
    simpa [Real.norm_eq_abs, sq_abs] using h2
  have hcs : (∑ p : Fin m × Fin n, A p.1 p.2 * (z p.1 * v p.2)) ^ 2 ≤
      (∑ p : Fin m × Fin n, A p.1 p.2 ^ 2) * (∑ p : Fin m × Fin n, (z p.1 * v p.2) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsum : dotProduct z (Matrix.mulVec A v) =
      ∑ p : Fin m × Fin n, A p.1 p.2 * (z p.1 * v p.2) := by
    simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hg : ∑ p : Fin m × Fin n, (z p.1 * v p.2) ^ 2 = (∑ i, z i ^ 2) * (∑ k, v k ^ 2) := by
    rw [Finset.sum_mul_sum, Fintype.sum_prod_type]
    simp [mul_pow]
  have hf : ∑ p : Fin m × Fin n, A p.1 p.2 ^ 2 = 1 := by
    rw [Fintype.sum_prod_type]
    exact hfro
  rw [hf, hg, one_mul, ← hsum] at hcs
  have hprod : eucNorm z * eucNorm v = Real.sqrt ((∑ i, z i ^ 2) * (∑ k, v k ^ 2)) := by
    unfold eucNorm
    rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  rw [hprod]
  exact Real.abs_le_sqrt hcs

/-- Pointwise sample bound: `c |zᵀ A v| ‖z‖ ‖v‖ ≤ c ‖z‖² ‖v‖²` for `c ≥ 0`. -/
private lemma sample_bound {m n : ℕ} (A : Mat m n) (hA : fro A = 1) (c : ℝ) (hc : 0 ≤ c)
    (z : Vec m) (v : Vec n) :
    c * (|dotProduct z (Matrix.mulVec A v)| * eucNorm z * eucNorm v) ≤
      c * ((∑ i, z i ^ 2) * (∑ k, v k ^ 2)) := by
  have h1 := abs_dot_le_eucNorm A hA z v
  have hz := eucNorm_nonneg' z
  have hv := eucNorm_nonneg' v
  have h3 : (eucNorm z * eucNorm v) * (eucNorm z * eucNorm v) =
      (∑ i, z i ^ 2) * (∑ k, v k ^ 2) := by
    rw [← eucNorm_sq' z, ← eucNorm_sq' v]
    ring
  have h2 : |dotProduct z (Matrix.mulVec A v)| * eucNorm z * eucNorm v ≤
      (eucNorm z * eucNorm v) * (eucNorm z * eucNorm v) := by
    calc |dotProduct z (Matrix.mulVec A v)| * eucNorm z * eucNorm v
        = |dotProduct z (Matrix.mulVec A v)| * (eucNorm z * eucNorm v) := by ring
      _ ≤ (eucNorm z * eucNorm v) * (eucNorm z * eucNorm v) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hz hv)
  calc c * (|dotProduct z (Matrix.mulVec A v)| * eucNorm z * eucNorm v)
      ≤ c * ((eucNorm z * eucNorm v) * (eucNorm z * eucNorm v)) :=
        mul_le_mul_of_nonneg_left h2 hc
    _ = c * ((∑ i, z i ^ 2) * (∑ k, v k ^ 2)) := by rw [h3]

/-- For each time `t`, the sample series is a.s. absolutely summable (Tonelli + Gaussian
moments of `‖z‖²‖w‖²`). -/
private lemma sample_summable_time [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightSeq w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    ∀ᵐ ω ∂P, Summable fun p : ℕ × Fin B =>
      w p.1 * |dotProduct (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1
          (Matrix.mulVec F.A (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2)| *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1 *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2 := by
  let Φ : Vec m × Vec n → ℝ := fun x =>
    |dotProduct x.1 (Matrix.mulVec F.A x.2)| * eucNorm x.1 * eucNorm x.2
  let g : Vec m × Vec n → ℝ := fun x => (∑ i, x.1 i ^ 2) * (∑ k, x.2 k ^ 2)
  have hΦm : Measurable Φ := by
    have hc : Continuous Φ := by
      simp only [Φ, eucNorm, dotProduct, Matrix.mulVec]
      fun_prop
    exact hc.measurable
  have hgm : Measurable g := by
    have hc : Continuous g := by
      simp only [g]
      fun_prop
    exact hc.measurable
  set K := ∫⁻ x, ENNReal.ofReal (g x)
    ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) with hKdef
  have hKfin : K < ⊤ := prod_sq_lintegral_lt_top m n
  have hlint : ∀ s a, ∫⁻ ω, ENNReal.ofReal (g (S.zw s a ω)) ∂P = K := by
    intro s a
    rw [hKdef, ← lintegral_map hgm.ennreal_ofReal (S.meas s a), S.law s a]
  have hbound : ∀ (j : ℕ) (a : Fin B),
      ∫⁻ ω, ENNReal.ofReal (w j * Φ (S.zw (t + 1 - (j : ℤ)) a ω)) ∂P
        ≤ ENNReal.ofReal (w j) * K := by
    intro j a
    calc ∫⁻ ω, ENNReal.ofReal (w j * Φ (S.zw (t + 1 - (j : ℤ)) a ω)) ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (w j) * ENNReal.ofReal (g (S.zw (t + 1 - (j : ℤ)) a ω)) ∂P := by
          refine lintegral_mono (fun ω => ?_)
          rw [← ENNReal.ofReal_mul (hw.1 j)]
          exact ENNReal.ofReal_le_ofReal (sample_bound F.A F.hA (w j) (hw.1 j) _ _)
      _ = ENNReal.ofReal (w j) * K := by
          have hm2 : Measurable (fun ω => ENNReal.ofReal (g (S.zw (t + 1 - (j : ℤ)) a ω))) :=
            (hgm.comp (S.meas _ _)).ennreal_ofReal
          rw [lintegral_const_mul _ hm2, hlint]
  have hmeas : ∀ p : ℕ × Fin B, Measurable fun ω =>
      ENNReal.ofReal (w p.1 * Φ (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω)) := fun p =>
    (((hΦm.comp (S.meas _ _)).const_mul (w p.1))).ennreal_ofReal
  have hfin : ∑' p : ℕ × Fin B, ENNReal.ofReal (w p.1) =
      (B : ENNReal) * ENNReal.ofReal (∑' j, w j) := by
    rw [show (∑' p : ℕ × Fin B, ENNReal.ofReal (w p.1)) =
        ∑' a : ℕ, ∑' b : Fin B, ENNReal.ofReal (w a) from
          ENNReal.tsum_prod (f := fun a _ => ENNReal.ofReal (w a))]
    rw [ENNReal.ofReal_tsum_of_nonneg (fun j => hw.1 j) hw.2.1]
    simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [ENNReal.tsum_mul_left]
  have hsum_lint : ∫⁻ ω, ∑' p : ℕ × Fin B,
      ENNReal.ofReal (w p.1 * Φ (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω)) ∂P ≠ ⊤ := by
    rw [lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun p => hbound p.1 p.2) ?_)
    rw [ENNReal.tsum_mul_right, hfin]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.natCast_lt_top B)
      ENNReal.ofReal_lt_top) hKfin
  have hae := ae_lt_top (Measurable.ennreal_tsum fun p => hmeas p) hsum_lint
  filter_upwards [hae] with ω hω
  refine (ENNReal.summable_toReal hω.ne).congr (fun p => ?_)
  rw [ENNReal.toReal_ofReal (mul_nonneg (hw.1 _)
    (mul_nonneg (mul_nonneg (abs_nonneg _) (eucNorm_nonneg' _)) (eucNorm_nonneg' _)))]
  ring

private lemma abs_le_eucNorm' {k : ℕ} (z : Vec k) (p : Fin k) : |z p| ≤ eucNorm z := by
  unfold eucNorm
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => z i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ p))

/-- Entrywise bound on `L (z ⊗ v) R`: `|(L (z ⊗ v) R)_{ik}| ≤ (∑_{p,q} |L_{ip}||R_{qk}|) ‖z‖‖v‖`. -/
private lemma outer_entry_bound {m n : ℕ} (L : Mat m m) (R : Mat n n) (z : Vec m) (v : Vec n)
    (i : Fin m) (k : Fin n) :
    |(L * Muon.outer z v * R) i k| ≤
      (∑ p, ∑ q, |L i p| * |R q k|) * (eucNorm z * eucNorm v) := by
  have hexp : (L * Muon.outer z v * R) i k = ∑ p, ∑ q, L i p * (z p * v q) * R q k := by
    simp only [Matrix.mul_apply, Muon.outer, Matrix.vecMulVec_apply, Finset.sum_mul]
    refine (Finset.sum_comm).trans ?_
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by ring
  have hterm : ∀ p q, |L i p * (z p * v q) * R q k| ≤
      (|L i p| * |R q k|) * (eucNorm z * eucNorm v) := by
    intro p q
    rw [abs_mul, abs_mul, abs_mul]
    have hz : |z p| ≤ eucNorm z := abs_le_eucNorm' z p
    have hv : |v q| ≤ eucNorm v := abs_le_eucNorm' v q
    have h0 : 0 ≤ |L i p| * |R q k| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |L i p| * (|z p| * |v q|) * |R q k|
        = (|L i p| * |R q k|) * (|z p| * |v q|) := by ring
      _ ≤ (|L i p| * |R q k|) * (eucNorm z * eucNorm v) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hz hv (abs_nonneg _) (eucNorm_nonneg' _)) h0
  rw [hexp]
  calc |∑ p, ∑ q, L i p * (z p * v q) * R q k|
      ≤ ∑ p, |∑ q, L i p * (z p * v q) * R q k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, |L i p * (z p * v q) * R q k| :=
        Finset.sum_le_sum fun p _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p, ∑ q, (|L i p| * |R q k|) * (eucNorm z * eucNorm v) :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hterm p q
    _ = (∑ p, ∑ q, |L i p| * |R q k|) * (eucNorm z * eucNorm v) := by
        simp only [Finset.sum_mul]

/-- Pull a constant factor through a finite sum (generic form, avoids pushing constants into
inner sums). -/
private lemma sum_factor_eq {ι : Type*} (w b K : ℝ) (s : Finset ι) (f T : ι → ℝ)
    (h : ∀ a, w * (b * f a) = (b * K) * T a) :
    w * (b * ∑ a ∈ s, f a) = (b * K) * ∑ a ∈ s, T a := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => h a

/-- Entry of one batch as the normalized sum of the slot terms. -/
private lemma batch_entry (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω)
    (i : Fin m) (k : Fin n) :
    frozenBatchG F S s ω i k = (B : ℝ)⁻¹ * ∑ a : Fin B,
      dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2) *
        (rOut F.C * Muon.outer (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C) i k := by
  rw [frozenBatchG_eq_sum]
  simp only [Matrix.smul_apply, Matrix.sum_apply, sampleTerm, smul_eq_mul]

/-- A.s. summability of the buffer series, for every time, for a nonnegative summable weight
sequence. Extends `lem_app_setup_ema_law_i` (EMA only) to `WeightSeq`. -/
theorem weightedBuf_summable_ae [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightSeq w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω := by
  have hall : ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun p : ℕ × Fin B =>
      w p.1 * |dotProduct (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1
          (Matrix.mulVec F.A (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2)| *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1 *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2 :=
    ae_all_iff.2 (fun t => sample_summable_time w hw F S t)
  filter_upwards [hall] with ω hω
  intro t
  refine Pi.summable.2 fun i => Pi.summable.2 fun k => ?_
  -- per-age, per-slot summability of the absolute sample terms
  have hQ : Summable fun j : ℕ => ∑ a : Fin B,
      w j * |dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1
          (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)| *
        eucNorm (S.zw (t + 1 - (j : ℤ)) a ω).1 *
        eucNorm (S.zw (t + 1 - (j : ℤ)) a ω).2 := by
    refine summable_sum fun a _ => ?_
    exact (hω t).comp_injective (i := fun j : ℕ => ((j, a) : ℕ × Fin B))
      (fun j1 j2 h => by simpa using h)
  refine Summable.of_norm_bounded (hQ.mul_left ((B : ℝ)⁻¹ *
    ∑ p : Fin m, ∑ q : Fin n, |rOut F.C i p| * |rIn F.C q k|)) (fun j => ?_)
  rw [Matrix.smul_apply, smul_eq_mul, batch_entry, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (hw.1 j)]
  have hX : |∑ a : Fin B, dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1
        (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2) *
      (rOut F.C * Muon.outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 *
        rIn F.C) i k| ≤
      ∑ a : Fin B, |dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1
          (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)| *
        ((∑ p : Fin m, ∑ q : Fin n, |rOut F.C i p| * |rIn F.C q k|) *
          (eucNorm (S.zw (t + 1 - (j : ℤ)) a ω).1 * eucNorm (S.zw (t + 1 - (j : ℤ)) a ω).2)) :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (outer_entry_bound _ _ _ _ i k) (abs_nonneg _))
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ)⁻¹)]
  refine (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (by positivity)) (hw.1 j)).trans
    (le_of_eq ?_)
  exact sum_factor_eq _ _ _ _ _ _ (fun a => by ring)

/-- A.s. absolute summability of the sample series `∑_{j,a} w_j |d_{ja}| ‖z_{ja}‖ ‖w_{ja}‖`,
for every time, for `WeightSeq w`. This is the domination needed to exchange the sample sum
with expectation (CARD §6.8). -/
theorem weightedBuf_sample_summable_ae [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightSeq w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    ∀ᵐ ω ∂P, ∀ t : ℤ, Summable fun p : ℕ × Fin B =>
      w p.1 *
        |dotProduct (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1
            (Matrix.mulVec F.A (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2)| *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).1 *
        eucNorm (S.zw (t + 1 - (p.1 : ℤ)) p.2 ω).2 :=
  ae_all_iff.2 (fun t => sample_summable_time w hw F S t)

/-- One slot entry `(zᵀ A w) (Σout^{1/2} (z ⊗ w) Σin^{1/2})_{ik}` as a function of `(z, w)`. -/
private def slotEntry (F : FrozenParams m n B) (i : Fin m) (k : Fin n) (x : Vec m × Vec n) : ℝ :=
  dotProduct x.1 (Matrix.mulVec F.A x.2) * (rOut F.C * Muon.outer x.1 x.2 * rIn F.C) i k

/-- The sample weight `‖z‖² ‖w‖²` of one sample. -/
private def sqProd (x : Vec m × Vec n) : ℝ := (∑ i, x.1 i ^ 2) * (∑ k, x.2 k ^ 2)

private lemma sqProd_continuous : Continuous (sqProd : Vec m × Vec n → ℝ) := by
  unfold sqProd
  fun_prop

private lemma slotEntry_continuous (F : FrozenParams m n B) (i : Fin m) (k : Fin n) :
    Continuous (slotEntry F i k) := by
  unfold slotEntry
  simp only [dotProduct, Matrix.mulVec, Muon.outer, Matrix.mul_apply, Matrix.vecMulVec_apply]
  fun_prop

private lemma slotEntry_bound (F : FrozenParams m n B) (i : Fin m) (k : Fin n)
    (x : Vec m × Vec n) :
    |slotEntry F i k x| ≤ (∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * sqProd x := by
  unfold slotEntry sqProd
  have h1 := abs_dot_le_eucNorm F.A F.hA x.1 x.2
  have h2 := outer_entry_bound (rOut F.C) (rIn F.C) x.1 x.2 i k
  have hz := eucNorm_nonneg' x.1
  have hv := eucNorm_nonneg' x.2
  rw [abs_mul]
  calc |dotProduct x.1 (Matrix.mulVec F.A x.2)| * |(rOut F.C * Muon.outer x.1 x.2 * rIn F.C) i k|
      ≤ (eucNorm x.1 * eucNorm x.2) *
          ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * (eucNorm x.1 * eucNorm x.2)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hz hv)
    _ = (∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
          ((∑ i, x.1 i ^ 2) * (∑ k, x.2 k ^ 2)) := by
        rw [← eucNorm_sq' x.1, ← eucNorm_sq' x.2]
        ring

private lemma sqProd_sample_integrable [IsProbabilityMeasure P] (S : FrozenSamples P m n B)
    (s : ℤ) (a : Fin B) : Integrable (fun ω => sqProd (S.zw s a ω)) P := by
  have hg : Integrable (sqProd : Vec m × Vec n → ℝ)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) :=
    (sum_sq_integrable' m).mul_prod (sum_sq_integrable' n)
  have hgm : AEStronglyMeasurable (sqProd : Vec m × Vec n → ℝ) (P.map (S.zw s a)) := by
    rw [S.law s a]
    exact hg.aestronglyMeasurable
  exact (integrable_map_measure hgm (S.meas s a).aemeasurable).1 (by rw [S.law s a]; exact hg)

private lemma slotEntry_sample_integrable [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => slotEntry F i k (S.zw s a ω)) P := by
  refine Integrable.mono'
    ((sqProd_sample_integrable S s a).const_mul (∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|))
    ((slotEntry_continuous F i k).measurable.comp (S.meas s a)).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    exact slotEntry_bound F i k (S.zw s a ω)

private lemma sample_integral_eq [IsProbabilityMeasure P] (S : FrozenSamples P m n B) (s : ℤ)
    (a : Fin B) (f : Vec m × Vec n → ℝ) (hf : Continuous f) :
    ∫ ω, f (S.zw s a ω) ∂P =
      ∫ x, f x ∂((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  rw [← S.law s a]
  exact (integral_map (S.meas s a).aemeasurable hf.aestronglyMeasurable).symm

private lemma batch_entry_slot (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
    (ω : Ω) (i : Fin m) (k : Fin n) :
    frozenBatchG F S s ω i k = (B : ℝ)⁻¹ * ∑ a : Fin B, slotEntry F i k (S.zw s a ω) :=
  batch_entry F S s ω i k

private lemma batch_entry_integrable [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => frozenBatchG F S s ω i k) P := by
  have hfun : (fun ω => frozenBatchG F S s ω i k) =
      fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, slotEntry F i k (S.zw s a ω) :=
    funext fun ω => batch_entry_slot F S s ω i k
  rw [hfun]
  exact (integrable_finset_sum _ fun a _ => slotEntry_sample_integrable F S s a i k).const_mul _

private lemma batch_entry_integral [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (k : Fin n) :
    ∫ ω, frozenBatchG F S s ω i k ∂P = (B : ℝ)⁻¹ * ∑ a : Fin B,
      ∫ x, slotEntry F i k x ∂((Muon.Foundations.stdGaussianPi m).prod
        (Muon.Foundations.stdGaussianPi n)) := by
  have hfun : (fun ω => frozenBatchG F S s ω i k) =
      fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, slotEntry F i k (S.zw s a ω) :=
    funext fun ω => batch_entry_slot F S s ω i k
  rw [hfun, integral_const_mul, integral_finset_sum _ fun a _ =>
    slotEntry_sample_integrable F S s a i k]
  congr 1
  exact Finset.sum_congr rfl fun a _ => sample_integral_eq S s a _ (slotEntry_continuous F i k)

/-- Common `L¹` bound for the entries of the batches: `∫ |G_{s,ik}| ≤ batchNormBound`, uniformly
in the time `s`. -/
private def batchNormBound (F : FrozenParams m n B) (i : Fin m) (k : Fin n) : ℝ :=
  (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
    ∑ a : Fin B, ∫ x, sqProd x ∂((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)))

private lemma batch_entry_norm_integral_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (k : Fin n) :
    ∫ ω, ‖frozenBatchG F S s ω i k‖ ∂P ≤ batchNormBound F i k := by
  have hpt : ∀ ω, ‖frozenBatchG F S s ω i k‖ ≤
      (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
        ∑ a : Fin B, sqProd (S.zw s a ω)) := by
    intro ω
    rw [Real.norm_eq_abs, batch_entry_slot, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (B : ℝ)⁻¹), Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun a _ => slotEntry_bound F i k (S.zw s a ω))
  have hint : Integrable (fun ω => (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
      ∑ a : Fin B, sqProd (S.zw s a ω))) P :=
    (((integrable_finset_sum _ fun a _ => sqProd_sample_integrable S s a).const_mul _)).const_mul _
  calc ∫ ω, ‖frozenBatchG F S s ω i k‖ ∂P
      ≤ ∫ ω, (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) *
          ∑ a : Fin B, sqProd (S.zw s a ω)) ∂P :=
        integral_mono (batch_entry_integrable F S s i k).norm hint hpt
    _ = batchNormBound F i k := by
        unfold batchNormBound
        rw [integral_const_mul, integral_const_mul,
          integral_finset_sum _ fun a _ => sqProd_sample_integrable S s a]
        exact congrArg (fun z => (B : ℝ)⁻¹ * ((∑ p, ∑ q, |rOut F.C i p| * |rIn F.C q k|) * z))
          (Finset.sum_congr rfl fun a _ => sample_integral_eq S s a sqProd sqProd_continuous)

/-- Expectation of the buffer: the sum over samples commutes with `𝔼` under the weight class,
and each batch has the common mean `𝔼 G_0` (`lem_app_setup_gaussian_moments`(iii)). -/
theorem mean_weightedBuf [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    Muon.mean P (fun ω => WeightedBuf w F S t ω) =
      (∑' j : ℕ, w j) • Muon.mean P (frozenBatchG F S 0) := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  have hae := weightedBuf_summable_ae w hw.1 F S
  have hcongr : ∫ ω, WeightedBuf w F S t ω i k ∂P =
      ∫ ω, ∑' j : ℕ, w j * frozenBatchG F S (t + 1 - (j : ℤ)) ω i k ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with ω hω
    have hs := hω t
    unfold WeightedBuf
    have hi : ∀ x : Fin m, (∑' j : ℕ, w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω : Mat m n) x =
        ∑' j : ℕ, (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω : Mat m n) x :=
      fun x => Pi.tsum_apply (x := x) hs
    have hk : ∀ y : Fin n, (∑' j : ℕ, (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω : Mat m n) i) y =
        ∑' j : ℕ, (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω : Mat m n) i y :=
      fun y => Pi.tsum_apply (x := y) (Pi.summable.1 hs i)
    rw [hi i, hk k]
    simp only [Matrix.smul_apply, smul_eq_mul]
  have hint : ∀ j : ℕ, Integrable (fun ω => w j * frozenBatchG F S (t + 1 - (j : ℤ)) ω i k) P :=
    fun j => (batch_entry_integrable F S _ i k).const_mul (w j)
  have hnorm_sum : Summable (fun j : ℕ =>
      ∫ ω, ‖w j * frozenBatchG F S (t + 1 - (j : ℤ)) ω i k‖ ∂P) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => norm_nonneg _)
      (fun j => ?_) (hw.1.2.1.mul_right (batchNormBound F i k))
    simp only [norm_mul, Real.norm_of_nonneg (hw.1.1 j)]
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (batch_entry_norm_integral_le F S _ i k) (hw.1.1 j)
  have hconst : ∀ s : ℤ, ∫ ω, frozenBatchG F S s ω i k ∂P =
      ∫ ω, frozenBatchG F S 0 ω i k ∂P := fun s => by
    rw [batch_entry_integral, batch_entry_integral]
  have hterm : ∀ j : ℕ, ∫ ω, w j * frozenBatchG F S (t + 1 - (j : ℤ)) ω i k ∂P =
      w j * ∫ ω, frozenBatchG F S 0 ω i k ∂P := fun j => by
    rw [integral_const_mul, hconst]
  rw [hcongr, ← integral_tsum_of_summable_integral_norm hint hnorm_sum, tsum_congr hterm,
    tsum_mul_right]

/-- Private: removing one slot from a finite sum of matrices and adding it back. -/
private lemma sum_ite_erase_add_eq (a : Fin B) (T : Fin B → Mat m n) :
    ∑ b : Fin B, (if b = a then (0 : Mat m n) else T b) + T a = ∑ b : Fin B, T b := by
  have h : ∀ b : Fin B, (if b = a then (0 : Mat m n) else T b) =
      T b - (if b = a then T b else 0) := by
    intro b
    by_cases hb : b = a
    · simp [hb]
    · simp [hb]
  rw [Finset.sum_congr rfl (fun b _ => h b), Finset.sum_sub_distrib]
  simp

/-- Deletion identity: when the buffer series is summable at `ω`, removing the slot `(s, a)`
(the age `j0` with `t + 1 - j0 = s`) from `WeightedBuf` subtracts the single term
`w_{j0} B^{-1} sampleTerm s a`. -/
theorem weightedBuf_eq_del_add (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s : ℤ) (a : Fin B) (j0 : ℕ) (hs : s = t + 1 - (j0 : ℤ)) (ω : Ω)
    (hsum : Summable fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :
    WeightedBuf w F S t ω =
      WeightedBufDel w F S t s a ω + w j0 • ((B : ℝ)⁻¹ • sampleTerm F S s a ω) := by
  have hterm : ∀ j : ℕ, w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω =
      w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
          if t + 1 - (j : ℤ) = s ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω)
        + (if j = j0 then w j0 • ((B : ℝ)⁻¹ • sampleTerm F S s a ω) else 0) := by
    intro j
    rw [frozenBatchG_eq_sum]
    by_cases hj : j = j0
    · subst hj
      have hts : t + 1 - (j : ℤ) = s := hs.symm
      simp only [hts, true_and, if_true]
      rw [← smul_add, ← smul_add, sum_ite_erase_add_eq]
    · have hne : t + 1 - (j : ℤ) ≠ s := by
        intro h
        apply hj
        omega
      simp only [if_neg hj, add_zero, hne, false_and, if_false]
  have hh : Summable fun j : ℕ => (if j = j0 then w j0 • ((B : ℝ)⁻¹ • sampleTerm F S s a ω) else 0) :=
    (hasSum_ite_eq j0 _).summable
  have hg : Summable fun j : ℕ => w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
          if t + 1 - (j : ℤ) = s ∧ b = a then 0 else sampleTerm F S (t + 1 - (j : ℤ)) b ω) :=
    (hsum.sub hh).congr (fun j => by rw [hterm j, add_sub_cancel_right])
  unfold WeightedBuf WeightedBufDel
  rw [tsum_congr hterm, hg.tsum_add hh, tsum_ite_eq]

/-- Private: the summand of one sample pair `x = (z, w)` (`sampleTerm` without the slot). -/
private def wbQ (F : FrozenParams m n B) (x : Vec m × Vec n) : Mat m n :=
  (dotProduct x.1 (Matrix.mulVec F.A x.2)) • (rOut F.C * Muon.outer x.1 x.2 * rIn F.C)

/-- Private: the deleted buffer as a function of the whole family `f : (s', b) ↦ (z, w)`. -/
private def wbDelF (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a : Fin B)
    (f : ℤ × Fin B → Vec m × Vec n) : Mat m n :=
  ∑' j : ℕ, w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if t + 1 - (j : ℤ) = s ∧ b = a then 0 else wbQ F (f (t + 1 - (j : ℤ), b)))

/-- Private: the family-level pair `(deleted buffer, sample at (s, a))`. -/
private def wbPairF (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a : Fin B)
    (f : ℤ × Fin B → Vec m × Vec n) : Mat m n × (Vec m × Vec n) :=
  (wbDelF w F t s a f, f (s, a))

/-- Private: the slot swap `a ↔ b` at time `s` acting on families. -/
private def wbSwapF (s : ℤ) (a b : Fin B) (f : ℤ × Fin B → Vec m × Vec n) :
    ℤ × Fin B → Vec m × Vec n :=
  fun p => f (Equiv.swap (s, a) (s, b) p)

private lemma wbDel_eq_wbDelF (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s : ℤ) (a : Fin B) (ω : Ω) :
    WeightedBufDel w F S t s a ω = wbDelF w F t s a (fun p => S.zw p.1 p.2 ω) := rfl

private lemma wbQ_measurable (F : FrozenParams m n B) : Measurable (wbQ F) := by
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
  unfold wbQ
  exact hdot.smul hM

private lemma wbDel_summand_meas (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a : Fin B)
    (j : ℕ) : Measurable (fun f : ℤ × Fin B → Vec m × Vec n => w j • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if t + 1 - (j : ℤ) = s ∧ b = a then (0 : Mat m n) else wbQ F (f (t + 1 - (j : ℤ), b)))) := by
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hsum : Measurable (fun f : ℤ × Fin B → Vec m × Vec n => ∑ b : Fin B,
      if t + 1 - (j : ℤ) = s ∧ b = a then (0 : Mat m n) else wbQ F (f (t + 1 - (j : ℤ), b))) := by
    refine Finset.measurable_sum _ (fun b _ => ?_)
    by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
    · simp only [if_pos h]; exact measurable_const
    · simp only [if_neg h]; exact (wbQ_measurable F).comp (measurable_pi_apply _)
  exact (hsum.const_smul ((B : ℝ)⁻¹)).const_smul (w j)

private lemma wbDelF_measurable (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a : Fin B) :
    Measurable (wbDelF w F t s a) := by
  unfold wbDelF
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  exact Measurable.tsum (fun j => wbDel_summand_meas w F t s a j)

/-- Private: measurability of a map into a Pi type with respect to an explicit σ-algebra. -/
private lemma wb_measurable_pi_sub {α δ : Type*} {X : δ → Type*} [∀ a, MeasurableSpace (X a)]
    (M : MeasurableSpace α) (g : α → ∀ a, X a) (h : ∀ a, Measurable[M] (fun x => g x a)) :
    Measurable[M] g := by
  letI : MeasurableSpace α := M
  exact measurable_pi_iff.mpr h

private lemma wbSwapF_measurable (s : ℤ) (a b : Fin B) : Measurable (wbSwapF (m := m) (n := n) s a b) :=
  measurable_pi_iff.mpr (fun p => measurable_pi_apply _)

private lemma wbPairF_measurable (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a : Fin B) :
    Measurable (wbPairF w F t s a) :=
  (wbDelF_measurable w F t s a).prodMk (measurable_pi_apply _)

/-- Private: the deleted buffer is `wbDelF` of the family with the `(s, a)` coordinate replaced
by `0` (the coordinate is never read). -/
private lemma wbDelF_swap (w : ℕ → ℝ) (F : FrozenParams m n B) (t s : ℤ) (a b : Fin B)
    (f : ℤ × Fin B → Vec m × Vec n) :
    wbDelF w F t s b (fun p => f (Equiv.swap (s, a) (s, b) p)) = wbDelF w F t s a f := by
  unfold wbDelF
  refine tsum_congr (fun j => ?_)
  by_cases hj : t + 1 - (j : ℤ) = s
  · have hswap : ∀ c : Fin B, Equiv.swap (s, a) (s, b) (s, c) = (s, Equiv.swap a b c) := by
      intro c
      by_cases hca : c = a <;> by_cases hcb : c = b <;>
        simp [Equiv.swap_apply_def, hca, hcb, Prod.ext_iff]
    have hsum : ∑ c : Fin B, (if c = b then (0 : Mat m n) else wbQ F (f (s, Equiv.swap a b c))) =
        ∑ c : Fin B, (if c = a then (0 : Mat m n) else wbQ F (f (s, c))) := by
      refine Fintype.sum_equiv (Equiv.swap a b) _ _ (fun c => ?_)
      by_cases hc : c = b
      · simp [hc]
      · have hc' : Equiv.swap a b c ≠ a := fun h =>
          hc ((Equiv.swap a b).injective (h.trans (Equiv.swap_apply_right a b).symm))
        simp [hc, hc']
    simp only [hj, true_and, eq_self_iff_true, hswap]
    rw [hsum]
  · have hfix : ∀ c : Fin B, Equiv.swap (s, a) (s, b) (t + 1 - (j : ℤ), c) = (t + 1 - (j : ℤ), c) :=
      fun c => Equiv.swap_apply_of_ne_of_ne (fun h => hj (congrArg Prod.fst h))
        (fun h => hj (congrArg Prod.fst h))
    simp [hfix, hj]

/-- Private: the joint law is a probability measure (from the marginal law of one sample). -/
private lemma wb_isProb (S : FrozenSamples P m n B) (s : ℤ) (a : Fin B) :
    IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have h := congrArg (fun μ : Measure (Vec m × Vec n) => μ Set.univ) (S.law s a)
  simp only [Measure.map_apply (S.meas s a) MeasurableSet.univ, Set.preimage_univ] at h
  rw [h]
  exact measure_univ

/-- Independence of the deleted buffer from the deleted sample: `M_0^{(s,a)}` is a function of
the samples other than `(s, a)`, which are independent of `(z_{s,a}, w_{s,a})` under the
independent family of `FrozenSamples`. -/
theorem weightedBufDel_indep (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t s : ℤ) (a : Fin B) :
    IndepFun (fun ω => WeightedBufDel w F S t s a ω) (S.zw s a) P := by
  haveI : IsProbabilityMeasure P := wb_isProb S s a
  have hind := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun p : ℤ × Fin B => fun ω => S.zw p.1 p.2 ω) P).mp S.indep
  have hdisj : Disjoint {p : ℤ × Fin B | p ≠ (s, a)} ({(s, a)} : Set (ℤ × Fin B)) := by
    rw [Set.disjoint_singleton_right]; exact fun h => h rfl
  have key := indep_iSup_of_disjoint (fun p : ℤ × Fin B => (S.meas p.1 p.2).comap_le) hind hdisj
  have hΨ : Measurable[⨆ i ∈ {p : ℤ × Fin B | p ≠ (s, a)},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (fun ω (p : ℤ × Fin B) => if p = (s, a) then (0 : Vec m × Vec n) else S.zw p.1 p.2 ω) := by
    refine wb_measurable_pi_sub _ _ (fun p => ?_)
    by_cases hp : p = (s, a)
    · simp only [if_pos hp]; exact measurable_const
    · simp only [if_neg hp]
      exact Measurable.of_comap_le (le_iSup₂
        (f := fun i (_ : i ∈ {p : ℤ × Fin B | p ≠ (s, a)}) =>
          MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) p hp)
  have hWBD : Measurable[⨆ i ∈ {p : ℤ × Fin B | p ≠ (s, a)},
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance]
      (fun ω => WeightedBufDel w F S t s a ω) := by
    have h2 := (wbDelF_measurable w F t s a).comp hΨ
    convert h2 using 1
    funext ω
    show wbDelF w F t s a (fun p => S.zw p.1 p.2 ω) =
      wbDelF w F t s a (fun p => if p = (s, a) then (0 : Vec m × Vec n) else S.zw p.1 p.2 ω)
    unfold wbDelF
    refine tsum_congr (fun j => ?_)
    congr 2
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
    · simp [h]
    · have hne : (t + 1 - (j : ℤ), b) ≠ (s, a) := fun heq =>
        h ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩
      simp only [if_neg h, hne, if_false]
  have hA : MeasurableSpace.comap (fun ω => WeightedBufDel w F S t s a ω) inferInstance ≤
      ⨆ i ∈ {p : ℤ × Fin B | p ≠ (s, a)},
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
    measurable_iff_comap_le.mp hWBD
  have hB : MeasurableSpace.comap (fun ω => S.zw s a ω) inferInstance ≤
      ⨆ i ∈ ({(s, a)} : Set (ℤ × Fin B)),
        MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance :=
    le_iSup₂ (f := fun i (_ : i ∈ ({(s, a)} : Set (ℤ × Fin B))) =>
      MeasurableSpace.comap (fun ω => S.zw i.1 i.2 ω) inferInstance) (s, a) (Set.mem_singleton _)
  exact (IndepFun_iff_Indep _ _ P).mpr (indep_of_indep_of_le_left (indep_of_indep_of_le_right key hB) hA)


/-- Exchangeability within a time (age): the joint law of the deleted buffer and the deleted
sample does not depend on the slot. Source: "samples of the same age are exchangeable"
(`section.tex` l.1189). -/
theorem weightedBufDel_law_slot_invariant (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t s : ℤ) (a b : Fin B) :
    P.map (fun ω => (WeightedBufDel w F S t s a ω, S.zw s a ω)) =
      P.map (fun ω => (WeightedBufDel w F S t s b ω, S.zw s b ω)) := by
  haveI : IsProbabilityMeasure P := wb_isProb S s a
  have hΦ : Measurable (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω) :=
    measurable_pi_iff.mpr (fun p => S.meas p.1 p.2)
  have hperm : P.map (fun ω (p : ℤ × Fin B) =>
      S.zw (Equiv.swap (s, a) (s, b) p).1 (Equiv.swap (s, a) (s, b) p).2 ω) =
      P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω) := by
    have hI : iIndepFun (fun p : ℤ × Fin B => fun ω =>
        S.zw (Equiv.swap (s, a) (s, b) p).1 (Equiv.swap (s, a) (s, b) p).2 ω) P :=
      S.indep.precomp (Equiv.swap (s, a) (s, b)).injective
    refine ((iIndepFun_iff_map_fun_eq_infinitePi_map (fun p : ℤ × Fin B =>
      S.meas (Equiv.swap (s, a) (s, b) p).1 (Equiv.swap (s, a) (s, b) p).2)).mp hI).trans ?_
    refine Eq.trans ?_ ((iIndepFun_iff_map_fun_eq_infinitePi_map
      (fun p : ℤ × Fin B => S.meas p.1 p.2)).mp S.indep).symm
    simp only [S.law]
  have hRmap : (P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map (wbSwapF s a b) =
      P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω) := by
    rw [Measure.map_map (wbSwapF_measurable (m := m) (n := n) s a b) hΦ]
    exact hperm
  have hGR : wbPairF w F t s a = wbPairF w F t s b ∘ wbSwapF s a b := by
    funext f
    refine Prod.ext ?_ ?_
    · exact (wbDelF_swap w F t s a b f).symm
    · show f (s, a) = f (Equiv.swap (s, a) (s, b) (s, b))
      rw [Equiv.swap_apply_right]
  calc P.map (fun ω => (WeightedBufDel w F S t s a ω, S.zw s a ω))
      = (P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map (wbPairF w F t s a) :=
        (Measure.map_map (wbPairF_measurable w F t s a) hΦ).symm
    _ = (P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map
          (wbPairF w F t s b ∘ wbSwapF s a b) := by rw [hGR]
    _ = ((P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map (wbSwapF s a b)).map
          (wbPairF w F t s b) :=
        (Measure.map_map (wbPairF_measurable w F t s b) (wbSwapF_measurable s a b)).symm
    _ = (P.map (fun ω (p : ℤ × Fin B) => S.zw p.1 p.2 ω)).map (wbPairF w F t s b) := by
        rw [hRmap]
    _ = P.map (fun ω => (WeightedBufDel w F S t s b ω, S.zw s b ω)) :=
        Measure.map_map (wbPairF_measurable w F t s b) hΦ


/-! ## `L²` truncation for the weight class -/

private lemma wb_memLp_of_covT_ne {X : Ω → Mat m n} [IsProbabilityMeasure P]
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i : Fin m) (j : Fin n)
    (h : covT P X i j i j ≠ 0) : MemLp (fun ω => X ω i j) 2 P := by
  by_contra hn
  apply h
  unfold covT
  rw [covariance_self (hX i j).aemeasurable]
  exact variance_of_not_memLp (hX i j).aestronglyMeasurable hn

private lemma wb_sampleTensor_diag_pos (A : Mat m n) (i : Fin m) (j : Fin n) :
    sampleTensor A i j i j ≠ 0 := by
  unfold sampleTensor
  have h1 : 0 ≤ (A * Aᵀ) i i := by
    rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => by simp [mul_self_nonneg]
  have h2 : 0 ≤ (Aᵀ * A) j j := by
    rw [Matrix.mul_apply]; exact Finset.sum_nonneg fun k _ => by simp [mul_self_nonneg]
  simp only [if_true, mul_one, one_mul]
  have h3 : 0 ≤ A i j * A i j := mul_self_nonneg _
  have h4 : 0 ≤ A i j * A i j := mul_self_nonneg _
  nlinarith

private lemma wb_sampleX_entry_memLp [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZ : Measurable Z) (hW : Measurable W)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => sampleX A (Z ω) (W ω) i j) 2 P := by
  refine wb_memLp_of_covT_ne (X := fun ω => sampleX A (Z ω) (W ω)) ?_ i j ?_
  · intro i j
    unfold sampleX
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, dotProduct, Matrix.mulVec]
    fun_prop
  · rw [lem_app_setup_gaussian_moments_ii hZW A hA]
    exact wb_sampleTensor_diag_pos A i j


private lemma wb_frozenBatchG_entry (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
    (ω : Ω) (i : Fin m) (j : Fin n) :
    frozenBatchG F S s ω i j = (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ p : Fin m, ∑ q : Fin n,
      (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q := by
  unfold frozenBatchG sampleX
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.vecMulVec_apply]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

private lemma wb_frozenBatchG_entry_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => frozenBatchG F S s ω i j) 2 P := by
  have : (fun ω => frozenBatchG F S s ω i j) = fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ p : Fin m,
      ∑ q : Fin n, (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q := by
    funext ω; exact wb_frozenBatchG_entry F S s ω i j
  rw [this]
  have h1 : ∀ a : Fin B, ∀ p : Fin m, ∀ q : Fin n, MemLp (fun ω => (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P := fun a p q =>
    MemLp.const_mul (wb_sampleX_entry_memLp (Z := fun ω => (S.zw s a ω).1)
      (W := fun ω => (S.zw s a ω).2)
      (measurable_fst.comp (S.meas s a)) (measurable_snd.comp (S.meas s a)) (S.law s a)
      F.A F.hA p q) _
  have h2 : ∀ a : Fin B, ∀ p : Fin m, MemLp (fun ω => ∑ q : Fin n, (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P := fun a p =>
    memLp_finset_sum _ fun q _ => h1 a p q
  have h3 : ∀ a : Fin B, MemLp (fun ω => ∑ p : Fin m, ∑ q : Fin n,
      (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P := fun a =>
    memLp_finset_sum _ fun p _ => h2 a p
  have h4 : MemLp (fun ω => ∑ a : Fin B, ∑ p : Fin m, ∑ q : Fin n,
      (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P :=
    memLp_finset_sum _ fun a _ => h3 a
  exact h4.const_mul _


private lemma wb_abs_entry_le_fro' {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
    |K i j| ≤ fro K := by
  unfold fro
  apply Real.abs_le_sqrt
  have h1 : ‖K i j‖ ^ 2 ≤ ∑ j', ‖K i j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖K i j'‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
  have h2 : ∑ j', ‖K i j'‖ ^ 2 ≤ ∑ i', ∑ j', ‖K i' j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun i' => ∑ j', ‖K i' j'‖ ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (Finset.mem_univ i)
  have h3 : ‖K i j‖ ^ 2 = K i j ^ 2 := by rw [Real.norm_eq_abs, sq_abs]
  linarith

private lemma wb_fro_sq_eq {m n : ℕ} (K : Mat m n) : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma wb_continuous_fro_sq {m n : ℕ} : Continuous (fun K : Mat m n => fro K ^ 2) := by
  simp_rw [wb_fro_sq_eq]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (Continuous.matrix_elem continuous_id i j).pow 2

private lemma wb_integrable_fro_sq_of_memLp {Y : Ω → Mat m n}
    (h : ∀ i j, MemLp (fun ω => Y ω i j) 2 P) :
    Integrable (fun ω => fro (Y ω) ^ 2) P := by
  simp_rw [wb_fro_sq_eq]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (h i j).integrable_sq

private lemma wb_memLp_entry_of_fro {Y : Ω → Mat m n}
    (hY : ∀ i j, AEStronglyMeasurable (fun ω => Y ω i j) P)
    (h : Integrable (fun ω => fro (Y ω) ^ 2) P) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => Y ω i j) 2 P := by
  rw [memLp_two_iff_integrable_sq (hY i j)]
  refine h.mono' ((hY i j).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have := pow_le_pow_left₀ (abs_nonneg (Y ω i j)) (wb_abs_entry_le_fro' (Y ω) i j) 2
  rwa [sq_abs] at this

private lemma wb_young_sq (a b ε : ℝ) (hε : 0 < ε) :
    a ^ 2 ≤ (1 + ε) * b ^ 2 + (1 + ε⁻¹) * (a - b) ^ 2 := by
  have h := mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg (ε * b - (a - b)))
  have e : ε⁻¹ * (ε * b - (a - b)) ^ 2 = ε * b ^ 2 - 2 * b * (a - b) + ε⁻¹ * (a - b) ^ 2 := by
    field_simp
    ring
  nlinarith [h, e]


private lemma wb_young_fro {m n : ℕ} (K L : Mat m n) (ε : ℝ) (hε : 0 < ε) :
    fro K ^ 2 ≤ (1 + ε) * fro L ^ 2 + (1 + ε⁻¹) * fro (K - L) ^ 2 := by
  simp only [wb_fro_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have := wb_young_sq (K i j) (L i j) ε hε
  simpa [Matrix.sub_apply] using this

private lemma wb_fro_sub_comm_sq {m n : ℕ} (K L : Mat m n) : fro (K - L) ^ 2 = fro (L - K) ^ 2 := by
  simp only [wb_fro_sq_eq, Matrix.sub_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma wb_le_of_forall_mul {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ε : ℝ, 0 < ε → a ≤ (1 + ε) * b) :
    a ≤ b := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 := h (δ / (b + 1)) (by positivity)
  have h2 : δ / (b + 1) * b ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

private lemma wb_sq_integral_le_of_memLp [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h1 := variance_eq_sub hf
  have h2 := variance_nonneg f P
  simp only [Pi.pow_apply] at h1
  nlinarith

private lemma wb_mean_batch_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    mean P (frozenBatchG F S s) = mean P (frozenBatchG F S 0) := by
  rw [(lem_app_setup_gaussian_moments_iv F S s).1, (lem_app_setup_gaussian_moments_iv F S 0).1]


private lemma wb_l2_limit [IsProbabilityMeasure P] (X : ℕ → Ω → Mat m n) (D : Ω → Mat m n)
    (c : ℕ → ℝ)
    (hX : ∀ N i j, MemLp (fun ω => X N ω i j) 2 P)
    (hconv : ∀ᵐ ω ∂P, Tendsto (fun N => X N ω) atTop (𝓝 (D ω)))
    (hc : ∀ N N', N ≤ N' → ∫ ω, fro (X N' ω - X N ω) ^ 2 ∂P ≤ c N) :
    (∀ i j, MemLp (fun ω => D ω i j) 2 P) ∧
      ∀ N, Integrable (fun ω => fro (D ω - X N ω) ^ 2) P ∧
        ∫ ω, fro (D ω - X N ω) ^ 2 ∂P ≤ c N := by
  have hDm : ∀ i j, AEStronglyMeasurable (fun ω => D ω i j) P := fun i j =>
    aestronglyMeasurable_of_tendsto_ae atTop (fun N => (hX N i j).aestronglyMeasurable)
      (by
        filter_upwards [hconv] with ω hω
        exact ((Continuous.matrix_elem continuous_id i j).tendsto _).comp hω)
  have hDX : ∀ N i j, AEStronglyMeasurable (fun ω => (D ω - X N ω) i j) P := fun N i j =>
    (hDm i j).sub (hX N i j).aestronglyMeasurable
  have hdiffL : ∀ N N' i j, MemLp (fun ω => (X N' ω - X N ω) i j) 2 P := fun N N' i j =>
    (hX N' i j).sub (hX N i j)
  have key : ∀ N, Integrable (fun ω => fro (D ω - X N ω) ^ 2) P ∧
      ∫ ω, fro (D ω - X N ω) ^ 2 ∂P ≤ c N := by
    intro N
    have hmeas : ∀ N', AEMeasurable (fun ω => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) P :=
      fun N' => ((wb_integrable_fro_sq_of_memLp (hdiffL N N')).aestronglyMeasurable.aemeasurable).ennreal_ofReal
    have hfat := lintegral_liminf_le' (u := atTop) (f := fun N' ω => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) hmeas
    have hlim : ∀ᵐ ω ∂P, Filter.liminf (fun N' => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) atTop
        = ENNReal.ofReal (fro (D ω - X N ω) ^ 2) := by
      filter_upwards [hconv] with ω hω
      refine Filter.Tendsto.liminf_eq ?_
      exact ENNReal.tendsto_ofReal
        ((wb_continuous_fro_sq.tendsto _).comp (hω.sub_const (X N ω)))
    have h1 : ∫⁻ ω, ENNReal.ofReal (fro (D ω - X N ω) ^ 2) ∂P ≤ ENNReal.ofReal (c N) := by
      calc ∫⁻ ω, ENNReal.ofReal (fro (D ω - X N ω) ^ 2) ∂P
          = ∫⁻ ω, Filter.liminf (fun N' => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) atTop ∂P :=
            lintegral_congr_ae (hlim.mono fun ω h => h.symm)
        _ ≤ Filter.liminf (fun N' => ∫⁻ ω, ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2) ∂P) atTop :=
            hfat
        _ ≤ ENNReal.ofReal (c N) := by
            refine Filter.liminf_le_of_frequently_le' (Filter.Eventually.frequently ?_)
            filter_upwards [Filter.eventually_ge_atTop N] with N' hN'
            rw [← ofReal_integral_eq_lintegral_ofReal
              (wb_integrable_fro_sq_of_memLp (hdiffL N N'))
              (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hc N N' hN')
    have hint : Integrable (fun ω => fro (D ω - X N ω) ^ 2) P := by
      refine ⟨?_, ?_⟩
      · have : AEStronglyMeasurable (fun ω => fro (D ω - X N ω) ^ 2) P := by
          simp_rw [wb_fro_sq_eq]
          exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
            Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hDX N i j).pow 2
        exact this
      · rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
        exact lt_of_le_of_lt h1 ENNReal.ofReal_lt_top
    refine ⟨hint, ?_⟩
    have h0 : 0 ≤ c N := le_trans (integral_nonneg fun ω => sq_nonneg _) (hc N N le_rfl)
    rw [← ENNReal.ofReal_le_ofReal_iff h0,
      ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
    exact h1
  refine ⟨fun i j => ?_, key⟩
  have h := wb_memLp_entry_of_fro (fun i j => hDX 0 i j) (key 0).1 i j
  have := h.add (hX 0 i j)
  exact this.ae_eq (Filter.Eventually.of_forall fun ω => by simp)



private lemma wb_young_int {U V' : Ω → Mat m n}
    (hU : Integrable (fun ω => fro (U ω) ^ 2) P) (hV : Integrable (fun ω => fro (V' ω) ^ 2) P)
    (hd : Integrable (fun ω => fro (U ω - V' ω) ^ 2) P) (ε : ℝ) (hε : 0 < ε) :
    ∫ ω, fro (U ω) ^ 2 ∂P ≤ (1 + ε) * ∫ ω, fro (V' ω) ^ 2 ∂P
      + (1 + ε⁻¹) * ∫ ω, fro (U ω - V' ω) ^ 2 ∂P := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hV.const_mul _) (hd.const_mul _)]
  exact integral_mono hU ((hV.const_mul _).add (hd.const_mul _)) fun ω => wb_young_fro _ _ ε hε


/-! ### Helpers for `weightedBuf_tail_l2` (ported from `Muon/Setup/Truncation.lean`, which keeps
them private; here adapted to a general weight sequence) -/

private lemma wb_mean_batch_eq' (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Muon.mean P (frozenBatchG F S s) = Muon.mean P (frozenBatchG F S 0) :=
  wb_mean_batch_eq F S s

private lemma wb_batch_measurable (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  refine measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun k => ?_
  have : (fun ω => frozenBatchG F S s ω i k) =
      fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, slotEntry F i k (S.zw s a ω) :=
    funext fun ω => batch_entry_slot F S s ω i k
  rw [this]
  exact (Finset.measurable_sum _ fun a _ =>
    (slotEntry_continuous F i k).measurable.comp (S.meas s a)).const_mul _

private lemma wb_fro_sq_time [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) :
    ∫ ω, (fro (frozenBatchG F S s ω - Muon.mean P (frozenBatchG F S 0))) ^ 2 ∂P =
      frozenVB S F := by
  have hc : Continuous (fun K : Mat m n => (fro (K - Muon.mean P (frozenBatchG F S 0))) ^ 2) :=
    wb_continuous_fro_sq.comp (continuous_id.sub continuous_const)
  have h1 := integral_map (μ := P) (wb_batch_measurable F S s).aemeasurable
    hc.aestronglyMeasurable
  have h2 := integral_map (μ := P) (wb_batch_measurable F S 0).aemeasurable
    hc.aestronglyMeasurable
  have hlaw := (lem_app_setup_gaussian_moments_iii F S).2 s 0
  unfold frozenVB
  rw [← h2, ← hlaw, h1]

/-- Orthogonality of the centered, independent batches, for an arbitrary weight sequence. -/
private lemma wb_orth [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (T : Finset ℕ) :
    ∫ ω, (fro (∑ j ∈ T,
        w j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - Muon.mean P (frozenBatchG F S 0)))) ^ 2 ∂P
      = frozenVB S F * ∑ j ∈ T, w j ^ 2 := by
  have hGmean : ∀ s i k, ∫ ω, frozenBatchG F S s ω i k ∂P = Muon.mean P (frozenBatchG F S 0) i k := by
    intro s i k
    have := congrFun (congrFun (wb_mean_batch_eq F S s) i) k
    simpa [Muon.mean] using this
  set μ := Muon.mean P (frozenBatchG F S 0) with hμ
  set X : Fin m → Fin n → ℕ → Ω → ℝ := fun i k j ω =>
    w j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω i k - μ i k) with hXdef
  have hXL : ∀ i k j, MemLp (X i k j) 2 P := fun i k j =>
    ((wb_frozenBatchG_entry_memLp F S _ i k).sub (memLp_const _)).const_mul _
  have hGint : ∀ s i k, Integrable (fun ω => frozenBatchG F S s ω i k) P := fun s i k =>
    (wb_frozenBatchG_entry_memLp F S s i k).integrable one_le_two
  have hX0 : ∀ i k j, ∫ ω, X i k j ω ∂P = 0 := by
    intro i k j
    simp only [hXdef]
    rw [integral_const_mul, integral_sub (hGint _ i k) (integrable_const _), hGmean]
    simp
  have hind : ∀ i k, (T : Set ℕ).Pairwise fun j j' => IndepFun (X i k j) (X i k j') P := by
    intro i k j hj j' hj' hne
    have hne' : t + 1 - (j : ℤ) ≠ t + 1 - (j' : ℤ) := by
      intro h; apply hne; omega
    have h := ((lem_app_setup_gaussian_moments_iii F S).1.indepFun hne')
    have hφ : ∀ j : ℕ, Measurable (fun K : Mat m n => w j * (K i k - μ i k)) := fun j => by
      fun_prop
    exact h.comp (hφ j) (hφ j')
  -- entrywise variance additivity
  have hentry : ∀ i k, ∫ ω, (∑ j ∈ T, X i k j ω) ^ 2 ∂P = ∑ j ∈ T, ∫ ω, X i k j ω ^ 2 ∂P := by
    intro i k
    have hv := IndepFun.variance_sum (X := X i k) (s := T) (μ := P) (fun j _ => hXL i k j)
      (hind i k)
    have hS : MemLp (∑ j ∈ T, X i k j) 2 P := memLp_finset_sum' T fun j _ => hXL i k j
    have e1 : variance (∑ j ∈ T, X i k j) P = ∫ ω, (∑ j ∈ T, X i k j ω) ^ 2 ∂P := by
      rw [variance_eq_sub hS]
      have : ∫ ω, (∑ j ∈ T, X i k j) ω ∂P = 0 := by
        simp only [Finset.sum_apply]
        rw [integral_finset_sum _ fun j _ => (hXL i k j).integrable one_le_two]
        exact Finset.sum_eq_zero fun j _ => hX0 i k j
      simp only [Pi.pow_apply, Finset.sum_apply] at this ⊢
      rw [this]; simp
    have e2 : ∀ j ∈ T, variance (X i k j) P = ∫ ω, X i k j ω ^ 2 ∂P := by
      intro j _
      rw [variance_eq_sub (hXL i k j)]
      simp only [Pi.pow_apply]
      rw [hX0]; simp
    rw [← e1, hv]
    exact Finset.sum_congr rfl e2
  have hslice : ∀ j, ∑ i, ∑ k, ∫ ω, X i k j ω ^ 2 ∂P = w j ^ 2 * frozenVB S F := by
    intro j
    have hint : ∀ i k, Integrable (fun ω => X i k j ω ^ 2) P := fun i k => (hXL i k j).integrable_sq
    have e : ∑ i, ∑ k, ∫ ω, X i k j ω ^ 2 ∂P =
        ∫ ω, w j ^ 2 * (fro (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ)) ^ 2 ∂P := by
      simp_rw [wb_fro_sq_eq, Finset.mul_sum]
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => by
        simpa [hXdef, mul_pow] using hint i k)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun k _ => by simpa [hXdef, mul_pow] using hint i k)]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [hXdef, Matrix.sub_apply, mul_pow]
    rw [e, integral_const_mul, wb_fro_sq_time]
  have hfro : ∀ ω, (fro (∑ j ∈ T,
        w j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ))) ^ 2 =
      ∑ i, ∑ k, (∑ j ∈ T, X i k j ω) ^ 2 := by
    intro ω
    rw [wb_fro_sq_eq]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    simp [hXdef, Matrix.sum_apply, Matrix.smul_apply, Matrix.sub_apply]
  have hSint : ∀ i k, Integrable (fun ω => (∑ j ∈ T, X i k j ω) ^ 2) P := fun i k => by
    have := (memLp_finset_sum' T fun j _ => hXL i k j).integrable_sq
    simpa [Finset.sum_apply] using this
  simp_rw [hfro]
  rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => hSint i k)]
  simp_rw [integral_finset_sum _ (fun k _ => hSint _ k)]
  simp_rw [hentry]
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_comm), Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hslice j]; ring

private lemma wb_sq_summable (w : ℕ → ℝ) (hw : WeightClass w) : Summable (fun j : ℕ => w j ^ 2) :=
  Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => by
    have := hw.1.1 j; have := hw.2.1 j; nlinarith) hw.1.2.1

private lemma wb_tail_hasSum (f : ℕ → ℝ) (hf : Summable f) (J : ℕ) :
    HasSum (fun r : ℕ => f (r + (J + 1))) (∑' j : ℕ, if J < j then f j else 0) := by
  have hg : Summable (fun j : ℕ => if J < j then f j else 0) := by
    refine Summable.of_norm_bounded hf.norm (fun j => ?_)
    split_ifs <;> simp
  have h1 := (hasSum_nat_add_iff' (J + 1)).2 hg.hasSum
  have h2 : ∑ i ∈ Finset.range (J + 1), (if J < i then f i else 0) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.1 hi
      simp [Nat.not_lt.2 (by omega : i ≤ J)]
  rw [h2, sub_zero] at h1
  have h3 : (fun n : ℕ => if J < n + (J + 1) then f (n + (J + 1)) else 0)
      = fun r : ℕ => f (r + (J + 1)) := funext fun n => by simp [if_pos (by omega : J < n + (J + 1))]
  rwa [h3] at h1

private lemma wb_tail_core [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    ∫ ω, (fro (WeightedBuf w F S t ω - WeightedBufTrunc w F S t J ω)) ^ 2 ∂P =
      (∑' j : ℕ, if J < j then w j else 0) ^ 2 *
          (fro (Muon.mean P (frozenBatchG F S 0))) ^ 2 +
        (∑' j : ℕ, if J < j then w j ^ 2 else 0) * frozenVB S F := by
  have hGint : ∀ s i j, Integrable (fun ω => frozenBatchG F S s ω i j) P := fun s i j =>
    (wb_frozenBatchG_entry_memLp F S s i j).integrable one_le_two
  have hGmean : ∀ s i j, ∫ ω, frozenBatchG F S s ω i j ∂P = Muon.mean P (frozenBatchG F S 0) i j := by
    intro s i j
    have := congrFun (congrFun (wb_mean_batch_eq F S s) i) j
    simpa [Muon.mean] using this
  set μ := Muon.mean P (frozenBatchG F S 0) with hμdef
  set V := frozenVB S F with hVdef
  have hV0 : 0 ≤ V := integral_nonneg fun ω => sq_nonneg _
  set T1 := ∑' j : ℕ, if J < j then w j else 0 with hT1
  set T2 := ∑' j : ℕ, if J < j then w j ^ 2 else 0 with hT2
  set Y : ℕ → Ω → Mat m n := fun j ω =>
    w j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ) with hYdef
  set X : ℕ → Ω → Mat m n := fun N ω => ∑ k ∈ Finset.range N, Y (k + (J + 1)) ω with hXdef
  set D : Ω → Mat m n := fun ω =>
    WeightedBuf w F S t ω - WeightedBufTrunc w F S t J ω - T1 • μ with hDdef
  have hYe : ∀ j ω i k, Y j ω i k = w j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω i k - μ i k) := by
    intro j ω i k
    simp [hYdef, Matrix.smul_apply, Matrix.sub_apply]
  have hYL : ∀ j i k, MemLp (fun ω => Y j ω i k) 2 P := by
    intro j i k
    have : (fun ω => Y j ω i k) = fun ω => w j *
        (frozenBatchG F S (t + 1 - (j : ℤ)) ω i k - μ i k) := funext fun ω => hYe j ω i k
    rw [this]
    exact ((wb_frozenBatchG_entry_memLp F S _ i k).sub (memLp_const _)).const_mul _
  have hXe : ∀ N ω i k, X N ω i k = ∑ r ∈ Finset.range N, Y (r + (J + 1)) ω i k := by
    intro N ω i k
    simp [hXdef, Matrix.sum_apply]
  have hXL : ∀ N i k, MemLp (fun ω => X N ω i k) 2 P := by
    intro N i k
    have : (fun ω => X N ω i k) = fun ω => ∑ r ∈ Finset.range N, Y (r + (J + 1)) ω i k :=
      funext fun ω => hXe N ω i k
    rw [this]
    exact memLp_finset_sum _ fun r _ => hYL _ i k
  have hXmean : ∀ N i k, ∫ ω, X N ω i k ∂P = 0 := by
    intro N i k
    have : (fun ω => X N ω i k) = fun ω => ∑ r ∈ Finset.range N, Y (r + (J + 1)) ω i k :=
      funext fun ω => hXe N ω i k
    rw [this, integral_finset_sum _ (fun r _ => (hYL _ i k).integrable one_le_two)]
    refine Finset.sum_eq_zero fun r _ => ?_
    simp_rw [hYe]
    rw [integral_const_mul, integral_sub (hGint _ i k) (integrable_const _), hGmean]
    simp
  have hw2s : Summable (fun j : ℕ => w j ^ 2) := wb_sq_summable w hw
  have hdiff : ∀ N N' ω, N < N' → X N' ω - X N ω = ∑ j ∈ Finset.Icc (N + (J + 1)) (N' + J),
      w j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ) := by
    intro N N' ω hN
    have h1 : X N' ω - X N ω = ∑ r ∈ Finset.Ico N N', Y (r + (J + 1)) ω := by
      rw [Finset.sum_Ico_eq_sub _ hN.le]
    have h2 : Finset.Ico (N + (J + 1)) (N' + (J + 1)) = Finset.Icc (N + (J + 1)) (N' + J) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [h1, Finset.sum_Ico_add' (fun j => Y j ω) N N' (J + 1), h2]
  have hsqIco : ∀ N N', N < N' → ∑ j ∈ Finset.Icc (N + (J + 1)) (N' + J), w j ^ 2
      = ∑ r ∈ Finset.Ico N N', w (r + (J + 1)) ^ 2 := by
    intro N N' hN
    have h2 : Finset.Ico (N + (J + 1)) (N' + (J + 1)) = Finset.Icc (N + (J + 1)) (N' + J) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [← h2, Finset.sum_Ico_add' (fun j => w j ^ 2) N N' (J + 1)]
  have horth : ∀ N N', N ≤ N' → ∫ ω, fro (X N' ω - X N ω) ^ 2 ∂P
      = V * ∑ r ∈ Finset.Ico N N', w (r + (J + 1)) ^ 2 := by
    intro N N' hN
    rcases hN.lt_or_eq with hlt | rfl
    · have := wb_orth w F S t (Finset.Icc (N + (J + 1)) (N' + J))
      simp_rw [hdiff N N' _ hlt]
      rw [this, hsqIco N N' hlt]
    · simp [fro]
  set c : ℕ → ℝ := fun N => V * ∑' k, w (k + (N + (J + 1))) ^ 2 with hcdef
  have hc : ∀ N N', N ≤ N' → ∫ ω, fro (X N' ω - X N ω) ^ 2 ∂P ≤ c N := by
    intro N N' hN
    rw [horth N N' hN]
    refine mul_le_mul_of_nonneg_left ?_ hV0
    rw [Finset.sum_Ico_eq_sum_range]
    have : ∀ k, w (N + k + (J + 1)) ^ 2 = w (k + (N + (J + 1))) ^ 2 := fun k => by
      congr 2; omega
    simp_rw [this]
    exact (hw2s.comp_injective (add_left_injective (N + (J + 1)))).sum_le_tsum _
      (fun _ _ => sq_nonneg _) |>.trans_eq' rfl
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have h1 := tendsto_sum_nat_add (fun j : ℕ => w j ^ 2)
    have h2 : Tendsto (fun N : ℕ => N + (J + 1)) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_right N (J + 1)) tendsto_id
    simpa using (h1.comp h2).const_mul V
  have hw1 : HasSum (fun r : ℕ => w (r + (J + 1))) T1 := wb_tail_hasSum w hw.1.2.1 J
  have hw2 : HasSum (fun r : ℕ => w (r + (J + 1)) ^ 2) T2 := wb_tail_hasSum _ hw2s J
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun N => X N ω) atTop (𝓝 (D ω)) := by
    filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
    have hs := hω t
    have h1 := (hasSum_nat_add_iff' (J + 1)).2 hs.hasSum
    have h3 := h1.sub (hw1.smul_const μ)
    have h4 := h3.tendsto_sum_nat
    refine h4.congr (fun N => ?_)
    simp [hXdef, hYdef, hDdef, smul_sub, WeightedBuf, WeightedBufTrunc]
  obtain ⟨hDL, hDX⟩ := wb_l2_limit X D c hXL hconv hc
  have hDint : Integrable (fun ω => fro (D ω) ^ 2) P := wb_integrable_fro_sq_of_memLp hDL
  have hXint : ∀ N, Integrable (fun ω => fro (X N ω) ^ 2) P := fun N =>
    wb_integrable_fro_sq_of_memLp (hXL N)
  have hXsq : ∀ N, ∫ ω, fro (X N ω) ^ 2 ∂P
      = V * ∑ r ∈ Finset.range N, w (r + (J + 1)) ^ 2 := by
    intro N
    have h := horth 0 N (Nat.zero_le N)
    have h0 : X 0 = fun _ => 0 := by
      funext ω; simp [hXdef]
    rw [h0, ← Finset.range_eq_Ico] at h
    simpa using h
  have hWt : Tendsto (fun N => ∑ r ∈ Finset.range N, w (r + (J + 1)) ^ 2) atTop (𝓝 T2) :=
    hw2.tendsto_sum_nat
  have hS0 : 0 ≤ T2 :=
    ge_of_tendsto' hWt fun N => Finset.sum_nonneg fun r _ => sq_nonneg _
  have hΔ0 : 0 ≤ ∫ ω, fro (D ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hΔ : ∫ ω, fro (D ω) ^ 2 ∂P = V * T2 := by
    apply le_antisymm
    · refine wb_le_of_forall_mul (mul_nonneg hV0 hS0) fun ε hε => ?_
      have hlim : Tendsto (fun N => (1 + ε) * (V * ∑ r ∈ Finset.range N,
          w (r + (J + 1)) ^ 2) + (1 + ε⁻¹) * c N) atTop
          (𝓝 ((1 + ε) * (V * T2) + (1 + ε⁻¹) * 0)) :=
        ((hWt.const_mul V).const_mul (1 + ε)).add (hc0.const_mul (1 + ε⁻¹))
      rw [mul_zero, add_zero] at hlim
      refine ge_of_tendsto' hlim fun N => ?_
      have h1 := wb_young_int hDint (hXint N) (hDX N).1 ε hε
      rw [hXsq N] at h1
      exact h1.trans (by nlinarith [(hDX N).2, show (0 : ℝ) ≤ 1 + ε⁻¹ by positivity])
    · refine wb_le_of_forall_mul hΔ0 fun ε hε => ?_
      have hlim : Tendsto (fun N => (1 + ε) * ∫ ω, fro (D ω) ^ 2 ∂P + (1 + ε⁻¹) * c N) atTop
          (𝓝 ((1 + ε) * ∫ ω, fro (D ω) ^ 2 ∂P + (1 + ε⁻¹) * 0)) :=
        tendsto_const_nhds.add (hc0.const_mul (1 + ε⁻¹))
      rw [mul_zero, add_zero] at hlim
      have hlim2 : Tendsto (fun N => V * ∑ r ∈ Finset.range N, w (r + (J + 1)) ^ 2)
          atTop (𝓝 (V * T2)) := hWt.const_mul V
      refine le_of_tendsto_of_tendsto hlim2 hlim (Filter.Eventually.of_forall fun N => ?_)
      have hd : Integrable (fun ω => fro (X N ω - D ω) ^ 2) P :=
        (hDX N).1.congr (Filter.Eventually.of_forall fun ω => wb_fro_sub_comm_sq _ _)
      have h1 := wb_young_int (hXint N) hDint hd ε hε
      rw [hXsq N] at h1
      have h2 : ∫ ω, fro (X N ω - D ω) ^ 2 ∂P = ∫ ω, fro (D ω - X N ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => wb_fro_sub_comm_sq _ _)
      rw [h2] at h1
      exact h1.trans (by nlinarith [(hDX N).2, show (0 : ℝ) ≤ 1 + ε⁻¹ by positivity])
  have hDmean : ∀ i k, ∫ ω, D ω i k ∂P = 0 := by
    intro i k
    have hle : ∀ N, (∫ ω, D ω i k ∂P) ^ 2 ≤ c N := by
      intro N
      have hL : MemLp (fun ω => D ω i k - X N ω i k) 2 P := (hDL i k).sub (hXL N i k)
      have h1 := wb_sq_integral_le_of_memLp hL
      rw [integral_sub ((hDL i k).integrable one_le_two) ((hXL N i k).integrable one_le_two),
        hXmean, sub_zero] at h1
      refine h1.trans ((integral_mono hL.integrable_sq (hDX N).1 fun ω => ?_).trans (hDX N).2)
      have := pow_le_pow_left₀ (abs_nonneg (D ω i k - X N ω i k))
        (wb_abs_entry_le_fro' (D ω - X N ω) i k) 2
      rwa [sq_abs] at this
    have h0 : (∫ ω, D ω i k ∂P) ^ 2 ≤ 0 := ge_of_tendsto' hc0 hle
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (sq_nonneg _))
  have hTe : ∀ ω i k, (WeightedBuf w F S t ω - WeightedBufTrunc w F S t J ω) i k
      = D ω i k + T1 * μ i k := by
    intro ω i k
    simp [hDdef, Matrix.sub_apply, Matrix.smul_apply]
  have hik : ∀ i k, ∫ ω, (D ω i k + T1 * μ i k) ^ 2 ∂P
      = ∫ ω, D ω i k ^ 2 ∂P + (T1 * μ i k) ^ 2 := by
    intro i k
    set a := T1 * μ i k with ha
    have hD2 : Integrable (fun ω => D ω i k ^ 2) P := (hDL i k).integrable_sq
    have hD1 : Integrable (fun ω => D ω i k) P := (hDL i k).integrable one_le_two
    have : (fun ω => (D ω i k + a) ^ 2) = fun ω => D ω i k ^ 2 + (2 * a) * D ω i k + a ^ 2 := by
      funext ω; ring
    have i1 : ∫ ω, (D ω i k ^ 2 + (2 * a) * D ω i k + a ^ 2) ∂P
        = ∫ ω, (D ω i k ^ 2 + (2 * a) * D ω i k) ∂P + ∫ ω, a ^ 2 ∂P :=
      integral_add (hD2.add (hD1.const_mul _)) (integrable_const _)
    have i2 : ∫ ω, (D ω i k ^ 2 + (2 * a) * D ω i k) ∂P
        = ∫ ω, D ω i k ^ 2 ∂P + ∫ ω, (2 * a) * D ω i k ∂P :=
      integral_add hD2 (hD1.const_mul _)
    rw [this, i1, i2, integral_const_mul, hDmean]
    simp
  have e1 : (fun ω => fro (WeightedBuf w F S t ω - WeightedBufTrunc w F S t J ω) ^ 2)
      = fun ω => ∑ i, ∑ k, (D ω i k + T1 * μ i k) ^ 2 := by
    funext ω
    rw [wb_fro_sq_eq]
    simp_rw [hTe]
  have e2 : ∫ ω, fro (D ω) ^ 2 ∂P = ∑ i, ∑ k, ∫ ω, D ω i k ^ 2 ∂P := by
    simp_rw [wb_fro_sq_eq]
    rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => (hDL i k).integrable_sq)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finset_sum _ (fun k _ => (hDL i k).integrable_sq)]
  have e5 : ∫ ω, ∑ i, ∑ k, (D ω i k + T1 * μ i k) ^ 2 ∂P
      = ∑ i, ∫ ω, ∑ k, (D ω i k + T1 * μ i k) ^ 2 ∂P :=
    integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ =>
      ((hDL i k).add (memLp_const _)).integrable_sq)
  rw [e1, e5]
  have e3 : ∀ i, ∫ ω, ∑ k, (D ω i k + T1 * μ i k) ^ 2 ∂P
      = ∑ k, (∫ ω, D ω i k ^ 2 ∂P + (T1 * μ i k) ^ 2) := by
    intro i
    have e6 : ∫ ω, ∑ k, (D ω i k + T1 * μ i k) ^ 2 ∂P
        = ∑ k, ∫ ω, (D ω i k + T1 * μ i k) ^ 2 ∂P :=
      integral_finset_sum _ (fun k _ => ((hDL i k).add (memLp_const _)).integrable_sq)
    rw [e6]
    exact Finset.sum_congr rfl fun k _ => hik i k
  simp_rw [e3, Finset.sum_add_distrib]
  rw [← e2, hΔ, wb_fro_sq_eq μ]
  have e4 : ∑ i, ∑ k, (T1 * μ i k) ^ 2 = T1 ^ 2 * ∑ i, ∑ k, μ i k ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_pow]
  rw [e4]
  ring


/-- `L²` truncation identity for the weight class. For the tail `M_t - M^{(J)}_t`, batches of
distinct ages are independent with the common mean `𝔼 G_0` and common Frobenius variance
`V_B = frozenVB`, so
`𝔼‖M_t − M^{(J)}_t‖_F² = (∑_{j>J} w_j)² ‖𝔼G‖_F² + ∑_{j>J} w_j² V_B`.
Source: the display in the proof of `lem:app-de-variance` (`section.tex` l.1251–1255). -/
theorem weightedBuf_tail_l2 [IsProbabilityMeasure P] (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    ∫ ω, (Muon.fro (WeightedBuf w F S t ω - WeightedBufTrunc w F S t J ω)) ^ 2 ∂P =
      (∑' j : ℕ, if J < j then w j else 0) ^ 2 *
          (Muon.fro (Muon.mean P (frozenBatchG F S 0))) ^ 2 +
        (∑' j : ℕ, if J < j then w j ^ 2 else 0) * frozenVB S F := by
  exact wb_tail_core w hw F S t J

/-! ## The bounds `eqn:app-de-qI` -/

/-! ### Private helpers for `eqn_app_de_qI` -/

private lemma pb_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

open scoped Matrix.Norms.L2Operator in
private lemma pb_abs_entry_le_opNorm {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

private lemma pb_inv_measurable {a : ℕ} : Measurable (fun X : Mat a a => X⁻¹) := by
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

private lemma pb_Rs_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rs M s) := by
  have hc : Continuous (fun M : Mat a b => M * Mᵀ + s • (1 : Mat a a)) := by fun_prop
  exact (pb_inv_measurable (a := a)).comp hc.measurable

private lemma pb_Rts_measurable {a b : ℕ} (s : ℝ) :
    Measurable (fun M : Mat a b => Rts M s) := by
  have hc : Continuous (fun M : Mat a b => Mᵀ * M + s • (1 : Mat b b)) := by fun_prop
  exact (pb_inv_measurable (a := b)).comp hc.measurable

private lemma pb_Rs_psd {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    (Rs K s).PosSemidef := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat a a)).PosDef := Matrix.PosDef.one.smul hs
  unfold Rs
  rw [add_comm]
  exact (Matrix.PosDef.add_posSemidef h2 h1).inv.posSemidef

private lemma pb_Rts_psd {a b : ℕ} (K : Mat a b) (s : ℝ) (hs : 0 < s) :
    (Rts K s).PosSemidef := by
  have h1 : (Kᵀ * K).PosSemidef := by
    have h := Matrix.posSemidef_conjTranspose_mul_self K
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h2 : (s • (1 : Mat b b)).PosDef := Matrix.PosDef.one.smul hs
  unfold Rts
  rw [add_comm]
  exact (Matrix.PosDef.add_posSemidef h2 h1).inv.posSemidef

private lemma pb_wb_measurable (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  unfold WeightedBuf
  exact Measurable.tsum fun j => (wb_batch_measurable F S (t + 1 - (j : ℤ))).const_smul (w j)

/-- Pointwise trace bounds for a PSD `S` (with `‖S‖ ≤ C`) and a PSD `R` (with `‖R‖ ≤ c`). -/
private lemma pb_trace_psd_bounds {p : ℕ} (S R : Mat p p) (hS : S.PosSemidef)
    (hR : R.PosSemidef) (C c : ℝ) (hS' : opNorm S ≤ C) (hR' : opNorm R ≤ c) :
    0 ≤ (S * R).trace ∧ (S * R).trace ≤ C * (p * c) := by
  constructor
  · have hr : CFC.sqrt S * CFC.sqrt S = S :=
      CFC.sqrt_mul_sqrt_self S (Matrix.nonneg_iff_posSemidef.mpr hS)
    have hrH : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)).isHermitian.eq
    have hpsd := hR.mul_mul_conjTranspose_same (CFC.sqrt S)
    rw [hrH] at hpsd
    have key : (S * R).trace = (CFC.sqrt S * R * CFC.sqrt S).trace := by
      calc (S * R).trace = (CFC.sqrt S * (CFC.sqrt S * R)).trace := by
            rw [← Matrix.mul_assoc, hr]
        _ = ((CFC.sqrt S * R) * CFC.sqrt S).trace :=
            Matrix.trace_mul_comm (CFC.sqrt S) (CFC.sqrt S * R)
        _ = (CFC.sqrt S * R * CFC.sqrt S).trace := rfl
    rw [key]
    exact hpsd.trace_nonneg
  · have h1 := trace_mul_le_opNorm_mul_nuc S R
    have h2 := nuc_le_rank_mul_opNorm R
    have hrank : (Matrix.rank R : ℝ) ≤ p := by
      have h := Matrix.rank_le_card_height R
      simp only [Fintype.card_fin] at h
      exact_mod_cast h
    have hnuc : nuc R ≤ (p : ℝ) * c :=
      h2.trans (mul_le_mul hrank hR' (pb_opNorm_nonneg R) (Nat.cast_nonneg _))
    have hC0 : 0 ≤ C := (pb_opNorm_nonneg S).trans hS'
    calc (S * R).trace ≤ |(S * R).trace| := le_abs_self _
      _ ≤ opNorm S * nuc R := h1
      _ ≤ C * nuc R := mul_le_mul_of_nonneg_right hS' (nuc_nonneg R)
      _ ≤ C * (p * c) := mul_le_mul_of_nonneg_left hnuc hC0

private lemma pb_trace_mean_eq [IsProbabilityMeasure P] {p : ℕ} (X : Ω → Mat p p)
    (hX : Measurable X) (c : ℝ) (hb : ∀ ω, opNorm (X ω) ≤ c) (S : Mat p p) :
    (S * Muon.mean P X).trace = ∫ ω, (S * X ω).trace ∂P := by
  have hmeas : ∀ i k, Measurable (fun ω => X ω k i) := fun i k =>
    (by fun_prop : Measurable fun M : Mat p p => M k i).comp hX
  have hint : ∀ i k, Integrable (fun ω => X ω k i) P := fun i k =>
    Integrable.mono' (integrable_const c) (hmeas i k).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs]
        exact (pb_abs_entry_le_opNorm (X ω) k i).trans (hb ω))
  have hL : (S * Muon.mean P X).trace = ∑ i, ∑ k, S i k * ∫ ω, X ω k i ∂P := by
    simp [Matrix.trace, Matrix.mul_apply, Muon.mean]
  have hR : ∀ ω, (S * X ω).trace = ∑ i, ∑ k, S i k * X ω k i := fun ω => by
    simp [Matrix.trace, Matrix.mul_apply]
  simp only [hR]
  rw [hL, integral_finset_sum _ (fun i _ => integrable_finset_sum _ (fun k _ =>
    (hint i k).const_mul (S i k)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun k _ => (hint i k).const_mul (S i k))]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul]

private lemma pb_expect_bounds [IsProbabilityMeasure P] {p : ℕ} (X : Ω → Mat p p)
    (hX : Measurable X) (S : Mat p p) (hS : S.PosSemidef) (C c : ℝ) (hC : opNorm S ≤ C)
    (hc : 0 ≤ c) (hPSD : ∀ ω, (X ω).PosSemidef) (hb : ∀ ω, opNorm (X ω) ≤ c) :
    0 ≤ (S * Muon.mean P X).trace ∧ (S * Muon.mean P X).trace ≤ C * (p * c) := by
  rw [pb_trace_mean_eq X hX c hb S]
  have hpt : ∀ ω, 0 ≤ (S * X ω).trace ∧ (S * X ω).trace ≤ C * (p * c) := fun ω =>
    pb_trace_psd_bounds S (X ω) hS (hPSD ω) C c hC (hb ω)
  have hCpc : 0 ≤ C * (p * c) :=
    mul_nonneg ((pb_opNorm_nonneg S).trans hC) (mul_nonneg (Nat.cast_nonneg _) hc)
  constructor
  · exact integral_nonneg fun ω => (hpt ω).1
  · have hnorm := norm_integral_le_of_norm_le_const (μ := P)
      (f := fun ω => (S * X ω).trace) (C := C * (p * c))
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_le]
        exact ⟨by linarith [(hpt ω).1], (hpt ω).2⟩)
    simp only [probReal_univ, mul_one] at hnorm
    rw [Real.norm_eq_abs] at hnorm
    exact (le_abs_self _).trans hnorm

/-- `eqn:app-de-qI`: for `s ∈ I` with `s ≥ s_- > 0`, under `‖Σout‖, ‖Σin‖ ≤ C_Σ` and
`N_out, N_in ≤ γ⋆ B`, the expected traces and `q_B(s)` are bounded:
`0 ≤ σ_B, σ̃_B ≤ C_Σ γ⋆ / s` and `0 ≤ q_B(s) ≤ (C_Σ γ⋆)² / s_-`. Source (`section.tex`
l.1202–1204; the paper's `q_I` is the right side of the last bound with `s_- = sm`):
\begin{equation}\label{eqn:app-de-qI}
0\le\sigma_B,\tilde\sigma_B\le\frac{C_\Sigma\gamma_\star}{s},\qquad
0\le q_B(s)\le q_I\defeq\frac{(C_\Sigma\gamma_\star)^2}{s_-}\qquad(s\in I).
-/
theorem eqn_app_de_qI (w : ℕ → ℝ) (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) [IsProbabilityMeasure P] (t : ℤ) (CSig γ sm : ℝ) (I : Set ℝ)
    (hsm : 0 < sm) (hI : ∀ s ∈ I, sm ≤ s)
    (hCSig : Muon.opNorm F.C.Sout ≤ CSig ∧ Muon.opNorm F.C.Sin ≤ CSig)
    (hγ : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (s : ℝ) (hs : s ∈ I) :
    0 ≤ sigmaB w F S t s ∧ sigmaB w F S t s ≤ CSig * γ / s ∧
      0 ≤ sigmaTildeB w F S t s ∧ sigmaTildeB w F S t s ≤ CSig * γ / s ∧
      0 ≤ qB w F S t s ∧ qB w F S t s ≤ (CSig * γ) ^ 2 / sm := by
  have hs0 : 0 < s := lt_of_lt_of_le hsm (hI s hs)
  have hB : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hWB := pb_wb_measurable w F S t
  have hRsM : Measurable (fun ω => Rs (WeightedBuf w F S t ω) s) :=
    Measurable.comp (g := fun M : Mat m n => Rs M s) (f := WeightedBuf w F S t)
      (pb_Rs_measurable s) hWB
  have hRtsM : Measurable (fun ω => Rts (WeightedBuf w F S t ω) s) :=
    Measurable.comp (g := fun M : Mat m n => Rts M s) (f := WeightedBuf w F S t)
      (pb_Rts_measurable s) hWB
  have hc : (0 : ℝ) ≤ 1 / s := by positivity
  have hSo := pb_expect_bounds (P := P) (fun ω => Rs (WeightedBuf w F S t ω) s) hRsM F.C.Sout
    F.C.psdOut CSig (1 / s) hCSig.1 hc (fun ω => pb_Rs_psd _ s hs0)
    (fun ω => (lem_app_de_resolvent _ s hs0).1)
  have hSi := pb_expect_bounds (P := P) (fun ω => Rts (WeightedBuf w F S t ω) s) hRtsM F.C.Sin
    F.C.psdIn CSig (1 / s) hCSig.2 hc (fun ω => pb_Rts_psd _ s hs0)
    (fun ω => (lem_app_de_resolvent _ s hs0).2.1)
  have hCS0 : 0 ≤ CSig := (pb_opNorm_nonneg F.C.Sout).trans hCSig.1
  have h3 : (m : ℝ) * (1 / s) ≤ γ * B * (1 / s) :=
    mul_le_mul_of_nonneg_right hγ.1 (by positivity)
  have h3' : (n : ℝ) * (1 / s) ≤ γ * B * (1 / s) :=
    mul_le_mul_of_nonneg_right hγ.2 (by positivity)
  have h4 : CSig * ((m : ℝ) * (1 / s)) ≤ CSig * (γ * B * (1 / s)) :=
    mul_le_mul_of_nonneg_left h3 hCS0
  have h4' : CSig * ((n : ℝ) * (1 / s)) ≤ CSig * (γ * B * (1 / s)) :=
    mul_le_mul_of_nonneg_left h3' hCS0
  have h5 : CSig * (γ * B * (1 / s)) = B * (CSig * γ / s) := by ring
  have hσ : 0 ≤ sigmaB w F S t s ∧ sigmaB w F S t s ≤ CSig * γ / s := by
    unfold sigmaB expRes
    refine ⟨mul_nonneg (inv_nonneg.mpr hB.le) hSo.1, ?_⟩
    rw [inv_mul_le_iff₀ hB]
    linarith [hSo.2, h4, h5]
  have hσt : 0 ≤ sigmaTildeB w F S t s ∧ sigmaTildeB w F S t s ≤ CSig * γ / s := by
    unfold sigmaTildeB expResT
    refine ⟨mul_nonneg (inv_nonneg.mpr hB.le) hSi.1, ?_⟩
    rw [inv_mul_le_iff₀ hB]
    linarith [hSi.2, h4', h5]
  have hX0 : 0 ≤ CSig * γ / s := hσ.1.trans hσ.2
  refine ⟨hσ.1, hσ.2, hσt.1, hσt.2, ?_, ?_⟩
  · unfold qB
    exact mul_nonneg (mul_nonneg hs0.le hσ.1) hσt.1
  · unfold qB
    calc s * sigmaB w F S t s * sigmaTildeB w F S t s
        ≤ s * (CSig * γ / s) * (CSig * γ / s) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hσ.2 hs0.le) hσt.2 hσt.1
            (mul_nonneg hs0.le hX0)
      _ = (CSig * γ) ^ 2 / s := by field_simp
      _ ≤ (CSig * γ) ^ 2 / sm :=
          div_le_div_of_nonneg_left (sq_nonneg _) hsm (hI s hs)

end Muon.DetEquiv
