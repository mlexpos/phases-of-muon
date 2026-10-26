import Muon.Volatility.Defs
import Muon.Volatility.HalfCandidates
import Muon.Drift.Defs
import Muon.DetEquiv.SampleModel
import Muon.DetEquiv.Branch
import Muon.DetEquiv.Resolvent
import Muon.Setup.Regime
import Muon.Drift.Mean
import Muon.DetEquiv.Trace

/-!
# Appendix D, part 3: centering and same-time energies of rows and columns

Work package L-D.3 (interface draft). Snapshot `cr-2026-10-23`. Source of record:
`sections/04-volatility/section.tex`: `lem:app-vol-centering` (l.428–440),
`thm:app-vol-half-same` (l.478–509), `eqn:app-vol-half-identity` (l.527–530) and
`eqn:app-vol-half-onestep` (l.519–522).
Card: `sections/04-volatility/CARD.md` §2, §3, §5 (row L-D.3).

Reused, not redefined: `def_app_vol_lag`, `centredUpd`, `sameTimeZ`, `sameTimeZc`, `SizeFin`
(`Muon.Volatility.Defs`); `volraw`, `volTildeZero`, `zbarRaw`
(`Muon.Volatility.HalfCandidates`);
`frozenUpd`, `FrozenParams`, `FrozenSamples`, `SpectralData`, `SetupRegime`, `pairSigma`
(`Muon.Setup`); `expRes`, `expResT` (`Muon.DetEquiv.SampleModel`); `Rbar`, `Rtbar`, `branchSol`,
`Fw` (`Muon.DetEquiv`); `Rs`, `Rts` (`Muon.DetEquiv.Resolvent`); `specOutFM`, `specInFM`
(`Muon.Drift.Defs`); `Muon.Q`, `Muon.mean`, `Muon.fro`, `Muon.opNorm`, `Muon.emaW`.

Encoding decisions (the card's B/C conclusions enter as hypotheses):
* The sups `e_B`, `ẽ_B` are given as real upper bounds `eB`, `eBt` on the norms over `I`
  (`∀ s ∈ I, ‖…‖ ≤ eB`). The conclusion `sup_I ≤ ϱ₊ e_B` is then `∀ ϱ ∈ I, … ≤ ϱ₊ eB`; for
  `eB` the exact supremum this is the paper's statement.
* `ε_B` and the mean bound of `thm:app-drift-mean` enter as the hypothesis `hmean`, quantified over
  all times `s` (stationarity, `lem:app-setup-ema-law`(ii), is not proved here).
* Finite-dimensional statements take `Ω : Type`. The limits (`_iii_raw`, `_iii_centered`, `_iv_raw`,
  `_iv_centered`) take a regime `R : SetupRegime` with `Ω : ℕ → Type`. Their sups over `ϱ` are
  taken in `ℝ≥0∞` (`⨆` of `ENNReal.ofReal`), so no `BddAbove` side condition is needed and the
  expectation is a lintegral.
* Pointwise claims (`_ii_zero_rows`, `_ii_zero_cols`, `lem_app_vol_centering_ii`) are stated for
  every sample point, as the paper states them.
* Expectations are Bochner integrals `∫ ω, … ∂P`, parenthesized (no binder-precedence ambiguity).
-/

set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open scoped Matrix MatrixOrder ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Volatility

variable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-! ## Candidates of `thm:app-vol-half-same` -/

/-- Row-side candidate of `thm:app-vol-half-same`(i):
`s̃₁(−ϱ) Σ_out (s̃₁(−ϱ) Σ_out + ϱ Id)^{-1}`, the deterministic limit of `𝔼[S_t(ϱ) S_t(ϱ)^⊤]`. -/
def halfGramOut (F : FrozenParams m n B) (ϱ : ℝ) : Mat m m :=
  let a := (branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).2.2.1
  (a • F.C.Sout) * (a • F.C.Sout + ϱ • (1 : Mat m m))⁻¹

/-- Column-side candidate of `thm:app-vol-half-same`(i):
`s₁(−ϱ) Σ_in (s₁(−ϱ) Σ_in + ϱ Id)^{-1}`, the deterministic limit of `𝔼[S_t(ϱ)^⊤ S_t(ϱ)]`. -/
def halfGramIn (F : FrozenParams m n B) (ϱ : ℝ) : Mat n n :=
  let a := (branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).2.2.2
  (a • F.C.Sin) * (a • F.C.Sin + ϱ • (1 : Mat n n))⁻¹

/-- Candidate `B⁻¹ Tr Σ_in − ϱ σ̃(−ϱ)` of `thm:app-vol-half-same`(iv), the input-side total. -/
def halfZTotIn (F : FrozenParams m n B) (ϱ : ℝ) : ℝ :=
  (B : ℝ)⁻¹ * (F.C.Sin).trace -
    ϱ * (branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).2.1

/-! ## Centering -/

/-! ### Private helpers for the centering bounds -/

private lemma hv_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma hv_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma hv_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma hv_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma hv_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma hv_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
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
    rw [hv_fro_sq, mul_pow, hv_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (hv_fro_nn _) (mul_nonneg (hv_opNorm_nonneg M) (hv_fro_nn N))
    two_ne_zero).mp hfro

private lemma hv_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := hv_fro_mul_le_left Nᵀ Mᵀ
  rw [hv_opNorm_transpose, hv_fro_transpose, ← Matrix.transpose_mul, hv_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma hv_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [hv_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [hv_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (hv_fro_nn X) (hv_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs

/-- Bilinearity of the Σ-pairing (private copies). -/
private lemma hv_pS_sub_left {m n : ℕ} (C : Covariances m n) (A B W : Mat m n) :
    Muon.Setup.pairSigma C (A - B) W = Muon.Setup.pairSigma C A W - Muon.Setup.pairSigma C B W := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]

private lemma hv_pS_sub_right {m n : ℕ} (C : Covariances m n) (V A B : Mat m n) :
    Muon.Setup.pairSigma C V (A - B) = Muon.Setup.pairSigma C V A - Muon.Setup.pairSigma C V B := by
  unfold Muon.Setup.pairSigma
  simp only [Matrix.mul_sub, Matrix.trace_sub, Matrix.transpose_sub]

/-- The Σ-pairing is symmetric (private copy). -/
private lemma hv_pS_comm {m n : ℕ} (C : Covariances m n) (V W : Mat m n) :
    Muon.Setup.pairSigma C V W = Muon.Setup.pairSigma C W V := by
  have hO : C.Soutᵀ = C.Sout := by
    have h := C.psdOut.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hI : C.Sinᵀ = C.Sin := by
    have h := C.psdIn.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  unfold Muon.Setup.pairSigma
  rw [← Matrix.trace_transpose (C.Sout * V * C.Sin * Wᵀ)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hO, hI]
  rw [show W * (C.Sin * (Vᵀ * C.Sout)) = (W * C.Sin * Vᵀ) * C.Sout by
        simp only [Matrix.mul_assoc]]
  rw [show C.Sout * W * C.Sin * Vᵀ = C.Sout * (W * C.Sin * Vᵀ) by
        simp only [Matrix.mul_assoc]]
  exact Matrix.trace_mul_comm _ _

/-- Pairing bound `|⟨V, W⟩_Σ| ≤ CSig² ‖V‖_F ‖W‖_F` when `‖Σ_out‖, ‖Σ_in‖ ≤ CSig`. -/
private lemma hv_pS_le {m n : ℕ} (C : Covariances m n) (CSig : ℝ)
    (hO : opNorm C.Sout ≤ CSig) (hI : opNorm C.Sin ≤ CSig) (V W : Mat m n) :
    |Muon.Setup.pairSigma C V W| ≤ CSig ^ 2 * (fro V * fro W) := by
  have hCS : 0 ≤ CSig := (hv_opNorm_nonneg _).trans hO
  have h1 : fro (C.Sout * V * C.Sin) ≤ CSig * fro V * CSig := by
    calc fro (C.Sout * V * C.Sin) ≤ fro (C.Sout * V) * opNorm C.Sin := hv_fro_mul_le_right _ _
      _ ≤ (opNorm C.Sout * fro V) * opNorm C.Sin :=
          mul_le_mul_of_nonneg_right (hv_fro_mul_le_left _ _) (hv_opNorm_nonneg _)
      _ ≤ (CSig * fro V) * CSig :=
          mul_le_mul (mul_le_mul_of_nonneg_right hO (hv_fro_nn _)) hI (hv_opNorm_nonneg _)
            (mul_nonneg hCS (hv_fro_nn _))
      _ = CSig * fro V * CSig := rfl
  have h2 := hv_trace_mul_transpose_le (C.Sout * V * C.Sin) W
  unfold Muon.Setup.pairSigma
  calc |Matrix.trace (C.Sout * V * C.Sin * Wᵀ)| ≤ fro (C.Sout * V * C.Sin) * fro W := h2
    _ ≤ (CSig * fro V * CSig) * fro W := mul_le_mul_of_nonneg_right h1 (hv_fro_nn _)
    _ = CSig ^ 2 * (fro V * fro W) := by ring

private lemma hv_isProb (F : FrozenParams m n B) (S : FrozenSamples P m n B) :
    IsProbabilityMeasure P := by
  refine ⟨?_⟩
  have h := S.law 0 ⟨0, F.hB⟩
  have h1 : (P.map (S.zw 0 ⟨0, F.hB⟩)) Set.univ = 1 := by
    rw [h]; exact measure_univ
  rwa [Measure.map_apply (S.meas _ _) MeasurableSet.univ, Set.preimage_univ] at h1

private lemma hv_abs_entry_le_fro {k l : ℕ} (K : Mat k l) (i : Fin k) (j : Fin l) :
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

private lemma hv_summable_mat_of_fro {k l : ℕ} {ι : Type*} (f : ι → Mat k l)
    (hf : Summable fun j => fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun k => ?_
  refine Summable.of_norm_bounded hf (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact hv_abs_entry_le_fro (f j) i k

private lemma hv_summand_cont (F : FrozenParams m n B) :
    Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
  fun_prop

private lemma hv_batch_sm (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (hv_summand_cont F).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private lemma hv_buf_aesm [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : AEStronglyMeasurable (frozenBuf F S t) P := by
  have : TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))
  have hae := (lem_app_setup_ema_law_i F S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (hv_batch_sm F S (t + 1 - (j : ℤ))).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      hv_summable_mat_of_fro _ (hω t)
    exact hs.hasSum.tendsto_sum_nat

private lemma hv_Q_meas {k l : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) : Measurable (fun K : Mat k l => Q ϱ K) :=
  (measurable_Q (m := k) (n := l)).comp
    ((measurable_const (a := (⟨ϱ, hϱ.le⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma hv_upd_aesm (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) : AEStronglyMeasurable (frozenUpd F S ϱ t) P := by
  have := hv_isProb F S
  exact ((hv_Q_meas ϱ hϱ).comp_aemeasurable (hv_buf_aesm F S t).aemeasurable).aestronglyMeasurable

private lemma hv_upd_fro_le (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) (ω : Ω) : fro (frozenUpd F S ϱ t ω) ≤ (m : ℝ) + 1 := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ.le (frozenBuf F S t ω)
  have h4 : ((frozenBuf F S t ω).rank : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast h3.trans (min_le_left _ _)
  have h5 : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by
    have : fro (Q ϱ (frozenBuf F S t ω)) ^ 2 ≤ (m : ℝ) := h2.trans h4
    unfold frozenUpd; nlinarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
  exact (pow_le_pow_iff_left₀ (hv_fro_nn _) (by positivity) two_ne_zero).mp h5

private lemma hv_upd_entry_int (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => frozenUpd F S ϱ t ω i j) P := by
  have := hv_isProb F S
  refine Integrable.of_bound (C := (m : ℝ) + 1) ?_ ?_
  · exact ((continuous_apply j).comp (continuous_apply i)).comp_aestronglyMeasurable
      (hv_upd_aesm F S hϱ t)
  · exact Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact (hv_abs_entry_le_fro _ i j).trans (hv_upd_fro_le F S hϱ t ω)


private lemma hv_trace_expand {k l : ℕ} (Fo : Mat k k) (Gi : Mat l l) (X Y μ ν : Mat k l) :
    Matrix.trace (Fo * (X - μ) * Gi * (Y - ν)ᵀ) =
      Matrix.trace (Fo * X * Gi * Yᵀ) - Matrix.trace ((Gi * νᵀ * Fo) * X)
        - Matrix.trace ((Fo * μ * Gi) * Yᵀ) + Matrix.trace (Fo * μ * Gi * νᵀ) := by
  have e1 : Matrix.trace (Fo * X * Gi * νᵀ) = Matrix.trace ((Gi * νᵀ * Fo) * X) := by
    rw [show Fo * X * Gi * νᵀ = Fo * (X * Gi * νᵀ) by simp only [Matrix.mul_assoc]]
    rw [Matrix.trace_mul_comm,
      show X * Gi * νᵀ * Fo = X * (Gi * νᵀ * Fo) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm]
  have e2 : Matrix.trace (Fo * μ * Gi * Yᵀ) = Matrix.trace ((Fo * μ * Gi) * Yᵀ) := rfl
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.transpose_sub, Matrix.trace_sub]
  rw [← e1]
  ring

private lemma hv_int_trace_mul {a b : ℕ} (A : Mat a b) (M : Ω → Mat b a)
    (hM : ∀ i j, Integrable (fun ω => M ω i j) P) :
    Integrable (fun ω => Matrix.trace (A * M ω)) P ∧
      ∫ ω, Matrix.trace (A * M ω) ∂P = Matrix.trace (A * Muon.mean P M) := by
  have hf : ∀ ω, Matrix.trace (A * M ω) = ∑ i, ∑ j, A i j * M ω j i := by
    intro ω; simp [Matrix.trace, Matrix.mul_apply]
  simp_rw [hf]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hM j i).const_mul _, ?_⟩
  rw [integral_finsetSum (Finset.univ : Finset (Fin a)) (f := fun i ω => ∑ j, A i j * M ω j i)
    (fun i _ => integrable_finsetSum _ fun j _ => (hM j i).const_mul _)]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Muon.mean, Matrix.of_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum (Finset.univ : Finset (Fin b)) (f := fun j ω => A i j * M ω j i)
    (fun j _ => (hM j i).const_mul _)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]

private lemma hv_trace_bound {k l : ℕ} (Fo : Mat k k) (Gi : Mat l l) (X Y : Mat k l) :
    |Matrix.trace (Fo * X * Gi * Yᵀ)| ≤ opNorm Fo * fro X * opNorm Gi * fro Y := by
  refine (hv_trace_mul_transpose_le (Fo * X * Gi) Y).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (hv_fro_nn _)
  calc fro (Fo * X * Gi) ≤ fro (Fo * X) * opNorm Gi := hv_fro_mul_le_right _ _
    _ ≤ (opNorm Fo * fro X) * opNorm Gi :=
        mul_le_mul_of_nonneg_right (hv_fro_mul_le_left _ _) (hv_opNorm_nonneg _)

private lemma hv_trace_aesm {k l : ℕ} (Fo : Mat k k) (Gi : Mat l l) {X Y : Ω → Mat k l}
    (hX : AEStronglyMeasurable X P) (hY : AEStronglyMeasurable Y P) :
    AEStronglyMeasurable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)) P := by
  have h1 : Continuous (fun p : Mat k l × Mat k l => p.1) := continuous_fst
  have h2 : Continuous (fun p : Mat k l × Mat k l => p.2ᵀ) := continuous_snd.matrix_transpose
  have h3 : Continuous (fun p : Mat k l × Mat k l => Fo * p.1 * Gi * p.2ᵀ) :=
    (((continuous_const (y := Fo)).matrix_mul h1).matrix_mul (continuous_const (y := Gi))).matrix_mul h2
  have hc : Continuous (fun p : Mat k l × Mat k l => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ)) :=
    h3.matrix_trace
  have hp : AEStronglyMeasurable (fun ω => (X ω, Y ω)) P := hX.prodMk hY
  exact Continuous.comp_aestronglyMeasurable
    (g := fun p : Mat k l × Mat k l => Matrix.trace (Fo * p.1 * Gi * p.2ᵀ))
    (f := fun ω => (X ω, Y ω)) hc hp

/-- `lem:app-vol-centering`, part (i), snapshot `cr-2026-10-23`. Declaration of record for the
first inequality of the lemma (the bound on the uncentred tested covariance). Finite dimension;
`ε_B` and the mean bound `hmean` are the conclusions of `thm:app-drift-mean` (imported as
hypotheses, for every time `s` by stationarity). The norms of the test matrices are operator norms.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Centering]\label{lem:app-vol-centering}
Under \cref{assum:app-setup-regime}, for all $\ridge,\ridge'\in[\ridge_-,\ridge_+]$,
every lag $\ell\ge0$ and $\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-centering}
\Big|\frac1B\EE\Tr\big[F\,{\mathsf S}_t(\ridge)\,G\,{\mathsf S}_{t+\ell}(\ridge')^\T\big]-C_\ell[F,G](\ridge,\ridge')\Big|
\le\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B},
\end{equation}
with $\varepsilon_B\to0$ the sequence of \cref{thm:app-drift-mean}, and
\begin{equation}\label{eqn:app-vol-centering-sample}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\abs{Z(\ridge)-Z^{\mathrm c}(\ridge)}\le
C_\Sigma^2\Big(\frac{4\sqrt{\gamma_\star}}{\sqrt B}(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)+\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B}\Big).
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_centering_i (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ϱlo ϱhi CSig εB : ℝ) (hϱ : 0 < ϱlo)
    (hmean : ∀ s : ℤ, ∀ ϱ ∈ Icc ϱlo ϱhi,
      fro (Muon.mean P (frozenUpd F S ϱ s)) ≤ CSig / Real.sqrt ϱlo + εB)
    (ℓ : ℕ) {ϱ ϱ' : ℝ} (hϱI : ϱ ∈ Icc ϱlo ϱhi) (hϱ'I : ϱ' ∈ Icc ϱlo ϱhi)
    (Fo : Mat m m) (Gi : Mat n n) (hFo : opNorm Fo ≤ 1) (hGi : opNorm Gi ≤ 1) :
    |((B : ℝ)⁻¹ * (∫ ω, Matrix.trace (Fo * frozenUpd F S ϱ t ω * Gi *
          (frozenUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P)) - def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ'|
      ≤ (CSig / Real.sqrt ϱlo + εB) ^ 2 / B := by
  have hP := hv_isProb F S
  have hϱ1 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  have hϱ2 : 0 < ϱ' := lt_of_lt_of_le hϱ hϱ'I.1
  set X := frozenUpd F S ϱ t with hX
  set Y := frozenUpd F S ϱ' (t + (ℓ : ℤ)) with hY
  set μ := Muon.mean P X with hμ
  set ν := Muon.mean P Y with hν
  have hXi : ∀ i j, Integrable (fun ω => X ω i j) P := hv_upd_entry_int F S hϱ1 t
  have hYi : ∀ i j, Integrable (fun ω => Y ω i j) P := hv_upd_entry_int F S hϱ2 _
  have hI1 : Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ)) P := by
    refine Integrable.of_bound (C := opNorm Fo * ((m : ℝ) + 1) * opNorm Gi * ((m : ℝ) + 1)) ?_ ?_
    · exact hv_trace_aesm Fo Gi (hv_upd_aesm F S hϱ1 t) (hv_upd_aesm F S hϱ2 _)
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (hv_trace_bound Fo Gi (X ω) (Y ω)).trans ?_
      have h1 := hv_upd_fro_le F S hϱ1 t ω
      have h2 := hv_upd_fro_le F S hϱ2 (t + (ℓ : ℤ)) ω
      have n1 := hv_opNorm_nonneg Fo
      have n2 := hv_opNorm_nonneg Gi
      have f1 := hv_fro_nn (X ω)
      have f2 := hv_fro_nn (Y ω)
      exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left h1 n1) le_rfl n2
        (mul_nonneg n1 (by linarith))) h2 f2 (by positivity)
  obtain ⟨hA1i, hA1⟩ := hv_int_trace_mul (Gi * νᵀ * Fo) X hXi
  obtain ⟨hA2i, hA2⟩ := hv_int_trace_mul (Fo * μ * Gi) (fun ω => (Y ω)ᵀ) (fun i j => hYi j i)
  have hmeanT : Muon.mean P (fun ω => (Y ω)ᵀ) = νᵀ := by
    ext i j; rfl
  rw [hmeanT] at hA2
  have hcyc : Matrix.trace ((Gi * νᵀ * Fo) * μ) = Matrix.trace (Fo * μ * Gi * νᵀ) := by
    rw [Matrix.trace_mul_comm (Gi * νᵀ * Fo) μ,
      show Fo * μ * Gi * νᵀ = Fo * (μ * Gi * νᵀ) by simp only [Matrix.mul_assoc],
      Matrix.trace_mul_comm Fo]
    simp only [Matrix.mul_assoc]
  have hpt : ∀ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) =
      Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) - Matrix.trace ((Gi * νᵀ * Fo) * X ω)
        - Matrix.trace ((Fo * μ * Gi) * (Y ω)ᵀ) + Matrix.trace (Fo * μ * Gi * νᵀ) :=
    fun ω => hv_trace_expand Fo Gi (X ω) (Y ω) μ ν
  have hI0 : ∫ ω, Matrix.trace (Fo * centredUpd F S ϱ t ω * Gi *
        (centredUpd F S ϱ' (t + (ℓ : ℤ)) ω)ᵀ) ∂P =
      (∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) ∂P) - Matrix.trace (Fo * μ * Gi * νᵀ) := by
    simp_rw [hpt]
    have e1 : Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) -
        Matrix.trace ((Gi * νᵀ * Fo) * X ω)) P := hI1.sub hA1i
    have e2 : Integrable (fun ω => Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) -
        Matrix.trace ((Gi * νᵀ * Fo) * X ω) - Matrix.trace ((Fo * μ * Gi) * (Y ω)ᵀ)) P :=
      e1.sub hA2i
    rw [integral_add e2 (integrable_const _), integral_sub e1 hA2i, integral_sub hI1 hA1i,
      hA1, hA2]
    simp only [integral_const, probReal_univ, one_smul]
    rw [← hμ, hcyc]
    ring
  have hdef : def_app_vol_lag F S ℓ t Fo Gi ϱ ϱ' =
      (B : ℝ)⁻¹ * ((∫ ω, Matrix.trace (Fo * X ω * Gi * (Y ω)ᵀ) ∂P) -
        Matrix.trace (Fo * μ * Gi * νᵀ)) := by
    unfold def_app_vol_lag
    rw [← hI0]
  rw [hdef, ← mul_sub, sub_sub_cancel, abs_mul]
  have hB0 : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hbd := hv_trace_bound Fo Gi μ ν
  have hm1 := hmean t ϱ ⟨hϱI.1, hϱI.2⟩
  have hm2 := hmean (t + (ℓ : ℤ)) ϱ' ⟨hϱ'I.1, hϱ'I.2⟩
  have f1 := hv_fro_nn μ
  have f2 := hv_fro_nn ν
  have h1 : |Matrix.trace (Fo * μ * Gi * νᵀ)| ≤ (CSig / Real.sqrt ϱlo + εB) ^ 2 := by
    refine hbd.trans ?_
    have : opNorm Fo * fro μ * opNorm Gi * fro ν ≤ 1 * fro μ * 1 * fro ν :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hFo f1) hGi (hv_opNorm_nonneg _)
        (mul_nonneg zero_le_one f1)) le_rfl f2 (mul_nonneg (mul_nonneg zero_le_one f1) zero_le_one)
    refine this.trans ?_
    rw [one_mul, mul_one, sq]
    exact mul_le_mul hm1 hm2 f2 (f1.trans hm1)
  rw [abs_of_pos (inv_pos.mpr hB0), div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hB0.le)

/-- `lem:app-vol-centering`, part (ii), snapshot `cr-2026-10-23`. Declaration of record for the
sample bound on `Z − Z^c`. Holds at every sample point (the paper's bound is deterministic given
`‖S_t(ϱ)‖_F ≤ √(γ⋆ B)`, from `lem:app-setup-filter`(i) and `SizeFin`). `ε_B` and `hmean` as in
part (i). LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{lemma}[Centering]\label{lem:app-vol-centering}
Under \cref{assum:app-setup-regime}, for all $\ridge,\ridge'\in[\ridge_-,\ridge_+]$,
every lag $\ell\ge0$ and $\norm F,\norm G\le1$,
\begin{equation}\label{eqn:app-vol-centering}
\Big|\frac1B\EE\Tr\big[F\,{\mathsf S}_t(\ridge)\,G\,{\mathsf S}_{t+\ell}(\ridge')^\T\big]-C_\ell[F,G](\ridge,\ridge')\Big|
\le\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B},
\end{equation}
with $\varepsilon_B\to0$ the sequence of \cref{thm:app-drift-mean}, and
\begin{equation}\label{eqn:app-vol-centering-sample}
\sup_{\ridge\in[\ridge_-,\ridge_+]}\abs{Z(\ridge)-Z^{\mathrm c}(\ridge)}\le
C_\Sigma^2\Big(\frac{4\sqrt{\gamma_\star}}{\sqrt B}(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)+\frac{(C_\Sigma\ridge_-^{-1/2}+\varepsilon_B)^2}{B}\Big).
\end{equation}
\end{lemma}
```
-/
theorem lem_app_vol_centering_ii (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (γstar CSig ϱlo ϱhi εB : ℝ) (hSize : SizeFin F.C B γstar CSig) (hϱ : 0 < ϱlo)
    (hmean : ∀ s : ℤ, ∀ ϱ ∈ Icc ϱlo ϱhi,
      fro (Muon.mean P (frozenUpd F S ϱ s)) ≤ CSig / Real.sqrt ϱlo + εB) :
    ∀ ω : Ω, ∀ ϱ ∈ Icc ϱlo ϱhi,
      |sameTimeZ F S ϱ t ω - sameTimeZc F S ϱ t ω| ≤
        CSig ^ 2 * (4 * Real.sqrt γstar / Real.sqrt B * (CSig / Real.sqrt ϱlo + εB) +
          (CSig / Real.sqrt ϱlo + εB) ^ 2 / B) := by
  obtain ⟨hmaxγ, hO, hI⟩ := hSize
  intro ω ϱ hϱI
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  set μ := CSig / Real.sqrt ϱlo + εB with hμdef
  have hSb : fro (Muon.mean P (frozenUpd F S ϱ t)) ≤ μ := hmean t ϱ hϱI
  have hs0 : 0 ≤ fro (Muon.mean P (frozenUpd F S ϱ t)) := hv_fro_nn _
  have hμ0 : 0 ≤ μ := hs0.trans hSb
  have hB0 : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hγ : 0 ≤ γstar := by
    have h0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hX2 : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ γstar * (B : ℝ) := by
    have h1 := (lem_app_setup_filter_i ϱ hϱ0.le (frozenBuf F S t ω)).2.1
    have h2 := (lem_app_setup_filter_i ϱ hϱ0.le (frozenBuf F S t ω)).2.2.1
    have h3 : ((frozenBuf F S t ω).rank : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast h2.trans min_le_max
    unfold frozenUpd
    linarith
  have hXn : fro (frozenUpd F S ϱ t ω) ≤ Real.sqrt γstar * Real.sqrt (B : ℝ) := by
    rw [← Real.sqrt_mul hγ]
    exact Real.le_sqrt_of_sq_le hX2
  have hsub : Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω - Muon.mean P (frozenUpd F S ϱ t))
      (frozenUpd F S ϱ t ω - Muon.mean P (frozenUpd F S ϱ t)) =
      Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω) (frozenUpd F S ϱ t ω)
        - 2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω) (Muon.mean P (frozenUpd F S ϱ t))
        + Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t)) := by
    rw [hv_pS_sub_left, hv_pS_sub_right, hv_pS_sub_right]
    have hc := hv_pS_comm F.C (Muon.mean P (frozenUpd F S ϱ t)) (frozenUpd F S ϱ t ω)
    linarith
  have hZ : sameTimeZ F S ϱ t ω - sameTimeZc F S ϱ t ω =
      (B : ℝ)⁻¹ * (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
          (Muon.mean P (frozenUpd F S ϱ t)) -
        Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t))) := by
    simp only [sameTimeZ, sameTimeZc, centredUpd]
    rw [hsub]
    ring
  have hS1 := hv_pS_le F.C CSig hO hI (frozenUpd F S ϱ t ω) (Muon.mean P (frozenUpd F S ϱ t))
  have hS2 := hv_pS_le F.C CSig hO hI (Muon.mean P (frozenUpd F S ϱ t))
    (Muon.mean P (frozenUpd F S ϱ t))
  have hgs : fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t)) ≤
      Real.sqrt γstar * Real.sqrt (B : ℝ) * μ :=
    mul_le_mul hXn hSb hs0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hss : fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t)) ≤
      μ * μ := mul_le_mul hSb hSb hs0 hμ0
  have hc1 : CSig ^ 2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) ≤
      CSig ^ 2 * (Real.sqrt γstar * Real.sqrt (B : ℝ) * μ) :=
    mul_le_mul_of_nonneg_left hgs (sq_nonneg _)
  have hc2 : CSig ^ 2 * (fro (Muon.mean P (frozenUpd F S ϱ t)) *
      fro (Muon.mean P (frozenUpd F S ϱ t))) ≤ CSig ^ 2 * (μ * μ) :=
    mul_le_mul_of_nonneg_left hss (sq_nonneg _)
  have hpa := abs_sub (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
      (Muon.mean P (frozenUpd F S ϱ t)))
    (Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
      (Muon.mean P (frozenUpd F S ϱ t)))
  rw [abs_mul, abs_two] at hpa
  have hfin : |2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
        (Muon.mean P (frozenUpd F S ϱ t)) -
      Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
        (Muon.mean P (frozenUpd F S ϱ t))| ≤
      CSig ^ 2 * (2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) +
        fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t))) := by
    have e : CSig ^ 2 * (2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) +
        fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t))) =
        2 * (CSig ^ 2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t)))) +
        CSig ^ 2 * (fro (Muon.mean P (frozenUpd F S ϱ t)) *
          fro (Muon.mean P (frozenUpd F S ϱ t))) := by ring
    rw [e]
    linarith [hS1, hS2, hpa]
  rw [hZ]
  have hfinal : |(B : ℝ)⁻¹ * (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
          (Muon.mean P (frozenUpd F S ϱ t)) -
        Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t)))| ≤
      (B : ℝ)⁻¹ * (CSig ^ 2 * (2 * (Real.sqrt γstar * Real.sqrt (B : ℝ) * μ) + μ * μ)) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB0)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hB0.le)
    nlinarith
  refine hfinal.trans ?_
  have hsB : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := Real.mul_self_sqrt hB0.le
  have hsBpos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hB0
  have hgnn : 0 ≤ Real.sqrt γstar := Real.sqrt_nonneg _
  generalize Real.sqrt (B : ℝ) = s at hsB hsBpos ⊢
  rw [← hsB]
  have e : (s * s)⁻¹ * (CSig ^ 2 * (2 * (Real.sqrt γstar * s * μ) + μ * μ)) =
      CSig ^ 2 * (2 * (Real.sqrt γstar * μ / s) + μ ^ 2 / (s * s)) := by
    field_simp
  rw [e]
  have hnn : 0 ≤ CSig ^ 2 * (Real.sqrt γstar * μ / s) :=
    mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg hgnn hμ0) hsBpos.le)
  have e3 : CSig ^ 2 * (4 * Real.sqrt γstar / s * μ + μ ^ 2 / (s * s)) =
      CSig ^ 2 * (2 * (Real.sqrt γstar * μ / s) + μ ^ 2 / (s * s)) +
        2 * (CSig ^ 2 * (Real.sqrt γstar * μ / s)) := by ring
  rw [e3]
  linarith

/-! ## Same-time energies of rows and columns -/

private lemma hv_opNorm_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : opNorm (c • A) = |c| * opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma hv_branch_nonneg (Fw' : ℝ → ℝ) (ν ν' : FiniteMeasure ℝ) (s : ℝ) :
    0 ≤ (branchSol Fw' ν ν' s).2.2.1 ∧ 0 ≤ (branchSol Fw' ν ν' s).2.2.2 := by
  unfold branchSol
  split_ifs with h
  · have hs := h.choose_spec
    revert hs
    generalize h.choose = x
    obtain ⟨σ, σ', a, c⟩ := x
    intro hs
    exact ⟨hs.2.2.1, hs.2.2.2.1⟩
  · simp

private lemma hv_gram_eq {d : ℕ} (A : Mat d d) (hA : A.PosSemidef) {a ϱ : ℝ} (ha : 0 ≤ a)
    (hϱ : 0 < ϱ) :
    (a • A) * (a • A + ϱ • (1 : Mat d d))⁻¹ = 1 - ϱ • (ϱ • (1 : Mat d d) + a • A)⁻¹ := by
  have hU : IsUnit (ϱ • (1 : Mat d d) + a • A) :=
    ((Matrix.PosDef.one.smul hϱ).add_posSemidef (hA.smul ha)).isUnit
  rw [add_comm (a • A)]
  have hdet : IsUnit (ϱ • (1 : Mat d d) + a • A).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have h1 : (ϱ • (1 : Mat d d) + a • A) * (ϱ • (1 : Mat d d) + a • A)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have h2 : a • A = (ϱ • (1 : Mat d d) + a • A) - ϱ • (1 : Mat d d) := by abel
  calc (a • A) * (ϱ • (1 : Mat d d) + a • A)⁻¹
      = ((ϱ • (1 : Mat d d) + a • A) - ϱ • (1 : Mat d d)) * (ϱ • (1 : Mat d d) + a • A)⁻¹ :=
        congrArg (· * (ϱ • (1 : Mat d d) + a • A)⁻¹) h2
    _ = 1 - ϱ • (ϱ • (1 : Mat d d) + a • A)⁻¹ := by
        rw [Matrix.sub_mul, h1, Matrix.smul_mul, Matrix.one_mul]

private lemma hv_gram_int [IsProbabilityMeasure P] {k l : ℕ} (Z : Ω → Mat k l)
    (hZ : AEStronglyMeasurable Z P) (c : ℝ) (hc : ∀ ω, fro (Z ω) ≤ c)
    (ho : ∀ ω, opNorm (Z ω) ≤ 1) :
    (∀ i j : Fin k, Integrable (fun ω => (Z ω * (Z ω)ᵀ) i j) P) ∧
      (∀ i' j' : Fin l, Integrable (fun ω => ((Z ω)ᵀ * Z ω) i' j') P) := by
  have h1 : Continuous (fun K : Mat k l => K * Kᵀ) :=
    continuous_id.matrix_mul continuous_id.matrix_transpose
  have h2 : Continuous (fun K : Mat k l => Kᵀ * K) :=
    continuous_id.matrix_transpose.matrix_mul continuous_id
  refine ⟨fun i j => ?_, fun i' j' => ?_⟩
  · refine Integrable.of_bound (C := c) ?_ ?_
    · exact ((continuous_apply j).comp ((continuous_apply i).comp h1)).comp_aestronglyMeasurable hZ
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (hv_abs_entry_le_fro _ i j).trans ?_
      refine (hv_fro_mul_le_right _ _).trans ?_
      rw [hv_opNorm_transpose]
      calc fro (Z ω) * opNorm (Z ω) ≤ fro (Z ω) * 1 :=
            mul_le_mul_of_nonneg_left (ho ω) (hv_fro_nn _)
        _ ≤ c := by rw [mul_one]; exact hc ω
  · refine Integrable.of_bound (C := c) ?_ ?_
    · exact ((continuous_apply j').comp ((continuous_apply i').comp h2)).comp_aestronglyMeasurable hZ
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs]
      refine (hv_abs_entry_le_fro _ i' j').trans ?_
      refine (hv_fro_mul_le_right _ _).trans ?_
      calc fro (Z ω)ᵀ * opNorm (Z ω) ≤ fro (Z ω)ᵀ * 1 :=
            mul_le_mul_of_nonneg_left (ho ω) (hv_fro_nn _)
        _ ≤ c := by rw [mul_one, hv_fro_transpose]; exact hc ω

private lemma hv_unit_KKt {k l : ℕ} (K : Mat k l) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    IsUnit (K * Kᵀ + ϱ • (1 : Mat k k)) := by
  have h1 : (K * Kᵀ).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self Kᵀ
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_transpose] at this
    exact this
  rw [add_comm]
  exact ((Matrix.PosDef.one.smul hϱ).add_posSemidef h1).isUnit

private lemma hv_Q_gram_out {k l : ℕ} (K : Mat k l) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Q ϱ K * (Q ϱ K)ᵀ = (1 : Mat k k) - ϱ • Rs K ϱ := by
  have hB0 : 0 ≤ K * Kᵀ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self Kᵀ
  have hT0 : 0 ≤ K * Kᵀ + ϱ • (1 : Mat k k) :=
    add_nonneg hB0 (smul_nonneg hϱ.le zero_le_one)
  have hTu := hv_unit_KKt K hϱ
  rw [Q_eq_inv_sqrt_mul hϱ K]
  set T := K * Kᵀ + ϱ • (1 : Mat k k) with hT
  set s := CFC.sqrt T with hs
  have hss : s * s = T := CFC.sqrt_mul_sqrt_self T hT0
  have hsT : sᵀ = s := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hsdet : IsUnit s.det := by
    have h := (Matrix.isUnit_iff_isUnit_det _).mp hTu
    rw [← hss, Matrix.det_mul] at h
    exact (IsUnit.mul_iff.mp h).1
  have hsi : s * s⁻¹ = 1 := Matrix.mul_nonsing_inv _ hsdet
  have his : s⁻¹ * s = 1 := Matrix.nonsing_inv_mul _ hsdet
  have hsiT : (s⁻¹)ᵀ = s⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsT]
  have hKK : K * Kᵀ = s * s - ϱ • (1 : Mat k k) := by rw [hss, hT]; abel
  have hRs : Rs K ϱ = s⁻¹ * s⁻¹ := by
    change T⁻¹ = _
    rw [← hss, Matrix.mul_inv_rev]
  rw [hRs, Matrix.transpose_mul, hsiT]
  calc s⁻¹ * K * (Kᵀ * s⁻¹) = s⁻¹ * (K * Kᵀ) * s⁻¹ := by simp only [Matrix.mul_assoc]
    _ = s⁻¹ * (s * s - ϱ • (1 : Mat k k)) * s⁻¹ := by rw [hKK]
    _ = (s⁻¹ * s) * (s * s⁻¹) - ϱ • (s⁻¹ * s⁻¹) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.mul_assoc]
    _ = 1 - ϱ • (s⁻¹ * s⁻¹) := by rw [his, hsi, Matrix.mul_one]

private lemma hv_Q_gram_in {k l : ℕ} (K : Mat k l) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    (Q ϱ K)ᵀ * Q ϱ K = (1 : Mat l l) - ϱ • Rts K ϱ := by
  have hB0 : 0 ≤ K * Kᵀ := by
    rw [Matrix.nonneg_iff_posSemidef]
    simpa using Matrix.posSemidef_conjTranspose_mul_self Kᵀ
  have hT0 : 0 ≤ K * Kᵀ + ϱ • (1 : Mat k k) :=
    add_nonneg hB0 (smul_nonneg hϱ.le zero_le_one)
  have hTu := hv_unit_KKt K hϱ
  have hTu' : IsUnit (Kᵀ * K + ϱ • (1 : Mat l l)) := by
    simpa using hv_unit_KKt Kᵀ hϱ
  rw [Q_eq_inv_sqrt_mul hϱ K]
  set T := K * Kᵀ + ϱ • (1 : Mat k k) with hT
  set s := CFC.sqrt T with hs
  have hss : s * s = T := CFC.sqrt_mul_sqrt_self T hT0
  have hsT : sᵀ = s := by
    have h := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)).isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hsdet : IsUnit s.det := by
    have h := (Matrix.isUnit_iff_isUnit_det _).mp hTu
    rw [← hss, Matrix.det_mul] at h
    exact (IsUnit.mul_iff.mp h).1
  have hsiT : (s⁻¹)ᵀ = s⁻¹ := by rw [Matrix.transpose_nonsing_inv, hsT]
  have hTinv : s⁻¹ * s⁻¹ = T⁻¹ := by rw [← hss, Matrix.mul_inv_rev]
  have hdetT : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det _).mp hTu
  have hdetT' : IsUnit (Kᵀ * K + ϱ • (1 : Mat l l)).det := (Matrix.isUnit_iff_isUnit_det _).mp hTu'
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdetT
  have hT'T : (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ * (Kᵀ * K + ϱ • (1 : Mat l l)) = 1 :=
    Matrix.nonsing_inv_mul _ hdetT'
  have hT'T2 : (Kᵀ * K + ϱ • (1 : Mat l l)) * (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetT'
  -- push-through: Kᵀ T⁻¹ = T'⁻¹ Kᵀ
  have hpush : Kᵀ * T⁻¹ = (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ * Kᵀ := by
    have h1 : (Kᵀ * K + ϱ • (1 : Mat l l)) * Kᵀ = Kᵀ * T := by
      rw [hT]
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, Matrix.mul_assoc]
    calc Kᵀ * T⁻¹ = (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ *
          ((Kᵀ * K + ϱ • (1 : Mat l l)) * (Kᵀ * T⁻¹)) := by
          rw [← Matrix.mul_assoc, hT'T, Matrix.one_mul]
      _ = (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ * Kᵀ := by
          rw [← Matrix.mul_assoc _ Kᵀ, h1, Matrix.mul_assoc, hTT, Matrix.mul_one]
  rw [Matrix.transpose_mul, hsiT]
  calc Kᵀ * s⁻¹ * (s⁻¹ * K) = Kᵀ * (s⁻¹ * s⁻¹) * K := by simp only [Matrix.mul_assoc]
    _ = Kᵀ * T⁻¹ * K := by rw [hTinv]
    _ = (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ * (Kᵀ * K) := by rw [hpush, Matrix.mul_assoc]
    _ = (Kᵀ * K + ϱ • (1 : Mat l l))⁻¹ * ((Kᵀ * K + ϱ • (1 : Mat l l)) - ϱ • 1) := by
        congr 1; abel
    _ = 1 - ϱ • Rts K ϱ := by
        rw [Matrix.mul_sub, hT'T, Matrix.mul_smul, Matrix.mul_one]
        rfl

private lemma hv_upd_gram_int (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) :
    (∀ i j : Fin m, Integrable (fun ω => (frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) i j) P) ∧
      (∀ i' j' : Fin n,
        Integrable (fun ω => ((frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) i' j') P) := by
  have := hv_isProb F S
  exact hv_gram_int (frozenUpd F S ϱ t) (hv_upd_aesm F S hϱ t) ((m : ℝ) + 1)
    (hv_upd_fro_le F S hϱ t)
    (fun ω => (lem_app_setup_filter_i ϱ hϱ.le (frozenBuf F S t ω)).1)

private lemma hv_mean_gram_out (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) :
    Muon.mean P (fun ω => frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) =
      (1 : Mat m m) - ϱ • expRes (emaW F.β) F S t ϱ := by
  have := hv_isProb F S
  ext i j
  have hid : ∀ ω, Rs (frozenBuf F S t ω) ϱ i j =
      ϱ⁻¹ * ((1 : Mat m m) i j - (frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) i j) := by
    intro ω
    have h := hv_Q_gram_out (frozenBuf F S t ω) hϱ
    have h2 := congrFun (congrFun h i) j
    change (Q ϱ (frozenBuf F S t ω) * (Q ϱ (frozenBuf F S t ω))ᵀ) i j = _ at h2
    change _ = ϱ⁻¹ * ((1 : Mat m m) i j - (Q ϱ (frozenBuf F S t ω) * (Q ϱ (frozenBuf F S t ω))ᵀ) i j)
    rw [h2]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hint := (hv_upd_gram_int F S hϱ t).1 i j
  simp only [expRes, Muon.mean, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    weightedBuf_emaW_eq_frozenBuf, hid]
  rw [integral_const_mul, integral_sub (integrable_const _) hint]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  field_simp
  ring

private lemma hv_mean_gram_in (F : FrozenParams m n B) (S : FrozenSamples P m n B) {ϱ : ℝ}
    (hϱ : 0 < ϱ) (t : ℤ) :
    Muon.mean P (fun ω => (frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) =
      (1 : Mat n n) - ϱ • expResT (emaW F.β) F S t ϱ := by
  have := hv_isProb F S
  ext i j
  have hid : ∀ ω, Rts (frozenBuf F S t ω) ϱ i j =
      ϱ⁻¹ * ((1 : Mat n n) i j - ((frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) i j) := by
    intro ω
    have h := hv_Q_gram_in (frozenBuf F S t ω) hϱ
    have h2 := congrFun (congrFun h i) j
    change ((Q ϱ (frozenBuf F S t ω))ᵀ * Q ϱ (frozenBuf F S t ω)) i j = _ at h2
    change _ = ϱ⁻¹ * ((1 : Mat n n) i j -
      ((Q ϱ (frozenBuf F S t ω))ᵀ * Q ϱ (frozenBuf F S t ω)) i j)
    rw [h2]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    field_simp
    ring
  have hint := (hv_upd_gram_int F S hϱ t).2 i j
  simp only [expResT, Muon.mean, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    weightedBuf_emaW_eq_frozenBuf, hid]
  rw [integral_const_mul, integral_sub (integrable_const _) hint]
  simp only [integral_const, probReal_univ, smul_eq_mul]
  field_simp
  ring

private lemma hv_half_bound {d : ℕ} (A : Mat d d) (hA : A.PosSemidef) (Gm E : Mat d d) {a ϱ ϱhi eB : ℝ}
    (ha : 0 ≤ a) (hϱ : 0 < ϱ) (hϱhi : ϱ ≤ ϱhi)
    (hG : Gm = (a • A) * (a • A + ϱ • (1 : Mat d d))⁻¹)
    (hE : opNorm (E - (ϱ • (1 : Mat d d) + a • A)⁻¹) ≤ eB) :
    opNorm (((1 : Mat d d) - ϱ • E) - Gm) ≤ ϱhi * eB := by
  have heB : 0 ≤ eB := (hv_opNorm_nonneg _).trans hE
  rw [hG, hv_gram_eq A hA ha hϱ]
  have : ((1 : Mat d d) - ϱ • E) - (1 - ϱ • (ϱ • (1 : Mat d d) + a • A)⁻¹) =
      (-ϱ) • (E - (ϱ • (1 : Mat d d) + a • A)⁻¹) := by
    module
  rw [this, hv_opNorm_smul, abs_neg, abs_of_pos hϱ]
  calc ϱ * opNorm (E - (ϱ • (1 : Mat d d) + a • A)⁻¹) ≤ ϱ * eB :=
        mul_le_mul_of_nonneg_left hE hϱ.le
    _ ≤ ϱhi * eB := mul_le_mul_of_nonneg_right hϱhi heB

/-- `thm:app-vol-half-same`, part (i), output side, snapshot `cr-2026-10-23`. Declaration of
record for the first inequality of (i). `eB` is an upper bound for the sup `e_B` over `I`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_i_out (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (ϱlo ϱhi eB : ℝ) (hϱ : 0 < ϱlo)
    (heB : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expRes (emaW F.β) F S t s -
        Rbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eB) :
    ∀ ϱ ∈ Icc ϱlo ϱhi,
      opNorm (Muon.mean P (fun ω => frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) -
        halfGramOut F ϱ) ≤ ϱhi * eB := by
  intro ϱ hϱI
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  have hnn := (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F)
    (Muon.Drift.specInFM F) ϱ).1
  rw [hv_mean_gram_out F S hϱ0 t]
  exact hv_half_bound F.C.Sout F.C.psdOut _ _ hnn hϱ0 hϱI.2 rfl (heB ϱ hϱI)

/-- `thm:app-vol-half-same`, part (i), input side, snapshot `cr-2026-10-23`. Declaration of
record for the second inequality of (i). `eBt` is an upper bound for the sup `ẽ_B` over `I`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_i_in (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (ϱlo ϱhi eBt : ℝ) (hϱ : 0 < ϱlo)
    (heBt : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expResT (emaW F.β) F S t s -
        Rtbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eBt) :
    ∀ ϱ ∈ Icc ϱlo ϱhi,
      opNorm (Muon.mean P (fun ω => (frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) -
        halfGramIn F ϱ) ≤ ϱhi * eBt := by
  intro ϱ hϱI
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  have hnn := (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F)
    (Muon.Drift.specInFM F) ϱ).2
  rw [hv_mean_gram_in F S hϱ0 t]
  exact hv_half_bound F.C.Sin F.C.psdIn _ _ hnn hϱ0 hϱI.2 rfl (heBt ϱ hϱI)

/-! ### Private helpers for the same-time energies, part (ii) -/

private lemma hv_quad_le {d : ℕ} (D : Mat d d) (x : Vec d) (hx : x ⬝ᵥ x = 1) :
    |x ⬝ᵥ (D *ᵥ x)| ≤ opNorm D := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm]
  set xe : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm x with hxe
  set ye : EuclideanSpace ℝ (Fin d) := (EuclideanSpace.equiv (Fin d) ℝ).symm (D *ᵥ x) with hye
  have hD := D.l2_opNorm_mulVec xe
  have hxn : ‖xe‖ = 1 := by
    have h1 : ‖xe‖ ^ 2 = x ⬝ᵥ x := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [hxe, dotProduct, Real.norm_eq_abs, sq_abs, sq]
    rw [hx] at h1
    nlinarith [norm_nonneg xe]
  have hinner : x ⬝ᵥ (D *ᵥ x) = @inner ℝ _ _ xe ye := by
    simp [hxe, hye, dotProduct, PiLp.inner_apply, RCLike.inner_apply, mul_comm]
  have hye' : ‖ye‖ ≤ ‖D‖ := by
    have : ‖ye‖ ≤ ‖D‖ * ‖xe‖ := hD
    rwa [hxn, mul_one] at this
  calc |x ⬝ᵥ (D *ᵥ x)| = |@inner ℝ _ _ xe ye| := by rw [hinner]
    _ ≤ ‖xe‖ * ‖ye‖ := abs_real_inner_le_norm xe ye
    _ ≤ 1 * ‖D‖ := by rw [hxn]; exact mul_le_mul_of_nonneg_left hye' (by norm_num)
    _ = ‖D‖ := one_mul _

private lemma hv_col_dot {d : ℕ} (U : Mat d d) (hU : Uᵀ * U = 1) (i : Fin d) :
    (fun k => U k i) ⬝ᵥ (fun k => U k i) = 1 := by
  have h := congrFun (congrFun hU i) i
  simpa [Matrix.mul_apply, dotProduct] using h

private lemma hv_halfGram_eig {d : ℕ} (Sg : Mat d d) (hSg : Sg.PosSemidef) {a ϱ μ : ℝ}
    (ha : 0 ≤ a) (hϱ : 0 < ϱ) (x : Vec d) (hx : x ⬝ᵥ x = 1) (heig : Sg *ᵥ x = μ • x) :
    x ⬝ᵥ (((a • Sg) * (a • Sg + ϱ • (1 : Mat d d))⁻¹) *ᵥ x) = a * μ / (ϱ + a * μ) := by
  rw [hv_gram_eq Sg hSg ha hϱ]
  have hU : IsUnit (ϱ • (1 : Mat d d) + a • Sg) :=
    ((Matrix.PosDef.one.smul hϱ).add_posSemidef (hSg.smul ha)).isUnit
  have hdet : IsUnit (ϱ • (1 : Mat d d) + a • Sg).det := (Matrix.isUnit_iff_isUnit_det _).mp hU
  have hKx : (ϱ • (1 : Mat d d) + a • Sg) *ᵥ x = (ϱ + a * μ) • x := by
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, heig, smul_smul,
      add_smul]
  have hcancel : (ϱ + a * μ) • ((ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x) = x := by
    rw [← Matrix.mulVec_smul, ← hKx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  have hc : ϱ + a * μ ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hcancel
    rw [← hcancel] at hx
    simp at hx
  have hinv : (ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x = (ϱ + a * μ)⁻¹ • x := by
    calc (ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x
        = (ϱ + a * μ)⁻¹ • ((ϱ + a * μ) • ((ϱ • (1 : Mat d d) + a • Sg)⁻¹ *ᵥ x)) := by
          rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      _ = (ϱ + a * μ)⁻¹ • x := by rw [hcancel]
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, hinv, smul_smul,
    dotProduct_sub, dotProduct_smul, hx, smul_eq_mul, mul_one]
  field_simp
  ring

private lemma hv_int_quad {d : ℕ} (M : Ω → Mat d d)
    (hI : ∀ i j : Fin d, Integrable (fun ω => M ω i j) P) (x : Vec d) :
    ∫ ω, x ⬝ᵥ (M ω *ᵥ x) ∂P = x ⬝ᵥ (Muon.mean P M *ᵥ x) := by
  have hexp : ∀ ω, x ⬝ᵥ (M ω *ᵥ x) = ∑ i, ∑ j, x i * (M ω i j * x j) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hexp' : x ⬝ᵥ (Muon.mean P M *ᵥ x) = ∑ i, ∑ j, x i * (Muon.mean P M i j * x j) := by
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  have hint_i : ∀ i, Integrable (fun ω => ∑ j, x i * (M ω i j * x j)) P := fun i =>
    integrable_finset_sum _ (fun j _ => ((hI i j).mul_const (x j)).const_mul (x i))
  simp only [hexp]
  rw [hexp', integral_finset_sum _ (fun i _ => hint_i i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finset_sum _ (fun j _ => ((hI i j).mul_const (x j)).const_mul (x i))]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, integral_mul_const]
  rfl

private lemma hv_dot_self {k l : ℕ} (A : Mat k l) (x : Vec l) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (((Aᵀ) * A) *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec x Aᵀ (A *ᵥ x), Matrix.vecMul_transpose]

private lemma hv_sqrt_symm {d : ℕ} (A : Mat d d) : (CFC.sqrt A)ᵀ = CFC.sqrt A := by
  have h := (CFC.sqrt_nonneg A).isSelfAdjoint
  unfold IsSelfAdjoint at h
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma hv_sqrt_kill {d : ℕ} (A : Mat d d) (hA : A.PosSemidef) (x : Vec d)
    (hx : A *ᵥ x = 0) : CFC.sqrt A *ᵥ x = 0 := by
  have hsq : CFC.sqrt A * CFC.sqrt A = A :=
    CFC.sqrt_mul_sqrt_self A (Matrix.nonneg_iff_posSemidef.mpr hA)
  have h := hv_dot_self (CFC.sqrt A) x
  rw [hv_sqrt_symm A, hsq, hx, dotProduct_zero] at h
  exact dotProduct_self_eq_zero.mp h

private lemma hv_batch_left (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    frozenBatchG F S s ω = rOut F.C * (((B : ℝ)⁻¹) • ∑ a : Fin B,
      ((dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) •
        (outer (S.zw s a ω).1 (S.zw s a ω).2 * rIn F.C))) := by
  unfold frozenBatchG
  rw [Matrix.mul_smul, Matrix.mul_sum]
  simp only [Matrix.mul_smul, Matrix.mul_assoc]

private lemma hv_batch_right (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    frozenBatchG F S s ω = (((B : ℝ)⁻¹) • ∑ a : Fin B,
      ((dotProduct (S.zw s a ω).1 (Matrix.mulVec F.A (S.zw s a ω).2)) •
        (rOut F.C * outer (S.zw s a ω).1 (S.zw s a ω).2))) * rIn F.C := by
  unfold frozenBatchG
  rw [Matrix.smul_mul, Matrix.sum_mul]
  simp only [Matrix.smul_mul, Matrix.mul_assoc]

private lemma hv_rOut_symm {m n : ℕ} (C : Covariances m n) : (rOut C)ᵀ = rOut C :=
  hv_sqrt_symm C.Sout

private lemma hv_batch_T_zero (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω)
    (u : Vec m) (hu : rOut F.C *ᵥ u = 0) : (frozenBatchG F S s ω)ᵀ *ᵥ u = 0 := by
  rw [hv_batch_left, Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hv_rOut_symm, hu,
    Matrix.mulVec_zero]

private lemma hv_batch_mulVec_zero (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
    (ω : Ω) (v : Vec n) (hv : rIn F.C *ᵥ v = 0) : frozenBatchG F S s ω *ᵥ v = 0 := by
  rw [hv_batch_right, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

private lemma hv_tsum_mulVec_zero {k l : ℕ} (f : ℕ → Mat k l) (x : Vec l)
    (h : ∀ j, f j *ᵥ x = 0) : (∑' j, f j) *ᵥ x = 0 := by
  by_cases hs : Summable f
  · let Φ : Mat k l →+ Vec k :=
      { toFun := fun A => A *ᵥ x
        map_zero' := Matrix.zero_mulVec x
        map_add' := fun A B => Matrix.add_mulVec A B x }
    have hΦc : Continuous Φ := continuous_id.matrix_mulVec continuous_const
    have hsum := (hs.hasSum.map Φ hΦc).tsum_eq
    have h2 : (∑' j, f j) *ᵥ x = ∑' j, f j *ᵥ x := hsum.symm
    rw [h2]
    simp only [h, tsum_zero]
  · rw [tsum_eq_zero_of_not_summable hs, Matrix.zero_mulVec]

private lemma hv_frozenBuf_T_zero (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (ω : Ω) (u : Vec m) (hu : rOut F.C *ᵥ u = 0) : (frozenBuf F S t ω)ᵀ *ᵥ u = 0 := by
  unfold frozenBuf
  rw [Matrix.transpose_tsum]
  apply hv_tsum_mulVec_zero
  intro j
  rw [Matrix.transpose_smul, Matrix.smul_mulVec, hv_batch_T_zero F S _ ω u hu, smul_zero]

private lemma hv_frozenBuf_mulVec_zero (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (ω : Ω) (v : Vec n) (hv : rIn F.C *ᵥ v = 0) : frozenBuf F S t ω *ᵥ v = 0 := by
  unfold frozenBuf
  apply hv_tsum_mulVec_zero
  intro j
  rw [Matrix.smul_mulVec, hv_batch_mulVec_zero F S _ ω v hv, smul_zero]


/-- `thm:app-vol-half-same`, part (ii), rows, snapshot `cr-2026-10-23`. Declaration of record for
the row energies `𝔼‖S_t(ϱ)^⊤ u_i‖²` against `volraw_i(ϱ)`, uniform over the rows `i`.
`Sp` is the spectral data of `Σ_out` (eigenvectors `u_i = Sp.u i`, eigenvalues `μ_i = Sp.μ i`).
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_ii_rows (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Sp : SpectralData F.C) (ϱlo ϱhi eB : ℝ) (hϱ : 0 < ϱlo)
    (heB : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expRes (emaW F.β) F S t s -
        Rbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eB) :
    ∀ ϱ ∈ Icc ϱlo ϱhi, ∀ i : Fin m,
      |(∫ ω, dotProduct ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) ∂P) -
        volraw F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (Sp.μ i) ϱ| ≤ ϱhi * eB := by
  intro ϱ hϱI i
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  have hD := thm_app_vol_half_same_i_out F S t ϱlo ϱhi eB hϱ heB ϱ hϱI
  have hpt : ∀ ω, dotProduct ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i) =
      Sp.u i ⬝ᵥ ((frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) *ᵥ Sp.u i) := by
    intro ω
    have h := hv_dot_self (frozenUpd F S ϱ t ω)ᵀ (Sp.u i)
    rw [transpose_transpose] at h
    exact h
  have hu : Sp.u i ⬝ᵥ Sp.u i = 1 := hv_col_dot Sp.uOut Sp.huOut i
  have hH : Sp.u i ⬝ᵥ (halfGramOut F ϱ *ᵥ Sp.u i) =
      volraw F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (Sp.μ i) ϱ := by
    unfold halfGramOut volraw
    exact hv_halfGram_eig F.C.Sout F.C.psdOut
      (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).1
      hϱ0 (Sp.u i) hu (Sp.eigOut i)
  have hint := (hv_upd_gram_int F S hϱ0 t).1
  have hI := hv_int_quad (fun ω => frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) hint (Sp.u i)
  beta_reduce at hI
  have heq : (fun ω => dotProduct ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)
      ((frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i)) =
      fun ω => Sp.u i ⬝ᵥ ((frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) *ᵥ Sp.u i) :=
    funext hpt
  rw [heq, hI]
  have key := hv_quad_le (Muon.mean P (fun ω => frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ) -
    halfGramOut F ϱ) (Sp.u i) hu
  rw [Matrix.sub_mulVec, dotProduct_sub, hH] at key
  exact key.trans hD

/-- `thm:app-vol-half-same`, part (ii), columns, snapshot `cr-2026-10-23`. Declaration of record
for the column energies `𝔼‖S_t(ϱ) v_j‖²` against `ṽ^{(0)}_j(ϱ)`, uniform over the columns `j`.
`Sp.v j`, `Sp.lam j` are the input eigenvector and eigenvalue.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_ii_cols (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Sp : SpectralData F.C) (ϱlo ϱhi eBt : ℝ) (hϱ : 0 < ϱlo)
    (heBt : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expResT (emaW F.β) F S t s -
        Rtbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eBt) :
    ∀ ϱ ∈ Icc ϱlo ϱhi, ∀ j : Fin n,
      |(∫ ω, dotProduct (frozenUpd F S ϱ t ω *ᵥ Sp.v j) (frozenUpd F S ϱ t ω *ᵥ Sp.v j) ∂P) -
        volTildeZero F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (Sp.lam j) ϱ|
        ≤ ϱhi * eBt := by
  intro ϱ hϱI j
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  have hD := thm_app_vol_half_same_i_in F S t ϱlo ϱhi eBt hϱ heBt ϱ hϱI
  have hpt : ∀ ω, dotProduct (frozenUpd F S ϱ t ω *ᵥ Sp.v j) (frozenUpd F S ϱ t ω *ᵥ Sp.v j) =
      Sp.v j ⬝ᵥ (((frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) *ᵥ Sp.v j) :=
    fun ω => hv_dot_self (frozenUpd F S ϱ t ω) (Sp.v j)
  have hu : Sp.v j ⬝ᵥ Sp.v j = 1 := hv_col_dot Sp.vIn Sp.hvIn j
  have hH : Sp.v j ⬝ᵥ (halfGramIn F ϱ *ᵥ Sp.v j) =
      volTildeZero F.β (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) (Sp.lam j) ϱ := by
    unfold halfGramIn volTildeZero
    exact hv_halfGram_eig F.C.Sin F.C.psdIn
      (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).2
      hϱ0 (Sp.v j) hu (Sp.eigIn j)
  have hint := (hv_upd_gram_int F S hϱ0 t).2
  have hI := hv_int_quad (fun ω => (frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) hint (Sp.v j)
  beta_reduce at hI
  have heq : (fun ω => dotProduct (frozenUpd F S ϱ t ω *ᵥ Sp.v j) (frozenUpd F S ϱ t ω *ᵥ Sp.v j)) =
      fun ω => Sp.v j ⬝ᵥ (((frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) *ᵥ Sp.v j) :=
    funext hpt
  rw [heq, hI]
  have key := hv_quad_le (Muon.mean P (fun ω => (frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω) -
    halfGramIn F ϱ) (Sp.v j) hu
  rw [Matrix.sub_mulVec, dotProduct_sub, hH] at key
  exact key.trans hD

/-- `thm:app-vol-half-same`, part (ii), exact zero rows, snapshot `cr-2026-10-23`. Declaration of
record for `S_t(ϱ)^⊤ u_i = 0` whenever `μ_i = 0`. Pointwise in the sample, as the paper states it.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_ii_zero_rows (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Sp : SpectralData F.C) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo) :
    ∀ ϱ ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ i : Fin m, Sp.μ i = 0 →
      (frozenUpd F S ϱ t ω)ᵀ *ᵥ Sp.u i = 0 := by
  intro ϱ _ ω i hμ
  have hk : (frozenBuf F S t ω)ᵀ *ᵥ Sp.u i = 0 :=
    hv_frozenBuf_T_zero F S t ω (Sp.u i)
      (hv_sqrt_kill F.C.Sout F.C.psdOut (Sp.u i) (by
        have h := Sp.eigOut i
        rw [hμ, zero_smul] at h
        exact h))
  unfold frozenUpd Q
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]

/-- `thm:app-vol-half-same`, part (ii), exact zero columns, snapshot `cr-2026-10-23`. Declaration
of record for `S_t(ϱ) v_j = 0` whenever `λ_j = 0`. Pointwise in the sample.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_ii_zero_cols (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Sp : SpectralData F.C) (ϱlo ϱhi : ℝ) (hϱ : 0 < ϱlo) :
    ∀ ϱ ∈ Icc ϱlo ϱhi, ∀ ω : Ω, ∀ j : Fin n, Sp.lam j = 0 →
      frozenUpd F S ϱ t ω *ᵥ Sp.v j = 0 := by
  intro ϱ _ ω j hlam
  have hk : frozenBuf F S t ω *ᵥ Sp.v j = 0 :=
    hv_frozenBuf_mulVec_zero F S t ω (Sp.v j)
      (hv_sqrt_kill F.C.Sin F.C.psdIn (Sp.v j) (by
        have h := Sp.eigIn j
        rw [hlam, zero_smul] at h
        exact h))
  unfold frozenUpd Q
  rw [cfc_mul_transpose_mul_intertwine, ← Matrix.mulVec_mulVec, hk, Matrix.mulVec_zero]

private lemma hv_trace_basis {d : ℕ} (D U : Mat d d) (hU : Uᵀ * U = 1) :
    D.trace = ∑ i, (fun k => U k i) ⬝ᵥ (D *ᵥ (fun k => U k i)) := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  calc D.trace = (D * (U * Uᵀ)).trace := by rw [hU', Matrix.mul_one]
    _ = (Uᵀ * D * U).trace := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm (D * U), Matrix.mul_assoc]
    _ = _ := by simp [Matrix.trace, Matrix.mul_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum, mul_assoc]

private lemma hv_trace_weighted_basis {d : ℕ} (A D U : Mat d d) (μ : Fin d → ℝ)
    (hA : Aᵀ = A) (hU : Uᵀ * U = 1)
    (heig : ∀ i, A *ᵥ (fun k => U k i) = μ i • (fun k => U k i)) :
    (A * D).trace = ∑ i, μ i * ((fun k => U k i) ⬝ᵥ (D *ᵥ (fun k => U k i))) := by
  rw [hv_trace_basis (A * D) U hU]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA,
    heig i, smul_dotProduct, smul_eq_mul]

private lemma hv_abs_trace_mul {d : ℕ} (A D : Mat d d) :
    |(A * D).trace| ≤ (d : ℝ) * opNorm A * opNorm D := by
  have htrace : |(A * D).trace| ≤ (d : ℝ) * opNorm (A * D) := by
    calc |(A * D).trace| ≤ ∑ i, |(A * D) i i| := by
          simpa [Matrix.trace] using Finset.abs_sum_le_sum_abs (fun i => (A * D) i i) Finset.univ
      _ ≤ ∑ i : Fin d, opNorm (A * D) := Finset.sum_le_sum fun i _ => by
          have h := hv_quad_le (A * D) (Pi.single i 1) (by simp only [single_dotProduct, Pi.single_eq_same, one_mul])
          simpa only [Matrix.mulVec_single_one, single_dotProduct, one_mul, Matrix.col_apply] using h
      _ = _ := by simp
  have hmul : opNorm (A * D) ≤ opNorm A * opNorm D := by
    open scoped Matrix.Norms.L2Operator in
    simpa only [opNorm_eq_norm] using Matrix.l2_opNorm_mul A D
  exact htrace.trans (by nlinarith [mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg d : (0:ℝ) ≤ d)])

private lemma hv_total_trace_bound {d : ℕ} (A D : Mat d d) {γ CS e : ℝ}
    (hB : 0 < B) (hd : (d : ℝ) ≤ γ * B) (hA : opNorm A ≤ CS)
    (hD : opNorm D ≤ e) :
    |(B : ℝ)⁻¹ * (A * D).trace| ≤ γ * CS * e := by
  have hB' : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS := (hv_opNorm_nonneg A).trans hA
  have he := (hv_opNorm_nonneg D).trans hD
  have hγB : 0 ≤ γ * B := (Nat.cast_nonneg d : (0:ℝ) ≤ d).trans hd
  rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hB'.le)]
  calc (B : ℝ)⁻¹ * |(A * D).trace|
      ≤ (B : ℝ)⁻¹ * ((d : ℝ) * opNorm A * opNorm D) :=
        mul_le_mul_of_nonneg_left (hv_abs_trace_mul A D) (by positivity)
    _ ≤ (B : ℝ)⁻¹ * ((γ * B) * CS * e) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (mul_le_mul hd hA (hv_opNorm_nonneg A) hγB) hD
        (hv_opNorm_nonneg D) (mul_nonneg hγB hCS)
    _ = γ * CS * e := by field_simp

private lemma hv_zbar_gram (F : FrozenParams m n B) (Sp : SpectralData F.C)
    {ϱ : ℝ} (hϱ : 0 < ϱ) :
    zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) Sp.μ ϱ =
      (B : ℝ)⁻¹ * (F.C.Sout * halfGramOut F ϱ).trace := by
  have hA : F.C.Soutᵀ = F.C.Sout := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using F.C.psdOut.isHermitian.eq
  rw [hv_trace_weighted_basis _ _ Sp.uOut Sp.μ hA Sp.huOut Sp.eigOut]
  unfold zbarRaw
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (hv_halfGram_eig F.C.Sout F.C.psdOut
    (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ).1
    hϱ (Sp.u i) (hv_col_dot Sp.uOut Sp.huOut i) (Sp.eigOut i)).symm

/-- `thm:app-vol-half-same`, part (iii), finite dimension, mean bound, snapshot `cr-2026-10-23`.
Declaration of record for `|𝔼Z(ϱ) − Z̄(ϱ)| ≤ γ⋆ C_Σ ϱ₊ e_B` under `Σ_in = Id` (the mean part of (iii);
the limits are `thm_app_vol_half_same_iii_raw` and `_iii_centered`). `Z̄` is `zbarRaw`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iii_mean (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (Sp : SpectralData F.C) (γstar CSig ϱlo ϱhi eB : ℝ)
    (hSize : SizeFin F.C B γstar CSig) (hIn : F.C.Sin = 1) (hϱ : 0 < ϱlo)
    (heB : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expRes (emaW F.β) F S t s -
        Rbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eB) :
    ∀ ϱ ∈ Icc ϱlo ϱhi,
      |(∫ ω, sameTimeZ F S ϱ t ω ∂P) -
        zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) Sp.μ ϱ| ≤
          γstar * CSig * ϱhi * eB := by
  intro ϱ hϱI
  have hϱ0 := lt_of_lt_of_le hϱ hϱI.1
  let G := fun ω => frozenUpd F S ϱ t ω * (frozenUpd F S ϱ t ω)ᵀ
  have hmean : (∫ ω, sameTimeZ F S ϱ t ω ∂P) =
      (B : ℝ)⁻¹ * (F.C.Sout * Muon.mean P G).trace := by
    simp only [sameTimeZ, pairSigma, hIn, Matrix.mul_one, Matrix.mul_assoc]
    rw [integral_const_mul]
    exact congrArg ((B : ℝ)⁻¹ * ·)
      (hv_int_trace_mul F.C.Sout G (hv_upd_gram_int F S hϱ0 t).1).2
  rw [hmean, hv_zbar_gram F Sp hϱ0, ← mul_sub, ← Matrix.trace_sub, ← Matrix.mul_sub]
  have hb := thm_app_vol_half_same_i_out F S t ϱlo ϱhi eB hϱ heB ϱ hϱI
  have hd : (m : ℝ) ≤ γstar * B := (Nat.cast_le.mpr (le_max_left m n)).trans hSize.1
  exact (hv_total_trace_bound F.C.Sout (Muon.mean P G - halfGramOut F ϱ)
    F.hB hd hSize.2.1 hb).trans_eq (by ring)

private lemma hv_regime_sigma (R : SetupRegime) (k : ℕ) {s : ℝ} (hs : 0 < s) :
    (R.B k : ℝ)⁻¹ * ((R.F k).C.Sout *
      Rbar (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) (R.F k).C s).trace =
      (branchSol (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) s).1 := by
  have hK : (Muon.Drift.specOutFM (R.F k), Muon.Drift.specInFM (R.F k)) ∈
      classK R.CSig (max R.γstar 1) := by
    obtain ⟨o1, o2⟩ := assum_app_setup_regime_nuOut R k
    obtain ⟨i1, i2⟩ := assum_app_setup_regime_nuIn R k
    have hle := ENNReal.ofReal_le_ofReal (le_max_left R.γstar 1)
    exact ⟨(measure_mono (Set.subset_univ _)).trans (o2.trans hle), o1,
      (measure_mono (Set.subset_univ _)).trans (i2.trans hle), i1⟩
  have h := branchSol_spec (Fw_admissible (Muon.Drift.emaW_weightClass_regime R).1)
    (lt_of_lt_of_le one_pos R.hC) (lt_of_lt_of_le one_pos (le_max_right R.γstar 1)) hK hs
  unfold Rbar
  generalize branchSol (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
    (Muon.Drift.specInFM (R.F k)) s = x at h ⊢
  obtain ⟨σ, σ', a, c⟩ := x
  obtain ⟨-, -, ha, -, hσ, -, -, -⟩ := h
  change σ = ∫ x, x / (a * x + s) ∂(nuOut (R.F k).C (R.B k)) at hσ
  rw [hσ, (def_app_de_branch_trace (R.F k).C (R.F k).hB hs ha).1,
    add_comm (s • (1 : Mat (R.m k) (R.m k)))]

private lemma hv_raw_trace_error (R : SetupRegime) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (k : ℕ) (S : FrozenSamples P (R.m k) (R.n k) (R.B k))
    (Sp : SpectralData (R.F k).C) (t : ℤ) (hIn : (R.F k).C.Sin = 1)
    {s : ℝ} (hs : 0 < s) (ω : Ω) :
    sameTimeZ (R.F k) S s t ω -
      zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) Sp.μ s =
      -s * ((R.B k : ℝ)⁻¹ * ((R.F k).C.Sout *
        Rs (WeightedBuf (emaW R.β) (R.F k) S t ω) s).trace -
          (branchSol (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) s).1) := by
  rw [hv_zbar_gram (R.F k) Sp hs]
  have ha := (hv_branch_nonneg (Fw (emaW (R.F k).β))
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) s).1
  simp only [sameTimeZ, pairSigma, hIn, Matrix.mul_one, Matrix.mul_assoc, frozenUpd]
  rw [hv_Q_gram_out _ hs]
  unfold halfGramOut
  rw [hv_gram_eq _ (R.F k).C.psdOut ha hs]
  simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.trace_sub,
    Matrix.trace_smul, smul_eq_mul]
  have hσ := hv_regime_sigma R k hs
  unfold Rbar at hσ
  rw [R.hβ k] at *
  simp only [WeightedBuf, frozenBuf, R.hβ]
  rw [← hσ]
  ring

/-- `thm:app-vol-half-same`, part (iii), raw total, snapshot `cr-2026-10-23`. Declaration of record
for `𝔼 sup_{ϱ∈I} |Z(ϱ) − Z̄(ϱ)|² → 0` along a regime with `Σ_in = Id`. The expectation of the
supremum is a lintegral of `⨆` over `ℝ≥0∞`. LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iii_raw {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (Sp : ∀ k, SpectralData (R.F k).C) (hIn : ∀ k, (R.F k).C.Sin = 1) :
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((sameTimeZ (R.F k) (S k) ϱ t ω -
          zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (Sp k).μ ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  have htrace := (cor_app_de_trace_iii R (emaW R.β)
    (Muon.Drift.emaW_weightClass_regime R) P S
    (fun k => Muon.Drift.specOutFM (R.F k)) (fun k => Muon.Drift.specInFM (R.F k))
    (fun _ => rfl) (fun _ => rfl) t (Icc R.ϱlo R.ϱhi) isCompact_Icc
    (fun _ hs => lt_of_lt_of_le R.hϱ.1 hs.1)).2
  have hlim := ENNReal.Tendsto.const_mul htrace
    (a := ENNReal.ofReal (R.ϱhi ^ 2)) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun k => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ω
  refine iSup₂_le fun s hs => ?_
  rw [hv_raw_trace_error R k (S k) (Sp k) t (hIn k)
    (lt_of_lt_of_le R.hϱ.1 hs.1) ω]
  have hs2 : s ^ 2 ≤ R.ϱhi ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (lt_of_lt_of_le R.hϱ.1 hs.1)) hs.2 2
  simp only [mul_pow, neg_sq, Real.norm_eq_abs, sq_abs] at *
  calc ENNReal.ofReal (s ^ 2 * _ ^ 2)
      ≤ ENNReal.ofReal (R.ϱhi ^ 2 * _ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hs2 (sq_nonneg _))
    _ = ENNReal.ofReal (R.ϱhi ^ 2) * ENNReal.ofReal (_ ^ 2) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_iSup₂_of_le s hs le_rfl) zero_le

private lemma hv_centering_at (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (γstar CSig ϱlo ϱhi εB : ℝ) (hSize : SizeFin F.C B γstar CSig) (hϱ : 0 < ϱlo)
    (hmean : ∀ ϱ ∈ Icc ϱlo ϱhi,
      fro (Muon.mean P (frozenUpd F S ϱ t)) ≤ CSig / Real.sqrt ϱlo + εB) :
    ∀ ω : Ω, ∀ ϱ ∈ Icc ϱlo ϱhi,
      |sameTimeZ F S ϱ t ω - sameTimeZc F S ϱ t ω| ≤
        CSig ^ 2 * (4 * Real.sqrt γstar / Real.sqrt B * (CSig / Real.sqrt ϱlo + εB) +
          (CSig / Real.sqrt ϱlo + εB) ^ 2 / B) := by
  obtain ⟨hmaxγ, hO, hI⟩ := hSize
  intro ω ϱ hϱI
  have hϱ0 : 0 < ϱ := lt_of_lt_of_le hϱ hϱI.1
  set μ := CSig / Real.sqrt ϱlo + εB with hμdef
  have hSb : fro (Muon.mean P (frozenUpd F S ϱ t)) ≤ μ := hmean ϱ hϱI
  have hs0 : 0 ≤ fro (Muon.mean P (frozenUpd F S ϱ t)) := hv_fro_nn _
  have hμ0 : 0 ≤ μ := hs0.trans hSb
  have hB0 : (0 : ℝ) < B := by exact_mod_cast F.hB
  have hγ : 0 ≤ γstar := by
    have h0 : (0 : ℝ) ≤ ((max m n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hX2 : fro (frozenUpd F S ϱ t ω) ^ 2 ≤ γstar * (B : ℝ) := by
    have h1 := (lem_app_setup_filter_i ϱ hϱ0.le (frozenBuf F S t ω)).2.1
    have h2 := (lem_app_setup_filter_i ϱ hϱ0.le (frozenBuf F S t ω)).2.2.1
    have h3 : ((frozenBuf F S t ω).rank : ℝ) ≤ ((max m n : ℕ) : ℝ) := by
      exact_mod_cast h2.trans min_le_max
    unfold frozenUpd
    linarith
  have hXn : fro (frozenUpd F S ϱ t ω) ≤ Real.sqrt γstar * Real.sqrt (B : ℝ) := by
    rw [← Real.sqrt_mul hγ]
    exact Real.le_sqrt_of_sq_le hX2
  have hsub : Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω - Muon.mean P (frozenUpd F S ϱ t))
      (frozenUpd F S ϱ t ω - Muon.mean P (frozenUpd F S ϱ t)) =
      Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω) (frozenUpd F S ϱ t ω)
        - 2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω) (Muon.mean P (frozenUpd F S ϱ t))
        + Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t)) := by
    rw [hv_pS_sub_left, hv_pS_sub_right, hv_pS_sub_right]
    have hc := hv_pS_comm F.C (Muon.mean P (frozenUpd F S ϱ t)) (frozenUpd F S ϱ t ω)
    linarith
  have hZ : sameTimeZ F S ϱ t ω - sameTimeZc F S ϱ t ω =
      (B : ℝ)⁻¹ * (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
          (Muon.mean P (frozenUpd F S ϱ t)) -
        Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t))) := by
    simp only [sameTimeZ, sameTimeZc, centredUpd]
    rw [hsub]
    ring
  have hS1 := hv_pS_le F.C CSig hO hI (frozenUpd F S ϱ t ω) (Muon.mean P (frozenUpd F S ϱ t))
  have hS2 := hv_pS_le F.C CSig hO hI (Muon.mean P (frozenUpd F S ϱ t))
    (Muon.mean P (frozenUpd F S ϱ t))
  have hgs : fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t)) ≤
      Real.sqrt γstar * Real.sqrt (B : ℝ) * μ :=
    mul_le_mul hXn hSb hs0 (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hss : fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t)) ≤
      μ * μ := mul_le_mul hSb hSb hs0 hμ0
  have hc1 : CSig ^ 2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) ≤
      CSig ^ 2 * (Real.sqrt γstar * Real.sqrt (B : ℝ) * μ) :=
    mul_le_mul_of_nonneg_left hgs (sq_nonneg _)
  have hc2 : CSig ^ 2 * (fro (Muon.mean P (frozenUpd F S ϱ t)) *
      fro (Muon.mean P (frozenUpd F S ϱ t))) ≤ CSig ^ 2 * (μ * μ) :=
    mul_le_mul_of_nonneg_left hss (sq_nonneg _)
  have hpa := abs_sub (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
      (Muon.mean P (frozenUpd F S ϱ t)))
    (Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
      (Muon.mean P (frozenUpd F S ϱ t)))
  rw [abs_mul, abs_two] at hpa
  have hfin : |2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
        (Muon.mean P (frozenUpd F S ϱ t)) -
      Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
        (Muon.mean P (frozenUpd F S ϱ t))| ≤
      CSig ^ 2 * (2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) +
        fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t))) := by
    have e : CSig ^ 2 * (2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t))) +
        fro (Muon.mean P (frozenUpd F S ϱ t)) * fro (Muon.mean P (frozenUpd F S ϱ t))) =
        2 * (CSig ^ 2 * (fro (frozenUpd F S ϱ t ω) * fro (Muon.mean P (frozenUpd F S ϱ t)))) +
        CSig ^ 2 * (fro (Muon.mean P (frozenUpd F S ϱ t)) *
          fro (Muon.mean P (frozenUpd F S ϱ t))) := by ring
    rw [e]
    linarith [hS1, hS2, hpa]
  rw [hZ]
  have hfinal : |(B : ℝ)⁻¹ * (2 * Muon.Setup.pairSigma F.C (frozenUpd F S ϱ t ω)
          (Muon.mean P (frozenUpd F S ϱ t)) -
        Muon.Setup.pairSigma F.C (Muon.mean P (frozenUpd F S ϱ t))
          (Muon.mean P (frozenUpd F S ϱ t)))| ≤
      (B : ℝ)⁻¹ * (CSig ^ 2 * (2 * (Real.sqrt γstar * Real.sqrt (B : ℝ) * μ) + μ * μ)) := by
    rw [abs_mul, abs_of_pos (inv_pos.mpr hB0)]
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hB0.le)
    nlinarith
  refine hfinal.trans ?_
  have hsB : Real.sqrt (B : ℝ) * Real.sqrt (B : ℝ) = (B : ℝ) := Real.mul_self_sqrt hB0.le
  have hsBpos : 0 < Real.sqrt (B : ℝ) := Real.sqrt_pos.mpr hB0
  have hgnn : 0 ≤ Real.sqrt γstar := Real.sqrt_nonneg _
  generalize Real.sqrt (B : ℝ) = s at hsB hsBpos ⊢
  rw [← hsB]
  have e : (s * s)⁻¹ * (CSig ^ 2 * (2 * (Real.sqrt γstar * s * μ) + μ * μ)) =
      CSig ^ 2 * (2 * (Real.sqrt γstar * μ / s) + μ ^ 2 / (s * s)) := by
    field_simp
  rw [e]
  have hnn : 0 ≤ CSig ^ 2 * (Real.sqrt γstar * μ / s) :=
    mul_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg hgnn hμ0) hsBpos.le)
  have e3 : CSig ^ 2 * (4 * Real.sqrt γstar / s * μ + μ ^ 2 / (s * s)) =
      CSig ^ 2 * (2 * (Real.sqrt γstar * μ / s) + μ ^ 2 / (s * s)) +
        2 * (CSig ^ 2 * (Real.sqrt γstar * μ / s)) := by ring
  rw [e3]
  linarith

private lemma hv_fro_add {k l : ℕ} (A D : Mat k l) :
    fro (A + D) ≤ fro A + fro D := by
  open scoped Matrix.Norms.Frobenius in
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]
  exact norm_add_le _ _

private lemma hv_le_biSup {f : ℝ → ℝ} {I : Set ℝ} (hb : BddAbove (f '' I))
    {s : ℝ} (hs : s ∈ I) : f s ≤ ⨆ s ∈ I, f s := by
  obtain ⟨b, hb'⟩ := hb
  have hbdd : BddAbove (Set.range fun s => ⨆ (_ : s ∈ I), f s) := by
    refine ⟨max b 0, ?_⟩
    rintro _ ⟨s', rfl⟩
    show (⨆ (_ : s' ∈ I), f s') ≤ max b 0
    by_cases hs' : s' ∈ I
    · rw [ciSup_pos hs']
      exact le_max_of_le_left (hb' ⟨s', hs', rfl⟩)
    · haveI : IsEmpty (s' ∈ I) := ⟨hs'⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  refine le_ciSup_of_le hbdd s ?_
  rw [ciSup_pos hs]

/-- `thm:app-vol-half-same`, part (iii), centred total, snapshot `cr-2026-10-23`. Declaration of
record for `𝔼 sup_{ϱ∈I} |Z^c(ϱ) − Z̄(ϱ)|² → 0` along a regime with `Σ_in = Id`. LaTeX, verbatim
from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iii_centered {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (Sp : ∀ k, SpectralData (R.F k).C) (hIn : ∀ k, (R.F k).C.Sin = 1) :
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((sameTimeZc (R.F k) (S k) ϱ t ω -
          zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) (Sp k).μ ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun k => Muon.Drift.epsB (emaW R.β) (R.F k) (S k) t
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi
  let a : ℕ → ℝ := fun k => R.CSig / Real.sqrt R.ϱlo + ε k
  let c : ℕ → ℝ := fun k => R.CSig ^ 2 *
    (4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k + (a k) ^ 2 / R.B k)
  have hm := Muon.Drift.thm_app_drift_mean R P S t
  have hmean : ∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) s t)) ≤ a k := by
    intro k s hs
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s) ≤ ε k := hv_le_biSup (hm.2.1 k) hs
    have hg := (hm.1 k s hs).2
    have hsqrt : R.CSig / Real.sqrt s ≤ R.CSig / Real.sqrt R.ϱlo :=
      div_le_div_of_nonneg_left (by linarith [R.hC]) (Real.sqrt_pos.mpr R.hϱ.1)
        (Real.sqrt_le_sqrt hs.1)
    have hadd := hv_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s)
      (Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s =
        Muon.mean (P k) (frozenUpd (R.F k) (S k) s t) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ k]
    rw [heq] at hadd he
    dsimp only [a]
    linarith
  have hcenter : ∀ k ω s, s ∈ Icc R.ϱlo R.ϱhi →
      |sameTimeZ (R.F k) (S k) s t ω - sameTimeZc (R.F k) (S k) s t ω| ≤ c k := by
    intro k ω s hs
    exact hv_centering_at (R.F k) (S k) t R.γstar R.CSig R.ϱlo R.ϱhi (ε k)
      ⟨R.dims k, R.normOut k, R.normIn k⟩ R.hϱ.1 (hmean k) ω s hs
  have hBtop : Tendsto (fun k => (R.B k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hBi : Tendsto (fun k => (R.B k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hBtop
  have hBsi : Tendsto (fun k => (Real.sqrt (R.B k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hBtop)
  have ha : Tendsto a atTop (𝓝 (R.CSig / Real.sqrt R.ϱlo)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hm.2.2.1
  have hc1 : Tendsto (fun k => 4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hBsi).mul ha
  have hc2 : Tendsto (fun k => (a k) ^ 2 / R.B k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (ha.pow 2).mul hBi
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, add_zero, mul_zero] using (hc1.add hc2).const_mul (R.CSig ^ 2)
  have hraw := thm_app_vol_half_same_iii_raw R P S t Sp hIn
  have hl1 := ENNReal.Tendsto.const_mul hraw (a := 2) (Or.inr (by norm_num))
  have hl2 := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (hc.pow 2))
    (a := 2) (Or.inr (by norm_num))
  simp only [zero_pow two_ne_zero, ENNReal.ofReal_zero, mul_zero] at hl1 hl2
  have hlim := hl1.add hl2
  rw [zero_add] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun k => ?_)
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hint : (∫⁻ _ : Ω k, (2 : ℝ≥0∞) * ENNReal.ofReal (c k ^ 2) ∂P k) =
      2 * ENNReal.ofReal (c k ^ 2) := by simp
  rw [← hint, ← lintegral_add_right _ measurable_const]
  apply lintegral_mono
  intro ω
  refine iSup₂_le fun s hs => ?_
  have hb := pow_le_pow_left₀ (abs_nonneg _) (hcenter k ω s hs) 2
  rw [sq_abs] at hb
  have hsq : (sameTimeZc (R.F k) (S k) s t ω -
      zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) (Sp k).μ s) ^ 2 ≤
      2 * (sameTimeZ (R.F k) (S k) s t ω -
        zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) (Sp k).μ s) ^ 2 + 2 * c k ^ 2 := by
    nlinarith [sq_nonneg (2 * sameTimeZ (R.F k) (S k) s t ω - sameTimeZc (R.F k) (S k) s t ω -
      zbarRaw (R.F k).β (R.B k) (Muon.Drift.specOutFM (R.F k))
        (Muon.Drift.specInFM (R.F k)) (Sp k).μ s)]
  refine (ENNReal.ofReal_le_ofReal hsq).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  norm_num only [ENNReal.ofReal_ofNat]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_iSup₂_of_le s hs le_rfl) zero_le) le_rfl

private lemma hv_spectral_props {k B : ℕ} (S : Mat k k) (hS : S.PosSemidef) {CS γ : ℝ}
    (hCS : opNorm S ≤ CS) (hB : 0 < B) (hk : (k : ℝ) ≤ γ * B) :
    ((B : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS)ᶜ = 0 ∧
    ((B : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS)
      ≤ ENNReal.ofReal γ := by
  have habs : ∀ i, |hS.isHermitian.eigenvalues i| ≤ opNorm S := by
    intro i
    have hv := hS.isHermitian.mulVec_eigenvectorBasis i
    have hn : ‖hS.isHermitian.eigenvectorBasis i‖ = 1 :=
      hS.isHermitian.eigenvectorBasis.orthonormal.1 i
    have h1 := Matrix.l2_opNorm_mulVec S (hS.isHermitian.eigenvectorBasis i)
    have h2 : (EuclideanSpace.equiv (Fin k) ℝ).symm (S *ᵥ ⇑(hS.isHermitian.eigenvectorBasis i)) =
        hS.isHermitian.eigenvalues i • hS.isHermitian.eigenvectorBasis i := by
      rw [hv]
      ext
      simp
    rw [h2, norm_smul, hn, Real.norm_eq_abs] at h1
    simp only [mul_one] at h1
    rw [opNorm_eq_norm]
    exact h1
  have hmem : ∀ i, hS.isHermitian.eigenvalues i ∈ Icc (0:ℝ) CS := fun i =>
    ⟨Matrix.PosSemidef.eigenvalues_nonneg hS i,
      (le_abs_self _).trans ((habs i).trans hCS)⟩
  constructor
  · have hz : ∀ i, Measure.dirac (hS.isHermitian.eigenvalues i) (Icc 0 CS)ᶜ = 0 := fun i => by
      rw [Measure.dirac_apply' _ measurableSet_Icc.compl]
      exact Set.indicator_of_notMem (by rw [Set.mem_compl_iff, not_not]; exact hmem i) _
    simp only [Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, hz,
      Finset.sum_const_zero, smul_zero]
  · have h1 : ∀ i, Measure.dirac (hS.isHermitian.eigenvalues i) (Icc 0 CS) = 1 := fun i =>
      Measure.dirac_apply_of_mem (hmem i)
    have hsum : (∑ i, Measure.dirac (hS.isHermitian.eigenvalues i)) (Icc 0 CS) = (k : ℝ≥0∞) := by
      simp only [Measure.coe_finsetSum, Finset.sum_apply, h1, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hBr : (0 : ℝ) < B := by exact_mod_cast hB
    have hconv : (B : ℝ≥0∞)⁻¹ * (k : ℝ≥0∞) = ENNReal.ofReal ((k : ℝ) / B) := by
      rw [ENNReal.ofReal_div_of_pos hBr, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        div_eq_mul_inv, mul_comm]
    rw [Measure.smul_apply, hsum, smul_eq_mul, hconv]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hBr).mpr hk)

private lemma hv_branch_spec (F : FrozenParams m n B) {γ CS ϱ : ℝ}
    (hSize : SizeFin F.C B γ CS) (hϱ : 0 < ϱ) :
    IsBranchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ
      (branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) ϱ) := by
  have hF : AdmissibleWeightFn (Fw (emaW F.β)) := by
    refine Fw_admissible ⟨fun j => ?_, ?_, 0, ?_⟩
    · unfold emaW
      exact mul_nonneg (by linarith [F.hβ.2]) (pow_nonneg F.hβ.1 j)
    · unfold emaW
      exact (summable_geometric_of_lt_one F.hβ.1 F.hβ.2).mul_left _
    · unfold emaW
      rw [pow_zero, mul_one]
      exact (by linarith [F.hβ.2] : (0:ℝ) < 1 - F.β).ne'
  have hd : ((max m n : ℕ) : ℝ) ≤ max γ 1 * B :=
    hSize.1.trans (mul_le_mul_of_nonneg_right (le_max_left γ 1) (Nat.cast_nonneg B))
  obtain ⟨ho1, ho2⟩ := hv_spectral_props F.C.Sout F.C.psdOut
    (hSize.2.1.trans (le_max_left CS 1)) F.hB
    ((Nat.cast_le.mpr (le_max_left m n)).trans hd)
  obtain ⟨hi1, hi2⟩ := hv_spectral_props F.C.Sin F.C.psdIn
    (hSize.2.2.trans (le_max_left CS 1)) F.hB
    ((Nat.cast_le.mpr (le_max_right m n)).trans hd)
  exact branchSol_spec hF (lt_of_lt_of_le one_pos (le_max_right CS 1))
    (lt_of_lt_of_le one_pos (le_max_right γ 1))
    (ν := Muon.Drift.specOutFM F) (ν' := Muon.Drift.specInFM F) ⟨ho2, ho1, hi2, hi1⟩ hϱ

private lemma hv_zin_gram (F : FrozenParams m n B) {γ CS ϱ : ℝ}
    (hSize : SizeFin F.C B γ CS) (hϱ : 0 < ϱ) :
    halfZTotIn F ϱ = (B : ℝ)⁻¹ * (F.C.Sin * halfGramIn F ϱ).trace := by
  have hs := hv_branch_spec F hSize hϱ
  have hc := (hv_branch_nonneg (Fw (emaW F.β)) (Muon.Drift.specOutFM F)
    (Muon.Drift.specInFM F) ϱ).2
  have hσ := hs.2.2.2.2.2.1
  change (branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F)
    (Muon.Drift.specInFM F) ϱ).2.1 = ∫ x, x /
      ((branchSol (Fw (emaW F.β)) (Muon.Drift.specOutFM F)
        (Muon.Drift.specInFM F) ϱ).2.2.2 * x + ϱ) ∂(nuIn F.C B) at hσ
  rw [(def_app_de_branch_trace F.C F.hB hϱ hc).2] at hσ
  unfold halfZTotIn halfGramIn
  rw [hv_gram_eq F.C.Sin F.C.psdIn hc hϱ, Matrix.mul_sub, Matrix.mul_one,
    Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul, hσ]
  rw [add_comm (ϱ • (1 : Mat n n))]
  ring

/-- `thm:app-vol-half-same`, part (iv), finite dimension, mean bound, snapshot `cr-2026-10-23`.
Declaration of record for the output-identity case: under `Σ_out = Id`, `|𝔼Z(ϱ) − (B⁻¹Tr Σ_in −
ϱσ̃(−ϱ))| ≤ γ⋆ C_Σ ϱ₊ ẽ_B`. `halfZTotIn` is the candidate. LaTeX, verbatim from `section.tex`
(the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iv_mean (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (γstar CSig ϱlo ϱhi eBt : ℝ)
    (hSize : SizeFin F.C B γstar CSig) (hOut : F.C.Sout = 1) (hϱ : 0 < ϱlo)
    (heBt : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expResT (emaW F.β) F S t s -
        Rtbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eBt) :
    ∀ ϱ ∈ Icc ϱlo ϱhi,
      |(∫ ω, sameTimeZ F S ϱ t ω ∂P) - halfZTotIn F ϱ| ≤ γstar * CSig * ϱhi * eBt := by
  intro ϱ hϱI
  have hϱ0 := lt_of_lt_of_le hϱ hϱI.1
  let G := fun ω => (frozenUpd F S ϱ t ω)ᵀ * frozenUpd F S ϱ t ω
  have htrace : ∀ X : Mat m n, pairSigma F.C X X = (F.C.Sin * (Xᵀ * X)).trace := by
    intro X
    simp only [pairSigma, hOut, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm X, Matrix.mul_assoc]
  have hmean : (∫ ω, sameTimeZ F S ϱ t ω ∂P) =
      (B : ℝ)⁻¹ * (F.C.Sin * Muon.mean P G).trace := by
    simp only [sameTimeZ, htrace]
    rw [integral_const_mul]
    exact congrArg ((B : ℝ)⁻¹ * ·)
      (hv_int_trace_mul F.C.Sin G (hv_upd_gram_int F S hϱ0 t).2).2
  rw [hmean, hv_zin_gram F hSize hϱ0, ← mul_sub, ← Matrix.trace_sub, ← Matrix.mul_sub]
  have hb := thm_app_vol_half_same_i_in F S t ϱlo ϱhi eBt hϱ heBt ϱ hϱI
  have hd : (n : ℝ) ≤ γstar * B := (Nat.cast_le.mpr (le_max_right m n)).trans hSize.1
  exact (hv_total_trace_bound F.C.Sin (Muon.mean P G - halfGramIn F ϱ)
    F.hB hd hSize.2.2 hb).trans_eq (by ring)

private lemma hv_raw_trace_error_in (R : SetupRegime) {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} (k : ℕ) (S : FrozenSamples P (R.m k) (R.n k) (R.B k))
    (t : ℤ) (hOut : (R.F k).C.Sout = 1) {s : ℝ} (hs : 0 < s) (ω : Ω) :
    sameTimeZ (R.F k) S s t ω - halfZTotIn (R.F k) s =
      -s * ((R.B k : ℝ)⁻¹ * ((R.F k).C.Sin *
        Rts (WeightedBuf (emaW R.β) (R.F k) S t ω) s).trace -
          (branchSol (Fw (emaW R.β)) (Muon.Drift.specOutFM (R.F k))
            (Muon.Drift.specInFM (R.F k)) s).2.1) := by
  have htrace : ∀ X : Mat (R.m k) (R.n k),
      pairSigma (R.F k).C X X = ((R.F k).C.Sin * (Xᵀ * X)).trace := by
    intro X
    simp only [pairSigma, hOut, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm X, Matrix.mul_assoc]
  simp only [sameTimeZ, htrace, frozenUpd]
  rw [hv_Q_gram_in _ hs]
  simp only [halfZTotIn, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul,
    Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  simp only [WeightedBuf, frozenBuf, R.hβ]
  ring

/-- `thm:app-vol-half-same`, part (iv), raw total, snapshot `cr-2026-10-23`. Declaration of record
for `𝔼 sup_{ϱ∈I} |Z(ϱ) − (B⁻¹Tr Σ_in − ϱσ̃(−ϱ))|² → 0` along a regime with `Σ_out = Id`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iv_raw {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (hOut : ∀ k, (R.F k).C.Sout = 1) :
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((sameTimeZ (R.F k) (S k) ϱ t ω - halfZTotIn (R.F k) ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  have htrace := (cor_app_de_trace_iv R (emaW R.β)
    (Muon.Drift.emaW_weightClass_regime R) P S
    (fun k => Muon.Drift.specOutFM (R.F k)) (fun k => Muon.Drift.specInFM (R.F k))
    (fun _ => rfl) (fun _ => rfl) t (Icc R.ϱlo R.ϱhi) isCompact_Icc
    (fun _ hs => lt_of_lt_of_le R.hϱ.1 hs.1)).2
  have hlim := ENNReal.Tendsto.const_mul htrace
    (a := ENNReal.ofReal (R.ϱhi ^ 2)) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun k => ?_)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro ω
  refine iSup₂_le fun s hs => ?_
  rw [hv_raw_trace_error_in R k (S k) t (hOut k)
    (lt_of_lt_of_le R.hϱ.1 hs.1) ω]
  have hs2 : s ^ 2 ≤ R.ϱhi ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (lt_of_lt_of_le R.hϱ.1 hs.1)) hs.2 2
  simp only [mul_pow, neg_sq, Real.norm_eq_abs, sq_abs] at *
  calc ENNReal.ofReal (s ^ 2 * _ ^ 2)
      ≤ ENNReal.ofReal (R.ϱhi ^ 2 * _ ^ 2) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hs2 (sq_nonneg _))
    _ = ENNReal.ofReal (R.ϱhi ^ 2) * ENNReal.ofReal (_ ^ 2) :=
        ENNReal.ofReal_mul (sq_nonneg _)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_iSup₂_of_le s hs le_rfl) zero_le

/-- `thm:app-vol-half-same`, part (iv), centred total, snapshot `cr-2026-10-23`. Declaration of
record for `𝔼 sup_{ϱ∈I} |Z^c(ϱ) − (B⁻¹Tr Σ_in − ϱσ̃(−ϱ))|² → 0` along a regime with `Σ_out = Id`.
LaTeX, verbatim from `section.tex` (the whole environment):

```latex
\begin{theorem}[Same-time energies of rows and columns]\label{thm:app-vol-half-same}
Assume \cref{assum:app-setup-regime}, let $I=[\ridge_-,\ridge_+]$, and put
\[
e_B\defeq\sup_{s\in I}\norm{\EE R(-s)-\Rbar(-s)},\qquad
\tilde e_B\defeq\sup_{s\in I}\norm{\EE\widetilde R(-s)-\Rtbar(-s)},
\]
which tend to zero by \cref{thm:app-de-gram}.
\begin{enumerate}[label=(\roman*)]
\item The expected update Gram matrices satisfy
\begin{equation}\label{eqn:app-vol-half-gram}
\begin{gathered}
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge){\mathsf S}_t(\ridge)^\T\big]-\tilde s_1(-\ridge)\Sigmaout\big(\tilde s_1(-\ridge)\Sigmaout+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,e_B ,\\
\sup_{\ridge\in I}\Big\|\EE\big[{\mathsf S}_t(\ridge)^\T{\mathsf S}_t(\ridge)\big]-s_1(-\ridge)\Sigmain\big(s_1(-\ridge)\Sigmain+\ridge\Id\big)^{-1}\Big\|\le\ridge_+\,\tilde e_B .
\end{gathered}
\end{equation}
\item The expected row and column energies satisfy
\begin{equation}\label{eqn:app-vol-half-rows}
\sup_{\ridge\in I}\max_{1\le i\le\Nout}\Big|\EE\norm{{\mathsf S}_t(\ridge)^\T u_i}^2-\volraw_i(\ridge)\Big|\le\ridge_+\,e_B ,\qquad
\sup_{\ridge\in I}\max_{1\le j\le\Nin}\Big|\EE\norm{{\mathsf S}_t(\ridge)v_j}^2-\widetilde{\mathfrak v}^{(0)}_j(\ridge)\Big|\le\ridge_+\,\tilde e_B ,
\end{equation}
${\mathsf S}_t(\ridge)^\T u_i=0$ for every $i$ with $\mu_i=0$, and ${\mathsf S}_t(\ridge)v_j=0$ for every
$j$ with $\lambda_j=0$.
\item If $\Sigmain=\Id_{\Nin}$, the raw and centered totals \cref{eqn:app-vol-Z} satisfy
\begin{equation}\label{eqn:app-vol-half-total}
\EE\sup_{\ridge\in I}\abs{Z(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,\qquad
\EE\sup_{\ridge\in I}\abs{Z^{\mathrm c}(\ridge)-\overline Z(\ridge)}^2\longrightarrow0,
\end{equation}
and $\sup_{\ridge\in I}\abs{\EE Z(\ridge)-\overline Z(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B$.
\item If $\Sigmaout=\Id_{\Nout}$, (iii) holds with the candidate $\overline Z$
replaced by $B^{-1}\Tr\Sigmain-\ridge\,\tilde\sigma(-\ridge)$ and $e_B$ by $\tilde e_B$.
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_vol_half_same_iv_centered {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (R : SetupRegime) (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (hOut : ∀ k, (R.F k).C.Sout = 1) :
    Tendsto (fun k => ∫⁻ ω, ⨆ ϱ ∈ Icc R.ϱlo R.ϱhi,
        ENNReal.ofReal ((sameTimeZc (R.F k) (S k) ϱ t ω - halfZTotIn (R.F k) ϱ) ^ 2) ∂(P k))
      atTop (𝓝 0) := by
  let ε : ℕ → ℝ := fun k => Muon.Drift.epsB (emaW R.β) (R.F k) (S k) t
    (Muon.Drift.specOutFM (R.F k)) (Muon.Drift.specInFM (R.F k)) R.ϱlo R.ϱhi
  let a : ℕ → ℝ := fun k => R.CSig / Real.sqrt R.ϱlo + ε k
  let c : ℕ → ℝ := fun k => R.CSig ^ 2 *
    (4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k + (a k) ^ 2 / R.B k)
  have hm := Muon.Drift.thm_app_drift_mean R P S t
  have hmean : ∀ k, ∀ s ∈ Icc R.ϱlo R.ϱhi,
      fro (Muon.mean (P k) (frozenUpd (R.F k) (S k) s t)) ≤ a k := by
    intro k s hs
    have he : fro (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s) ≤ ε k := hv_le_biSup (hm.2.1 k) hs
    have hg := (hm.1 k s hs).2
    have hsqrt : R.CSig / Real.sqrt s ≤ R.CSig / Real.sqrt R.ϱlo :=
      div_le_div_of_nonneg_left (by linarith [R.hC]) (Real.sqrt_pos.mpr R.hϱ.1)
        (Real.sqrt_le_sqrt hs.1)
    have hadd := hv_fro_add
      (Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s -
        Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s)
      (Muon.Drift.Gbar (emaW R.β) (R.F k) (Muon.Drift.specOutFM (R.F k))
          (Muon.Drift.specInFM (R.F k)) s)
    rw [sub_add_cancel] at hadd
    have heq : Muon.Drift.EQ (emaW R.β) (R.F k) (S k) t s =
        Muon.mean (P k) (frozenUpd (R.F k) (S k) s t) := by
      unfold Muon.Drift.EQ
      congr 1
      funext ω
      unfold frozenUpd WeightedBuf frozenBuf
      rw [R.hβ k]
    rw [heq] at hadd he
    dsimp only [a]
    linarith
  have hcenter : ∀ k ω s, s ∈ Icc R.ϱlo R.ϱhi →
      |sameTimeZ (R.F k) (S k) s t ω - sameTimeZc (R.F k) (S k) s t ω| ≤ c k := by
    intro k ω s hs
    exact hv_centering_at (R.F k) (S k) t R.γstar R.CSig R.ϱlo R.ϱhi (ε k)
      ⟨R.dims k, R.normOut k, R.normIn k⟩ R.hϱ.1 (hmean k) ω s hs
  have hBtop : Tendsto (fun k => (R.B k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp R.prop.B_top
  have hBi : Tendsto (fun k => (R.B k : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hBtop
  have hBsi : Tendsto (fun k => (Real.sqrt (R.B k : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hBtop)
  have ha : Tendsto a atTop (𝓝 (R.CSig / Real.sqrt R.ϱlo)) := by
    simpa only [add_zero] using tendsto_const_nhds.add hm.2.2.1
  have hc1 : Tendsto (fun k => 4 * Real.sqrt R.γstar / Real.sqrt (R.B k) * a k)
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, zero_mul] using
      (tendsto_const_nhds.mul hBsi).mul ha
  have hc2 : Tendsto (fun k => (a k) ^ 2 / R.B k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using (ha.pow 2).mul hBi
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c, add_zero, mul_zero] using (hc1.add hc2).const_mul (R.CSig ^ 2)
  have hraw := thm_app_vol_half_same_iv_raw R P S t hOut
  have hl1 := ENNReal.Tendsto.const_mul hraw (a := 2) (Or.inr (by norm_num))
  have hl2 := ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal (hc.pow 2))
    (a := 2) (Or.inr (by norm_num))
  simp only [zero_pow two_ne_zero, ENNReal.ofReal_zero, mul_zero] at hl1 hl2
  have hlim := hl1.add hl2
  rw [zero_add] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) (Eventually.of_forall fun k => ?_)
  rw [← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  have hint : (∫⁻ _ : Ω k, (2 : ℝ≥0∞) * ENNReal.ofReal (c k ^ 2) ∂P k) =
      2 * ENNReal.ofReal (c k ^ 2) := by simp
  rw [← hint, ← lintegral_add_right _ measurable_const]
  apply lintegral_mono
  intro ω
  refine iSup₂_le fun s hs => ?_
  have hb := pow_le_pow_left₀ (abs_nonneg _) (hcenter k ω s hs) 2
  rw [sq_abs] at hb
  have hsq : (sameTimeZc (R.F k) (S k) s t ω -
      halfZTotIn (R.F k) s) ^ 2 ≤
      2 * (sameTimeZ (R.F k) (S k) s t ω -
        halfZTotIn (R.F k) s) ^ 2 + 2 * c k ^ 2 := by
    nlinarith [sq_nonneg (2 * sameTimeZ (R.F k) (S k) s t ω - sameTimeZc (R.F k) (S k) s t ω -
      halfZTotIn (R.F k) s)]
  refine (ENNReal.ofReal_le_ofReal hsq).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
  norm_num only [ENNReal.ofReal_ofNat]
  exact add_le_add (mul_le_mul_of_nonneg_left (le_iSup₂_of_le s hs le_rfl) zero_le) le_rfl

/-! ## Non-label helpers: `eqn:app-vol-half-identity` and `eqn:app-vol-half-onestep` -/

/-- Exact identity `eqn:app-vol-half-identity` (used in the proof of `thm:app-vol-half-same`), for
`ϱ > 0`: `Q_ϱ(K)Q_ϱ(K)^⊤ = K K^⊤(K K^⊤+ϱ)^{-1} = Id − ϱ R_ϱ(K)` and `Q_ϱ(K)^⊤Q_ϱ(K) = Id −
ϱ R̃_ϱ(K)`, with `R_ϱ(K) = (KK^⊤+ϱ)^{-1}` (`Rs`) and `R̃_ϱ(K) = (K^⊤K+ϱ)^{-1}` (`Rts`).
Snapshot `cr-2026-10-23`. LaTeX, verbatim from `section.tex` (the display):

```latex
\begin{equation}\label{eqn:app-vol-half-identity}
\Qridge\ridge(K)\Qridge\ridge(K)^\T=KK^\T\big(KK^\T+\ridge\Id\big)^{-1}=\Id-\ridge\,R_\ridge(K),\qquad
\Qridge\ridge(K)^\T\Qridge\ridge(K)=\Id-\ridge\,\widetilde R_\ridge(K).
\end{equation}
```
-/
theorem half_identity {m n : ℕ} (K : Mat m n) {ϱ : ℝ} (hϱ : 0 < ϱ) :
    Muon.Q ϱ K * (Muon.Q ϱ K)ᵀ = K * Kᵀ * (K * Kᵀ + ϱ • (1 : Mat m m))⁻¹ ∧
      Muon.Q ϱ K * (Muon.Q ϱ K)ᵀ = (1 : Mat m m) - ϱ • Rs K ϱ ∧
      (Muon.Q ϱ K)ᵀ * Muon.Q ϱ K = (1 : Mat n n) - ϱ • Rts K ϱ := by
  refine ⟨?_, hv_Q_gram_out K hϱ, hv_Q_gram_in K hϱ⟩
  rw [hv_Q_gram_out K hϱ]
  have hu := (Matrix.isUnit_iff_isUnit_det _).mp (hv_unit_KKt K hϱ)
  have hmul := Matrix.mul_nonsing_inv (K * Kᵀ + ϱ • (1 : Mat m m)) hu
  have hsplit : K * Kᵀ = (K * Kᵀ + ϱ • (1 : Mat m m)) - ϱ • 1 := by abel
  nth_rw 1 [hsplit]
  rw [Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hmul]
  rfl

/-- Frozen one-step quadratic term `eqn:app-vol-half-onestep`, snapshot `cr-2026-10-23`. For
`Σ_in = Id` and `ϱ ∈ I`, the quadratic term of the one-step identity equals
`(lr²B/2)(Z̄(ϱ) + r_B(ϱ))` with `|r_B(ϱ)| ≤ γ⋆ C_Σ ϱ₊ e_B`. Here the left side is the expected
quadratic term `(lr²/2) 𝔼‖S_t(ϱ)‖_Σ²` written directly (with `pairSigma = B·Z`); `r_B` is the
remainder, so the existential form is the paper's definition of `r_B`. LaTeX, verbatim from
`section.tex` (the display):

```latex
\begin{equation}\label{eqn:app-vol-half-onestep}
\frac{\lr^2}{2}\,\EE\norm{\Qridge\ridge(\Mt)}_\Sigma^2=\frac{\lr^2B}{2}\Big(\overline Z(\ridge)+r_B(\ridge)\Big),\qquad
\sup_{\ridge\in I}\abs{r_B(\ridge)}\le\gamma_\star C_\Sigma\ridge_+e_B .
\end{equation}
```
-/
theorem half_onestep (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (Sp : SpectralData F.C) (lr γstar CSig ϱlo ϱhi eB : ℝ)
    (hSize : SizeFin F.C B γstar CSig) (hIn : F.C.Sin = 1) (hϱ : 0 < ϱlo)
    (heB : ∀ s ∈ Icc ϱlo ϱhi,
      opNorm (expRes (emaW F.β) F S t s -
        Rbar (Fw (emaW F.β)) (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) F.C s) ≤ eB) :
    ∀ ϱ ∈ Icc ϱlo ϱhi, ∃ r : ℝ,
      lr ^ 2 / 2 * (∫ ω, pairSigma F.C (frozenUpd F S ϱ t ω) (frozenUpd F S ϱ t ω) ∂P) =
        lr ^ 2 * (B : ℝ) / 2 *
          (zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) Sp.μ ϱ + r) ∧
      |r| ≤ γstar * CSig * ϱhi * eB := by
  intro ϱ hϱI
  refine ⟨(∫ ω, sameTimeZ F S ϱ t ω ∂P) -
    zbarRaw F.β B (Muon.Drift.specOutFM F) (Muon.Drift.specInFM F) Sp.μ ϱ, ?_,
    thm_app_vol_half_same_iii_mean F S t Sp γstar CSig ϱlo ϱhi eB
      hSize hIn hϱ heB ϱ hϱI⟩
  rw [add_sub_cancel]
  simp only [sameTimeZ, integral_const_mul]
  have hB : (B : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt F.hB)
  field_simp


end Muon.Volatility
