import Muon.Setup.Frozen
import Muon.Setup.Weights
import Muon.Setup.RegularizedMap
import Muon.Foundations.Probability

/-!
# History truncation and sample sensitivity (Appendix A)

Source: `sections/01-setup/section.tex`, snapshot `cr-2026-10-23`: `lem:app-setup-truncation`
(l.868–886). Card: `sections/01-setup/CARD.md` §5, work package L-A.8. Consumers: B–E.

Conventions (all objects of the frozen model are reused from `Muon.Setup.Frozen`):
* The paper's `\Gt` is `G_{t+1}`, i.e. `frozenBatchG F S (t + 1)`; `\Mt` is `frozenBuf F S t`.
* `truncBuf F S t J` is the truncated buffer `M^{(J)} = ∑_{j=0}^J w_j G_{t+1-j}` (a finite sum).
* Part (iii) takes an independent copy of the whole sample family as the hypothesis `IndepCopy S`
  (card §5; the L-A.7 review ruled that conditioning on `ℱ_t` is not encoded). The copy is jointly
  independent of `S` on the same `Ω`. `copySamples S C s a` is the family with the single sample
  `(z_{sa}, w_{sa})` replaced by its copy, by `Function.update`; `bufOf F (copySamples S C (t+1-j) a) t`
  is `M_t^{[ja]}`.
* `batchOf` and `bufOf` are the batch and buffer formulas of `frozenBatchG`/`frozenBuf` for an
  arbitrary sample array. `batchOf_zw_eq` and `bufOf_zw_eq` show they agree with the frozen objects.
  They exist because a modified sample array has no `FrozenSamples` structure without unproved
  independence fields.
* Where the paper's expectation is an `∫` of a function that must be `L²` or `L¹` for the value to be
  meaningful, that square-integrability is stated as an explicit conjunct: Lean's Bochner integral and
  `variance` are junk values off `L¹`/`L²`.
* The Efron–Stein inequality (part (iii)) is `Muon.Foundations.efron_stein`; it is used only in proofs.
* The global hypothesis `0 < ϱ` of the lemma is carried by every part.
-/

noncomputable section

open scoped Matrix MatrixOrder
open MeasureTheory ProbabilityTheory Filter Topology
open Muon

namespace Muon.Setup

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}

/-- Independent copy of the frozen sample family (hypothesis of `lem:app-setup-truncation`(iii)).
`zw'` has the law of `S.zw` sample by sample, and the families `S.zw` and `zw'` are jointly
independent on `(Ω, P)`. Card §5: the copy is a hypothesis because conditioning on `ℱ_t` is not
encoded in the frozen model. -/
structure IndepCopy (S : FrozenSamples P m n B) where
  zw' : ℤ → Fin B → Ω → Vec m × Vec n
  meas : ∀ s a, Measurable (zw' s a)
  law : ∀ s a,
    P.map (zw' s a) = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)
  indep : iIndepFun
    (fun p : Bool × (ℤ × Fin B) =>
      (if p.1 then zw' p.2.1 p.2.2 else S.zw p.2.1 p.2.2 : Ω → Vec m × Vec n)) P

/-- Frozen batch `G_s` for an arbitrary sample array `z` (the formula of `frozenBatchG`). -/
def batchOf (F : FrozenParams m n B) (z : ℤ → Fin B → Ω → Vec m × Vec n) (s : ℤ) (ω : Ω) :
    Mat m n :=
  ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (z s a ω).1 (Matrix.mulVec F.A (z s a ω).2)) •
      (rOut F.C * outer (z s a ω).1 (z s a ω).2 * rIn F.C)

/-- Frozen buffer `∑_{j ≥ 0} w_j G_{t+1-j}` for an arbitrary sample array `z` (the formula of
`frozenBuf`). -/
def bufOf (F : FrozenParams m n B) (z : ℤ → Fin B → Ω → Vec m × Vec n) (t : ℤ) (ω : Ω) :
    Mat m n :=
  ∑' j : ℕ, emaW F.β j • batchOf F z (t + 1 - (j : ℤ)) ω

/-- The sample family of `S` with the single pair `(z_{sa}, w_{sa})` replaced by the independent
copy `zw'_{sa}` (`M_t^{[ja]}` with `s = t + 1 - j`, `a` the slot). -/
def copySamples (S : FrozenSamples P m n B) (C : IndepCopy S) (s : ℤ) (a : Fin B) :
    ℤ → Fin B → Ω → Vec m × Vec n :=
  Function.update S.zw s (Function.update (S.zw s) a (C.zw' s a))

/-- Truncated buffer `M^{(J)}_t = ∑_{j=0}^J w_j G_{t+1-j}` (`lem:app-setup-truncation`). -/
def truncBuf (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) (ω : Ω) :
    Mat m n :=
  ∑ j ∈ Finset.range (J + 1), emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω

/-- Bridge: `batchOf` at the frozen family is `frozenBatchG` (definitional). -/
theorem batchOf_zw_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    batchOf F S.zw s ω = frozenBatchG F S s ω := rfl

/-- Bridge: `bufOf` at the frozen family is `frozenBuf` (definitional). -/
theorem bufOf_zw_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (ω : Ω) :
    bufOf F S.zw t ω = frozenBuf F S t ω := rfl


/-! ### Auxiliary lemmas for parts (ii) and (i) -/

private lemma fro_sq_Q_le {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) (K L : Mat m n) :
    fro (Q ϱ K - Q ϱ L) ^ 2 ≤ ϱ⁻¹ * fro (K - L) ^ 2 := by
  have h := lem_app_setup_filter_iii ϱ hϱ K L
  have hsq : (ϱ ^ (-(1 / 2 : ℝ))) ^ 2 = ϱ⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hϱ.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hnn : 0 ≤ fro (Q ϱ K - Q ϱ L) := Real.sqrt_nonneg _
  have := pow_le_pow_left₀ hnn h 2
  rw [mul_pow, hsq] at this
  exact this

private lemma abs_entry_le_fro {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
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

private lemma summable_mat_of_fro {m n : ℕ} {ι : Type*} (f : ι → Mat m n)
    (hf : Summable fun j => fro (f j)) : Summable f := by
  refine (Pi.summable).2 fun i => (Pi.summable).2 fun k => ?_
  refine Summable.of_norm_bounded hf (fun j => ?_)
  rw [Real.norm_eq_abs]
  exact abs_entry_le_fro (f j) i k

private lemma summand_cont {m n B : ℕ} (F : FrozenParams m n B) :
    Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
  fun_prop

private lemma frozenBatchG_sm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    StronglyMeasurable (frozenBatchG F S s) := by
  unfold frozenBatchG
  refine StronglyMeasurable.const_smul ?_ ((B : ℝ))⁻¹
  exact Finset.stronglyMeasurable_fun_sum Finset.univ fun a _ =>
    (summand_cont F).comp_stronglyMeasurable (S.meas s a).stronglyMeasurable

private instance instPseudoMetrizableMat {m n : ℕ} :
    TopologicalSpace.PseudoMetrizableSpace (Mat m n) :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin m → Fin n → ℝ))

private instance instSecondCountableMat {m n : ℕ} : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma truncBuf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    AEStronglyMeasurable (truncBuf F S t J) P := by
  unfold truncBuf
  exact (Finset.stronglyMeasurable_fun_sum (Finset.range (J + 1)) fun j _ =>
    (frozenBatchG_sm F S (t + 1 - (j : ℤ))).const_smul (emaW F.β j)).aestronglyMeasurable

private lemma frozenBuf_aesm {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {m n B : ℕ}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) :
    AEStronglyMeasurable (frozenBuf F S t) P := by
  have hae := (lem_app_setup_ema_law_i F S).1
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun N ω =>
    ∑ j ∈ Finset.range N, emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) (fun N => ?_) ?_
  · exact (Finset.stronglyMeasurable_fun_sum (Finset.range N) fun j _ =>
      (frozenBatchG_sm F S (t + 1 - (j : ℤ))).const_smul (emaW F.β j)).aestronglyMeasurable
  · filter_upwards [hae] with ω hω
    have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      summable_mat_of_fro _ (hω t)
    exact hs.hasSum.tendsto_sum_nat

private lemma Q_measurable_fn {m n : ℕ} (ϱ : ℝ) (hϱ : 0 < ϱ) :
    Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ.le⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma memLp_of_covT_ne {X : Ω → Mat m n} [IsProbabilityMeasure P]
    (hX : ∀ i j, Measurable (fun ω => X ω i j)) (i : Fin m) (j : Fin n)
    (h : covT P X i j i j ≠ 0) : MemLp (fun ω => X ω i j) 2 P := by
  by_contra hn
  apply h
  unfold covT
  rw [covariance_self (hX i j).aemeasurable]
  exact variance_of_not_memLp (hX i j).aestronglyMeasurable hn

private lemma sampleTensor_diag_pos (A : Mat m n) (i : Fin m) (j : Fin n) :
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

private lemma sampleX_entry_memLp [IsProbabilityMeasure P] {Z : Ω → Vec m} {W : Ω → Vec n}
    (hZ : Measurable Z) (hW : Measurable W)
    (hZW : P.map (fun ω => (Z ω, W ω)) = (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n))
    (A : Mat m n) (hA : fro A = 1) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => sampleX A (Z ω) (W ω) i j) 2 P := by
  refine memLp_of_covT_ne (X := fun ω => sampleX A (Z ω) (W ω)) ?_ i j ?_
  · intro i j
    unfold sampleX
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, dotProduct, Matrix.mulVec]
    fun_prop
  · rw [lem_app_setup_gaussian_moments_ii hZW A hA]
    exact sampleTensor_diag_pos A i j


private lemma frozenBatchG_entry (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ)
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

private lemma frozenBatchG_entry_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (s : ℤ) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => frozenBatchG F S s ω i j) 2 P := by
  have : (fun ω => frozenBatchG F S s ω i j) = fun ω => (B : ℝ)⁻¹ * ∑ a : Fin B, ∑ p : Fin m,
      ∑ q : Fin n, (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q := by
    funext ω; exact frozenBatchG_entry F S s ω i j
  rw [this]
  have h1 : ∀ a : Fin B, ∀ p : Fin m, ∀ q : Fin n, MemLp (fun ω => (rOut F.C i p * rIn F.C q j) *
        sampleX F.A (S.zw s a ω).1 (S.zw s a ω).2 p q) 2 P := fun a p q =>
    MemLp.const_mul (sampleX_entry_memLp (Z := fun ω => (S.zw s a ω).1)
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


private lemma abs_entry_le_fro' {m n : ℕ} (K : Mat m n) (i : Fin m) (j : Fin n) :
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

private lemma fro_sq_eq {m n : ℕ} (K : Mat m n) : fro K ^ 2 = ∑ i, ∑ j, K i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma continuous_fro_sq {m n : ℕ} : Continuous (fun K : Mat m n => fro K ^ 2) := by
  simp_rw [fro_sq_eq]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    (Continuous.matrix_elem continuous_id i j).pow 2

private lemma integrable_fro_sq_of_memLp {Y : Ω → Mat m n}
    (h : ∀ i j, MemLp (fun ω => Y ω i j) 2 P) :
    Integrable (fun ω => fro (Y ω) ^ 2) P := by
  simp_rw [fro_sq_eq]
  exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (h i j).integrable_sq

private lemma memLp_entry_of_fro {Y : Ω → Mat m n}
    (hY : ∀ i j, AEStronglyMeasurable (fun ω => Y ω i j) P)
    (h : Integrable (fun ω => fro (Y ω) ^ 2) P) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => Y ω i j) 2 P := by
  rw [memLp_two_iff_integrable_sq (hY i j)]
  refine h.mono' ((hY i j).pow 2) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have := pow_le_pow_left₀ (abs_nonneg (Y ω i j)) (abs_entry_le_fro' (Y ω) i j) 2
  rwa [sq_abs] at this

private lemma young_sq (a b ε : ℝ) (hε : 0 < ε) :
    a ^ 2 ≤ (1 + ε) * b ^ 2 + (1 + ε⁻¹) * (a - b) ^ 2 := by
  have h := mul_nonneg (inv_nonneg.2 hε.le) (sq_nonneg (ε * b - (a - b)))
  have e : ε⁻¹ * (ε * b - (a - b)) ^ 2 = ε * b ^ 2 - 2 * b * (a - b) + ε⁻¹ * (a - b) ^ 2 := by
    field_simp
    ring
  nlinarith [h, e]


private lemma young_fro {m n : ℕ} (K L : Mat m n) (ε : ℝ) (hε : 0 < ε) :
    fro K ^ 2 ≤ (1 + ε) * fro L ^ 2 + (1 + ε⁻¹) * fro (K - L) ^ 2 := by
  simp only [fro_sq_eq, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
  have := young_sq (K i j) (L i j) ε hε
  simpa [Matrix.sub_apply] using this

private lemma fro_sub_comm_sq {m n : ℕ} (K L : Mat m n) : fro (K - L) ^ 2 = fro (L - K) ^ 2 := by
  simp only [fro_sq_eq, Matrix.sub_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma le_of_forall_mul {a b : ℝ} (hb : 0 ≤ b) (h : ∀ ε : ℝ, 0 < ε → a ≤ (1 + ε) * b) :
    a ≤ b := by
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have h1 := h (δ / (b + 1)) (by positivity)
  have h2 : δ / (b + 1) * b ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

private lemma sq_integral_le_of_memLp [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : MemLp f 2 P) :
    (∫ ω, f ω ∂P) ^ 2 ≤ ∫ ω, f ω ^ 2 ∂P := by
  have h1 := variance_eq_sub hf
  have h2 := variance_nonneg f P
  simp only [Pi.pow_apply] at h1
  nlinarith

private lemma mean_batch_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    mean P (frozenBatchG F S s) = mean P (frozenBatchG F S 0) := by
  rw [(lem_app_setup_gaussian_moments_iv F S s).1, (lem_app_setup_gaussian_moments_iv F S 0).1]


private lemma l2_limit [IsProbabilityMeasure P] (X : ℕ → Ω → Mat m n) (D : Ω → Mat m n)
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
      fun N' => ((integrable_fro_sq_of_memLp (hdiffL N N')).aestronglyMeasurable.aemeasurable).ennreal_ofReal
    have hfat := lintegral_liminf_le' (u := atTop) (f := fun N' ω => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) hmeas
    have hlim : ∀ᵐ ω ∂P, Filter.liminf (fun N' => ENNReal.ofReal (fro (X N' ω - X N ω) ^ 2)) atTop
        = ENNReal.ofReal (fro (D ω - X N ω) ^ 2) := by
      filter_upwards [hconv] with ω hω
      refine Filter.Tendsto.liminf_eq ?_
      exact ENNReal.tendsto_ofReal
        ((continuous_fro_sq.tendsto _).comp (hω.sub_const (X N ω)))
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
              (integrable_fro_sq_of_memLp (hdiffL N N'))
              (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (hc N N' hN')
    have hint : Integrable (fun ω => fro (D ω - X N ω) ^ 2) P := by
      refine ⟨?_, ?_⟩
      · have : AEStronglyMeasurable (fun ω => fro (D ω - X N ω) ^ 2) P := by
          simp_rw [fro_sq_eq]
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
  have h := memLp_entry_of_fro (fun i j => hDX 0 i j) (key 0).1 i j
  have := h.add (hX 0 i j)
  exact this.ae_eq (Filter.Eventually.of_forall fun ω => by simp)



private lemma young_int {U V' : Ω → Mat m n}
    (hU : Integrable (fun ω => fro (U ω) ^ 2) P) (hV : Integrable (fun ω => fro (V' ω) ^ 2) P)
    (hd : Integrable (fun ω => fro (U ω - V' ω) ^ 2) P) (ε : ℝ) (hε : 0 < ε) :
    ∫ ω, fro (U ω) ^ 2 ∂P ≤ (1 + ε) * ∫ ω, fro (V' ω) ^ 2 ∂P
      + (1 + ε⁻¹) * ∫ ω, fro (U ω - V' ω) ^ 2 ∂P := by
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hV.const_mul _) (hd.const_mul _)]
  exact integral_mono hU ((hV.const_mul _).add (hd.const_mul _)) fun ω => young_fro _ _ ε hε

private lemma truncation_i_core [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    Integrable (fun ω => fro (frozenBuf F S t ω - truncBuf F S t J ω) ^ 2) P ∧
      mean P (fun ω => frozenBuf F S t ω - truncBuf F S t J ω)
        = (F.β ^ (J + 1)) • mean P (frozenBatchG F S (t + 1)) ∧
      ∫ ω, (fro (frozenBuf F S t ω - truncBuf F S t J ω)) ^ 2 ∂P
        = F.β ^ (2 * (J + 1)) *
            (fro (mean P (frozenBatchG F S (t + 1))) ^ 2 + sPow F.β 2 * frozenVB S F) := by
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  have hGint : ∀ s i j, Integrable (fun ω => frozenBatchG F S s ω i j) P := fun s i j =>
    (frozenBatchG_entry_memLp F S s i j).integrable one_le_two
  have hGmean : ∀ s i j, ∫ ω, frozenBatchG F S s ω i j ∂P = mean P (frozenBatchG F S 0) i j := by
    intro s i j
    have := congrFun (congrFun (mean_batch_eq F S s) i) j
    simpa [mean] using this
  set μ := mean P (frozenBatchG F S 0) with hμdef
  set V := frozenVB S F with hVdef
  have hV0 : 0 ≤ V := integral_nonneg fun ω => sq_nonneg _
  set Y : ℕ → Ω → Mat m n := fun j ω =>
    emaW F.β j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ) with hYdef
  set X : ℕ → Ω → Mat m n := fun N ω => ∑ k ∈ Finset.range N, Y (k + (J + 1)) ω with hXdef
  set D : Ω → Mat m n := fun ω => frozenBuf F S t ω - truncBuf F S t J ω - F.β ^ (J + 1) • μ
    with hDdef
  have hYe : ∀ j ω i k, Y j ω i k = emaW F.β j * (frozenBatchG F S (t + 1 - (j : ℤ)) ω i k - μ i k) := by
    intro j ω i k
    simp [hYdef, Matrix.smul_apply, Matrix.sub_apply]
  have hYL : ∀ j i k, MemLp (fun ω => Y j ω i k) 2 P := by
    intro j i k
    have : (fun ω => Y j ω i k) = fun ω => emaW F.β j *
        (frozenBatchG F S (t + 1 - (j : ℤ)) ω i k - μ i k) := funext fun ω => hYe j ω i k
    rw [this]
    exact ((frozenBatchG_entry_memLp F S _ i k).sub (memLp_const _)).const_mul _
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
  have hw2s : Summable (fun j : ℕ => emaW F.β j ^ 2) := by
    have h := (summable_geometric_of_lt_one (sq_nonneg F.β)
      (by nlinarith : F.β ^ 2 < 1)).mul_left ((1 - F.β) ^ 2)
    refine h.congr (fun j => ?_)
    simp only [emaW]
    ring
  -- orthogonality in the shifted indexing
  have hdiff : ∀ N N' ω, N < N' → X N' ω - X N ω = ∑ j ∈ Finset.Icc (N + (J + 1)) (N' + J),
      emaW F.β j • (frozenBatchG F S (t + 1 - (j : ℤ)) ω - μ) := by
    intro N N' ω hN
    have h1 : X N' ω - X N ω = ∑ r ∈ Finset.Ico N N', Y (r + (J + 1)) ω := by
      rw [Finset.sum_Ico_eq_sub _ hN.le]
    have h2 : Finset.Ico (N + (J + 1)) (N' + (J + 1)) = Finset.Icc (N + (J + 1)) (N' + J) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [h1, Finset.sum_Ico_add' (fun j => Y j ω) N N' (J + 1), h2]
  have hsqIco : ∀ N N', N < N' → ∑ j ∈ Finset.Icc (N + (J + 1)) (N' + J), emaW F.β j ^ 2
      = ∑ r ∈ Finset.Ico N N', emaW F.β (r + (J + 1)) ^ 2 := by
    intro N N' hN
    have h2 : Finset.Ico (N + (J + 1)) (N' + (J + 1)) = Finset.Icc (N + (J + 1)) (N' + J) := by
      ext x; simp only [Finset.mem_Ico, Finset.mem_Icc]; omega
    rw [← h2, Finset.sum_Ico_add' (fun j => emaW F.β j ^ 2) N N' (J + 1)]
  have horth : ∀ N N', N ≤ N' → ∫ ω, fro (X N' ω - X N ω) ^ 2 ∂P
      = V * ∑ r ∈ Finset.Ico N N', emaW F.β (r + (J + 1)) ^ 2 := by
    intro N N' hN
    rcases hN.lt_or_eq with hlt | rfl
    · have := eqn_app_setup_orthogonality F S t (k := N + (J + 1)) (l := N' + J) (by omega)
      simp_rw [hdiff N N' _ hlt]
      rw [this, hsqIco N N' hlt]
    · simp [fro]
  set c : ℕ → ℝ := fun N => V * ∑' k, emaW F.β (k + (N + (J + 1))) ^ 2 with hcdef
  have hc : ∀ N N', N ≤ N' → ∫ ω, fro (X N' ω - X N ω) ^ 2 ∂P ≤ c N := by
    intro N N' hN
    rw [horth N N' hN]
    refine mul_le_mul_of_nonneg_left ?_ hV0
    rw [Finset.sum_Ico_eq_sum_range]
    have : ∀ k, emaW F.β (N + k + (J + 1)) ^ 2 = emaW F.β (k + (N + (J + 1))) ^ 2 := fun k => by
      congr 2; omega
    simp_rw [this]
    exact (hw2s.comp_injective (add_left_injective (N + (J + 1)))).sum_le_tsum _
      (fun _ _ => sq_nonneg _) |>.trans_eq' rfl
  have hc0 : Tendsto c atTop (𝓝 0) := by
    have h1 := tendsto_sum_nat_add (fun j : ℕ => emaW F.β j ^ 2)
    have h2 : Tendsto (fun N : ℕ => N + (J + 1)) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_right N (J + 1)) tendsto_id
    simpa using (h1.comp h2).const_mul V
  have hsw : Summable (fun j : ℕ => emaW F.β j) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left (1 - F.β)
  have hw : HasSum (fun r : ℕ => emaW F.β (r + (J + 1))) (F.β ^ (J + 1)) := by
    have h0 : HasSum (fun j : ℕ => emaW F.β j) 1 := by
      have := hsw.hasSum
      rwa [tsum_emaW hβ0 hβ1] at this
    have h1 := (hasSum_nat_add_iff' (J + 1)).2 h0
    rwa [startup_weight_sum hβ0 hβ1 J, sub_sub_cancel] at h1
  have hw2 : HasSum (fun r : ℕ => emaW F.β (r + (J + 1)) ^ 2)
      (sPow F.β 2 * F.β ^ (2 * (J + 1))) := by
    have h0 : HasSum (fun j : ℕ => if J < j then emaW F.β j ^ 2 else 0)
        (sPow F.β 2 * F.β ^ (2 * (J + 1))) := by
      have hg : Summable (fun j : ℕ => if J < j then emaW F.β j ^ 2 else 0) := by
        refine Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hw2s
        · split_ifs <;> positivity
        · split_ifs
          · exact le_rfl
          · exact sq_nonneg _
      have := hg.hasSum
      rwa [truncation_tail_weight_sq_sum hβ0 hβ1 J] at this
    have h1 := (hasSum_nat_add_iff' (J + 1)).2 h0
    have h2 : ∑ i ∈ Finset.range (J + 1), (if J < i then emaW F.β i ^ 2 else 0) = 0 :=
      Finset.sum_eq_zero fun i hi => by
        have := Finset.mem_range.1 hi
        simp [Nat.not_lt.2 (by omega : i ≤ J)]
    rw [h2, sub_zero] at h1
    have h3 : (fun n : ℕ => if J < n + (J + 1) then emaW F.β (n + (J + 1)) ^ 2 else 0)
        = fun r : ℕ => emaW F.β (r + (J + 1)) ^ 2 := funext fun n => by simp [if_pos (by omega : J < n + (J + 1))]
    rwa [h3] at h1
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun N => X N ω) atTop (𝓝 (D ω)) := by
    filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
    have hs : Summable (fun j : ℕ => emaW F.β j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) :=
      summable_mat_of_fro _ (hω t)
    have h1 := (hasSum_nat_add_iff' (J + 1)).2 hs.hasSum
    have h3 := h1.sub (hw.smul_const μ)
    have h4 := h3.tendsto_sum_nat
    refine h4.congr (fun N => ?_)
    simp [hXdef, hYdef, smul_sub]
  obtain ⟨hDL, hDX⟩ := l2_limit X D c hXL hconv hc
  have hDint : Integrable (fun ω => fro (D ω) ^ 2) P := integrable_fro_sq_of_memLp hDL
  have hXint : ∀ N, Integrable (fun ω => fro (X N ω) ^ 2) P := fun N =>
    integrable_fro_sq_of_memLp (hXL N)
  have hXsq : ∀ N, ∫ ω, fro (X N ω) ^ 2 ∂P
      = V * ∑ r ∈ Finset.range N, emaW F.β (r + (J + 1)) ^ 2 := by
    intro N
    have h := horth 0 N (Nat.zero_le N)
    have h0 : X 0 = fun _ => 0 := by
      funext ω; simp [hXdef]
    rw [h0, ← Finset.range_eq_Ico] at h
    simpa using h
  have hWt : Tendsto (fun N => ∑ r ∈ Finset.range N, emaW F.β (r + (J + 1)) ^ 2) atTop
      (𝓝 (sPow F.β 2 * F.β ^ (2 * (J + 1)))) := hw2.tendsto_sum_nat
  have hS0 : 0 ≤ sPow F.β 2 * F.β ^ (2 * (J + 1)) :=
    ge_of_tendsto' hWt fun N => Finset.sum_nonneg fun r _ => sq_nonneg _
  have hΔ0 : 0 ≤ ∫ ω, fro (D ω) ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
  have hΔ : ∫ ω, fro (D ω) ^ 2 ∂P = V * (sPow F.β 2 * F.β ^ (2 * (J + 1))) := by
    apply le_antisymm
    · refine le_of_forall_mul (mul_nonneg hV0 hS0) fun ε hε => ?_
      have hlim : Tendsto (fun N => (1 + ε) * (V * ∑ r ∈ Finset.range N,
          emaW F.β (r + (J + 1)) ^ 2) + (1 + ε⁻¹) * c N) atTop
          (𝓝 ((1 + ε) * (V * (sPow F.β 2 * F.β ^ (2 * (J + 1)))) + (1 + ε⁻¹) * 0)) :=
        ((hWt.const_mul V).const_mul (1 + ε)).add (hc0.const_mul (1 + ε⁻¹))
      rw [mul_zero, add_zero] at hlim
      refine ge_of_tendsto' hlim fun N => ?_
      have h1 := young_int hDint (hXint N) (hDX N).1 ε hε
      rw [hXsq N] at h1
      exact h1.trans (by nlinarith [(hDX N).2, show (0 : ℝ) ≤ 1 + ε⁻¹ by positivity])
    · refine le_of_forall_mul hΔ0 fun ε hε => ?_
      have hlim : Tendsto (fun N => (1 + ε) * ∫ ω, fro (D ω) ^ 2 ∂P + (1 + ε⁻¹) * c N) atTop
          (𝓝 ((1 + ε) * ∫ ω, fro (D ω) ^ 2 ∂P + (1 + ε⁻¹) * 0)) :=
        tendsto_const_nhds.add (hc0.const_mul (1 + ε⁻¹))
      rw [mul_zero, add_zero] at hlim
      have hlim2 : Tendsto (fun N => V * ∑ r ∈ Finset.range N, emaW F.β (r + (J + 1)) ^ 2)
          atTop (𝓝 (V * (sPow F.β 2 * F.β ^ (2 * (J + 1))))) := hWt.const_mul V
      refine le_of_tendsto_of_tendsto hlim2 hlim (Filter.Eventually.of_forall fun N => ?_)
      have hd : Integrable (fun ω => fro (X N ω - D ω) ^ 2) P :=
        (hDX N).1.congr (Filter.Eventually.of_forall fun ω => fro_sub_comm_sq _ _)
      have h1 := young_int (hXint N) hDint hd ε hε
      rw [hXsq N] at h1
      have h2 : ∫ ω, fro (X N ω - D ω) ^ 2 ∂P = ∫ ω, fro (D ω - X N ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => fro_sub_comm_sq _ _)
      rw [h2] at h1
      exact h1.trans (by nlinarith [(hDX N).2, show (0 : ℝ) ≤ 1 + ε⁻¹ by positivity])
  have hDmean : ∀ i k, ∫ ω, D ω i k ∂P = 0 := by
    intro i k
    have hle : ∀ N, (∫ ω, D ω i k ∂P) ^ 2 ≤ c N := by
      intro N
      have hL : MemLp (fun ω => D ω i k - X N ω i k) 2 P := (hDL i k).sub (hXL N i k)
      have h1 := sq_integral_le_of_memLp hL
      rw [integral_sub ((hDL i k).integrable one_le_two) ((hXL N i k).integrable one_le_two),
        hXmean, sub_zero] at h1
      refine h1.trans ((integral_mono hL.integrable_sq (hDX N).1 fun ω => ?_).trans (hDX N).2)
      have := pow_le_pow_left₀ (abs_nonneg (D ω i k - X N ω i k))
        (abs_entry_le_fro' (D ω - X N ω) i k) 2
      rwa [sq_abs] at this
    have h0 : (∫ ω, D ω i k ∂P) ^ 2 ≤ 0 := ge_of_tendsto' hc0 hle
    exact pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h0 (sq_nonneg _))
  have hTe : ∀ ω i k, (frozenBuf F S t ω - truncBuf F S t J ω) i k
      = D ω i k + F.β ^ (J + 1) * μ i k := by
    intro ω i k
    simp [hDdef, Matrix.sub_apply, Matrix.smul_apply]
  have hTL : ∀ i k, MemLp (fun ω => (frozenBuf F S t ω - truncBuf F S t J ω) i k) 2 P := by
    intro i k
    have : (fun ω => (frozenBuf F S t ω - truncBuf F S t J ω) i k)
        = fun ω => D ω i k + F.β ^ (J + 1) * μ i k := funext fun ω => hTe ω i k
    rw [this]
    exact (hDL i k).add (memLp_const _)
  have hmu : mean P (frozenBatchG F S (t + 1)) = μ := mean_batch_eq F S (t + 1)
  refine ⟨integrable_fro_sq_of_memLp hTL, ?_, ?_⟩
  · ext i k
    simp only [mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
    rw [hGmean]
    simp_rw [hTe]
    rw [integral_add ((hDL i k).integrable one_le_two) (integrable_const _), hDmean]
    simp
  · rw [hmu]
    have hik : ∀ i k, ∫ ω, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P
        = ∫ ω, D ω i k ^ 2 ∂P + (F.β ^ (J + 1) * μ i k) ^ 2 := by
      intro i k
      set a := F.β ^ (J + 1) * μ i k with ha
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
    have e1 : (fun ω => fro (frozenBuf F S t ω - truncBuf F S t J ω) ^ 2)
        = fun ω => ∑ i, ∑ k, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 := by
      funext ω
      rw [fro_sq_eq]
      simp_rw [hTe]
    have e2 : ∫ ω, fro (D ω) ^ 2 ∂P = ∑ i, ∑ k, ∫ ω, D ω i k ^ 2 ∂P := by
      simp_rw [fro_sq_eq]
      rw [integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ => (hDL i k).integrable_sq)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finset_sum _ (fun k _ => (hDL i k).integrable_sq)]
    have e5 : ∫ ω, ∑ i, ∑ k, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P
        = ∑ i, ∫ ω, ∑ k, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P :=
      integral_finset_sum _ (fun i _ => integrable_finset_sum _ fun k _ =>
        ((hDL i k).add (memLp_const _)).integrable_sq)
    rw [e1, e5]
    have e3 : ∀ i, ∫ ω, ∑ k, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P
        = ∑ k, (∫ ω, D ω i k ^ 2 ∂P + (F.β ^ (J + 1) * μ i k) ^ 2) := by
      intro i
      have e6 : ∫ ω, ∑ k, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P
          = ∑ k, ∫ ω, (D ω i k + F.β ^ (J + 1) * μ i k) ^ 2 ∂P :=
        integral_finset_sum _ (fun k _ => ((hDL i k).add (memLp_const _)).integrable_sq)
      rw [e6]
      exact Finset.sum_congr rfl fun k _ => hik i k
    simp_rw [e3, Finset.sum_add_distrib]
    rw [← e2, hΔ, fro_sq_eq μ]
    have e4 : ∑ i, ∑ k, (F.β ^ (J + 1) * μ i k) ^ 2 = F.β ^ (2 * (J + 1)) * ∑ i, ∑ k, μ i k ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_pow, ← pow_mul, mul_comm (J + 1) 2]
    rw [e4]
    ring


/-- `lem:app-setup-truncation`(i), snapshot `cr-2026-10-23`. Declaration of record of part (i). The full environment, verbatim from `section.tex` (l.868–886):
```latex
\begin{lemma}[History truncation and sample sensitivity]\label{lem:app-setup-truncation}
In the frozen-state model let $M^{(J)}\defeq\sum_{j=0}^J\emaw jG_{t+1-j}$ for
$J\ge0$, and let $\ridge>0$.
\begin{enumerate}[label=(\roman*)]
\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item $\EE\norm{\Qridge\ridge(\Mt)-\Qridge\ridge(M^{(J)})}_\F^2\le\ridge^{-1}\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item Let $F:\R^{\Nout\times\Nin}\to\R$ be Lipschitz in Frobenius norm with
constant $L_F$, and let $\Mt^{[ja]}$ denote the buffer with the sample
$(z_{ja},w_{ja})$ replaced by an independent copy. Then
\[
\EE\big|F(\Mt)-F(\Mt^{[ja]})\big|^2\le\frac{2L_F^2\,\emaw j^2\,\mathsf V_B}{B},\qquad
\Var F(\Mt)\le L_F^2\,\sw2\,\mathsf V_B .
\]
\item If $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ then
$\norm{\EE\Gt}_\F\le C_\Sigma$ and
$\mathsf V_B\le C_\Sigma^2\,(\Nout\Nin+2\Nout+2\Nin+3)/B$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_truncation_i [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    Integrable (fun ω => fro (frozenBuf F S t ω - truncBuf F S t J ω) ^ 2) P ∧
      mean P (fun ω => frozenBuf F S t ω - truncBuf F S t J ω)
        = (F.β ^ (J + 1)) • mean P (frozenBatchG F S (t + 1)) ∧
      ∫ ω, (fro (frozenBuf F S t ω - truncBuf F S t J ω)) ^ 2 ∂P
        = F.β ^ (2 * (J + 1)) *
            (fro (mean P (frozenBatchG F S (t + 1))) ^ 2 + sPow F.β 2 * frozenVB S F) := by
  exact truncation_i_core F S t J

/-- `lem:app-setup-truncation`(ii), snapshot `cr-2026-10-23`. Declaration of record of part (ii). The full environment, verbatim from `section.tex` (l.868–886):
```latex
\begin{lemma}[History truncation and sample sensitivity]\label{lem:app-setup-truncation}
In the frozen-state model let $M^{(J)}\defeq\sum_{j=0}^J\emaw jG_{t+1-j}$ for
$J\ge0$, and let $\ridge>0$.
\begin{enumerate}[label=(\roman*)]
\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item $\EE\norm{\Qridge\ridge(\Mt)-\Qridge\ridge(M^{(J)})}_\F^2\le\ridge^{-1}\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item Let $F:\R^{\Nout\times\Nin}\to\R$ be Lipschitz in Frobenius norm with
constant $L_F$, and let $\Mt^{[ja]}$ denote the buffer with the sample
$(z_{ja},w_{ja})$ replaced by an independent copy. Then
\[
\EE\big|F(\Mt)-F(\Mt^{[ja]})\big|^2\le\frac{2L_F^2\,\emaw j^2\,\mathsf V_B}{B},\qquad
\Var F(\Mt)\le L_F^2\,\sw2\,\mathsf V_B .
\]
\item If $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ then
$\norm{\EE\Gt}_\F\le C_\Sigma$ and
$\mathsf V_B\le C_\Sigma^2\,(\Nout\Nin+2\Nout+2\Nin+3)/B$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_truncation_ii [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    Integrable (fun ω => fro (Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω)) ^ 2) P ∧
      ∫ ω, (fro (Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω))) ^ 2 ∂P
        ≤ ϱ⁻¹ * (F.β ^ (2 * (J + 1)) *
            (fro (mean P (frozenBatchG F S (t + 1))) ^ 2 + sPow F.β 2 * frozenVB S F)) := by
  obtain ⟨hint, -, hval⟩ := lem_app_setup_truncation_i ϱ hϱ F S t J
  have hbound : ∀ ω, fro (Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω)) ^ 2
      ≤ ϱ⁻¹ * fro (frozenBuf F S t ω - truncBuf F S t J ω) ^ 2 :=
    fun ω => fro_sq_Q_le ϱ hϱ _ _
  have hdiff : AEStronglyMeasurable (fun ω => Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω)) P :=
    (((Q_measurable_fn ϱ hϱ).comp_aemeasurable (frozenBuf_aesm F S t).aemeasurable).aestronglyMeasurable).sub
      (((Q_measurable_fn ϱ hϱ).comp_aemeasurable (truncBuf_aesm F S t J).aemeasurable).aestronglyMeasurable)
  have hfro : Measurable (fun K : Mat m n => fro K ^ 2) := by
    unfold fro
    fun_prop
  have hmeas : AEStronglyMeasurable
      (fun ω => fro (Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω)) ^ 2) P :=
    (hfro.comp_aemeasurable hdiff.aemeasurable).aestronglyMeasurable
  have hint2 : Integrable
      (fun ω => fro (Q ϱ (frozenBuf F S t ω) - Q ϱ (truncBuf F S t J ω)) ^ 2) P := by
    refine Integrable.mono' (hint.const_mul ϱ⁻¹) hmeas (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact hbound ω
  refine ⟨hint2, ?_⟩
  have hmono := integral_mono hint2 (hint.const_mul ϱ⁻¹) hbound
  rw [integral_const_mul, hval] at hmono
  exact hmono

private def Tm (F : FrozenParams m n B) (p : Vec m × Vec n) : Mat m n :=
  (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)

private lemma Tm_cont (F : FrozenParams m n B) : Continuous (Tm F) := summand_cont F

private lemma Tm_entry (F : FrozenParams m n B) (p : Vec m × Vec n) (i : Fin m) (j : Fin n) :
    Tm F p i j = ∑ r : Fin m, ∑ q : Fin n,
      (rOut F.C i r * rIn F.C q j) * sampleX F.A p.1 p.2 r q := by
  unfold Tm sampleX
  simp only [Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.vecMulVec_apply]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

private lemma batch_eq_Tm (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω) :
    frozenBatchG F S s ω = ((B : ℝ))⁻¹ • ∑ a : Fin B, Tm F (S.zw s a ω) := rfl

private def vv (F : FrozenParams m n B) : ℝ :=
  ∑ i : Fin m, ∑ j : Fin n, variance (fun x : Vec m × Vec n => Tm F x i j)
    ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))

private lemma Tm_meas_entry (F : FrozenParams m n B) (i : Fin m) (j : Fin n) :
    Measurable (fun x : Vec m × Vec n => Tm F x i j) :=
  (Continuous.matrix_elem (Tm_cont F) i j).measurable

private lemma Tm_memLp_nu (F : FrozenParams m n B) (i : Fin m) (j : Fin n) :
    MemLp (fun x : Vec m × Vec n => Tm F x i j) 2
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  have h : ∀ r q, MemLp (fun x : Vec m × Vec n => sampleX F.A x.1 x.2 r q) 2
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := fun r q =>
    sampleX_entry_memLp (P := (Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) (Z := fun x => x.1) (W := fun x => x.2)
      measurable_fst measurable_snd (by simp) F.A F.hA r q
  simp_rw [Tm_entry]
  exact memLp_finsetSum _ fun r _ => memLp_finsetSum _ fun q _ => (h r q).const_mul _

private lemma Tm_memLp {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (F : FrozenParams m n B) {X : Ω' → Vec m × Vec n} (hX : Measurable X)
    (hl : P'.map X = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    (i : Fin m) (j : Fin n) :
    MemLp (fun ω => Tm F (X ω) i j) 2 P' := by
  have h := Tm_memLp_nu F i j
  rw [← hl] at h
  exact (memLp_map_measure_iff h.aestronglyMeasurable hX.aemeasurable).1 h

private lemma Tm_integral_law {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (F : FrozenParams m n B) {X : Ω' → Vec m × Vec n} (hX : Measurable X)
    (hl : P'.map X = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    (i : Fin m) (j : Fin n) :
    ∫ ω, Tm F (X ω) i j ∂P' = ∫ x, Tm F x i j ∂((Muon.Foundations.stdGaussianPi m).prod
      (Muon.Foundations.stdGaussianPi n)) := by
  rw [← hl, integral_map hX.aemeasurable (Tm_meas_entry F i j).aestronglyMeasurable]

private lemma Tm_variance_law {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    (F : FrozenParams m n B) {X : Ω' → Vec m × Vec n} (hX : Measurable X)
    (hl : P'.map X = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    (i : Fin m) (j : Fin n) :
    variance (fun ω => Tm F (X ω) i j) P' = variance (fun x : Vec m × Vec n => Tm F x i j)
      ((Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n)) := by
  rw [← hl, variance_map (Tm_meas_entry F i j).aemeasurable hX.aemeasurable]
  rfl

private lemma pair_int {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P'] (F : FrozenParams m n B) {X X' : Ω' → Vec m × Vec n}
    (hX : Measurable X) (hX' : Measurable X')
    (hl : P'.map X = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    (hl' : P'.map X' = (Muon.Foundations.stdGaussianPi m).prod (Muon.Foundations.stdGaussianPi n))
    (hind : IndepFun X X' P') :
    ∫ ω, fro (Tm F (X ω) - Tm F (X' ω)) ^ 2 ∂P' = 2 * vv F := by
  have hU : ∀ i j, MemLp (fun ω => Tm F (X ω) i j) 2 P' := fun i j => Tm_memLp F hX hl i j
  have hU' : ∀ i j, MemLp (fun ω => Tm F (X' ω) i j) 2 P' := fun i j => Tm_memLp F hX' hl' i j
  have hD : ∀ i j, MemLp (fun ω => Tm F (X ω) i j - Tm F (X' ω) i j) 2 P' :=
    fun i j => (hU i j).sub (hU' i j)
  have e1 : ∀ ω, fro (Tm F (X ω) - Tm F (X' ω)) ^ 2
      = ∑ i, ∑ j, (Tm F (X ω) i j - Tm F (X' ω) i j) ^ 2 := by
    intro ω
    rw [fro_sq_eq]
    simp [Matrix.sub_apply]
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hD i j).integrable_sq)]
  unfold vv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hD i j).integrable_sq), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hi : IndepFun (fun ω => Tm F (X ω) i j) (fun ω => Tm F (X' ω) i j) P' :=
    hind.comp (Tm_meas_entry F i j) (Tm_meas_entry F i j)
  have hm0 : ∫ ω, (Tm F (X ω) i j - Tm F (X' ω) i j) ∂P' = 0 := by
    rw [integral_sub ((hU i j).integrable one_le_two) ((hU' i j).integrable one_le_two),
      Tm_integral_law F hX hl, Tm_integral_law F hX' hl', sub_self]
  have hv : variance (fun ω => Tm F (X ω) i j - Tm F (X' ω) i j) P'
      = variance (fun x : Vec m × Vec n => Tm F x i j) ((Muon.Foundations.stdGaussianPi m).prod
        (Muon.Foundations.stdGaussianPi n)) * 2 := by
    have h1 : (fun ω => Tm F (X ω) i j - Tm F (X' ω) i j)
        = (fun ω => Tm F (X ω) i j) + (-(fun ω => Tm F (X' ω) i j)) := by
      funext ω; simp [sub_eq_add_neg]
    rw [h1, IndepFun.variance_add (hU i j) (hU' i j).neg hi.neg_right, variance_neg,
      Tm_variance_law F hX hl, Tm_variance_law F hX' hl']
    ring
  have := variance_eq_integral (hD i j).aemeasurable (μ := P')
  rw [hv] at this
  have h3 : (P'[fun ω => Tm F (X ω) i j - Tm F (X' ω) i j]) = 0 := hm0
  rw [h3] at this
  simp only [sub_zero] at this
  rw [← this]
  ring

private lemma batch_entry_Tm (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) (ω : Ω)
    (i : Fin m) (j : Fin n) :
    frozenBatchG F S s ω i j = (B : ℝ)⁻¹ * ∑ a : Fin B, Tm F (S.zw s a ω) i j := by
  rw [batch_eq_Tm]
  simp [Matrix.smul_apply, Matrix.sum_apply]

private lemma frozenVB_eq [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) : frozenVB S F = vv F / (B : ℝ) := by
  unfold frozenVB vv
  have hG : ∀ i j, MemLp (fun ω => frozenBatchG F S 0 ω i j) 2 P := fun i j =>
    frozenBatchG_entry_memLp F S 0 i j
  have e1 : ∀ ω, fro (frozenBatchG F S 0 ω - mean P (frozenBatchG F S 0)) ^ 2
      = ∑ i, ∑ j, (frozenBatchG F S 0 ω i j - ∫ ω', frozenBatchG F S 0 ω' i j ∂P) ^ 2 := by
    intro ω
    rw [fro_sq_eq]
    simp [Matrix.sub_apply, mean]
  simp_rw [e1]
  have hI : ∀ i j, Integrable (fun ω => (frozenBatchG F S 0 ω i j
      - ∫ ω', frozenBatchG F S 0 ω' i j ∂P) ^ 2) P := fun i j =>
    ((hG i j).sub (memLp_const (∫ ω', frozenBatchG F S 0 ω' i j ∂P))).integrable_sq
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hI i j),
    Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hI i j), Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← variance_eq_integral (hG i j).aemeasurable]
  have h1 : (fun ω => frozenBatchG F S 0 ω i j)
      = fun ω => ((B : ℝ)⁻¹) * (∑ a : Fin B, (fun ω => Tm F (S.zw 0 a ω) i j)) ω := by
    funext ω
    rw [batch_entry_Tm, Finset.sum_apply]
  rw [h1, variance_const_mul, IndepFun.variance_sum]
  · have : ∀ a : Fin B, variance (fun ω => Tm F (S.zw 0 a ω) i j) P
        = variance (fun x : Vec m × Vec n => Tm F x i j) ((Muon.Foundations.stdGaussianPi m).prod
          (Muon.Foundations.stdGaussianPi n)) := fun a =>
      Tm_variance_law F (S.meas 0 a) (S.law 0 a) i j
    simp_rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    by_cases hB : (B : ℝ) = 0
    · simp [hB]
    · field_simp
  · exact fun a _ => Tm_memLp F (S.meas 0 a) (S.law 0 a) i j
  · intro a _ a' _ haa
    have := S.indep.indepFun (i := ((0 : ℤ), a)) (j := ((0 : ℤ), a'))
      (by intro h; exact haa (by simpa using h))
    exact this.comp (Tm_meas_entry F i j) (Tm_meas_entry F i j)

private lemma continuous_fro_fn {m n : ℕ} : Continuous (fun K : Mat m n => fro K) := by
  unfold fro
  fun_prop

private lemma Phi_cont (LF : ℝ) (Φ : Mat m n → ℝ)
    (hΦ : ∀ K L : Mat m n, |Φ K - Φ L| ≤ LF * fro (K - L)) : Continuous Φ := by
  rw [continuous_iff_continuousAt]
  intro K
  rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
  refine squeeze_zero_norm' (a := fun K' => LF * fro (K' - K))
    (Filter.Eventually.of_forall fun K' => ?_) ?_
  · rw [Real.norm_eq_abs]; exact hΦ K' K
  · have hc : Continuous (fun K' : Mat m n => LF * fro (K' - K)) :=
      continuous_const.mul (continuous_fro_fn.comp (continuous_id.sub continuous_const))
    have := hc.tendsto K
    simpa [fro] using this

private lemma memLp_Phi [IsProbabilityMeasure P] (LF : ℝ) (Φ : Mat m n → ℝ)
    (hΦ : ∀ K L : Mat m n, |Φ K - Φ L| ≤ LF * fro (K - L)) {K : Ω → Mat m n}
    (hK : AEStronglyMeasurable K P) (hint : Integrable (fun ω => fro (K ω) ^ 2) P) :
    MemLp (fun ω => Φ (K ω)) 2 P := by
  have hm : AEStronglyMeasurable (fun ω => Φ (K ω)) P :=
    (Phi_cont LF Φ hΦ).comp_aestronglyMeasurable hK
  rw [memLp_two_iff_integrable_sq hm]
  refine Integrable.mono' ((integrable_const (2 * Φ 0 ^ 2)).add (hint.const_mul (2 * LF ^ 2)))
    (hm.pow 2) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h1 : |Φ (K ω) - Φ 0| ≤ LF * fro (K ω - 0) := hΦ _ _
  rw [sub_zero] at h1
  have h2 : Φ (K ω) ^ 2 ≤ 2 * Φ 0 ^ 2 + 2 * (LF * fro (K ω)) ^ 2 := by
    have h3 : (Φ (K ω) - Φ 0) ^ 2 ≤ (LF * fro (K ω)) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    nlinarith [sq_nonneg (Φ (K ω) - 2 * Φ 0)]
  calc Φ (K ω) ^ 2 ≤ 2 * Φ 0 ^ 2 + 2 * (LF * fro (K ω)) ^ 2 := h2
    _ = 2 * Φ 0 ^ 2 + 2 * LF ^ 2 * fro (K ω) ^ 2 := by ring

private lemma truncBuf_entry_memLp [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) (i : Fin m) (j : Fin n) :
    MemLp (fun ω => truncBuf F S t J ω i j) 2 P := by
  have : (fun ω => truncBuf F S t J ω i j) = fun ω => ∑ r ∈ Finset.range (J + 1),
      emaW F.β r * frozenBatchG F S (t + 1 - (r : ℤ)) ω i j := by
    funext ω; simp [truncBuf, Matrix.sum_apply, Matrix.smul_apply]
  rw [this]
  exact memLp_finsetSum _ fun r _ => (frozenBatchG_entry_memLp F S _ i j).const_mul _

private lemma trunc_fro_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ) :
    Integrable (fun ω => fro (truncBuf F S t J ω) ^ 2) P :=
  integrable_fro_sq_of_memLp (truncBuf_entry_memLp F S t J)

private lemma buf_fro_int [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) :
    Integrable (fun ω => fro (frozenBuf F S t ω) ^ 2) P := by
  have h1 := (truncation_i_core F S t 0).1
  have h2 := trunc_fro_int F S t 0
  have hm : AEStronglyMeasurable (fun ω => fro (frozenBuf F S t ω) ^ 2) P :=
    (continuous_fro_sq.comp_aestronglyMeasurable (frozenBuf_aesm F S t))
  refine Integrable.mono' ((h2.const_mul 2).add (h1.const_mul 2)) hm
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have := young_fro (frozenBuf F S t ω) (truncBuf F S t 0 ω) 1 one_pos
  simp only [Pi.add_apply]
  norm_num at this ⊢
  linarith

private lemma trunc_eq_sum (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (J : ℕ)
    (ω : Ω) : truncBuf F S t J ω = ∑ k : Fin (J + 1) × Fin B,
      (emaW F.β k.1 * (B : ℝ)⁻¹) • Tm F (S.zw (t + 1 - ((k.1 : ℕ) : ℤ)) k.2 ω) := by
  unfold truncBuf
  rw [Finset.sum_range, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [batch_eq_Tm, smul_smul, Finset.smul_sum]

private lemma fro_smul_sq {m n : ℕ} (c : ℝ) (K : Mat m n) : fro (c • K) ^ 2 = c ^ 2 * fro K ^ 2 := by
  simp only [fro_sq_eq, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma var_trunc_le [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (LF : ℝ) (Φ : Mat m n → ℝ)
    (hΦ : ∀ K L : Mat m n, |Φ K - Φ L| ≤ LF * fro (K - L)) (J : ℕ) :
    variance (fun ω => Φ (truncBuf F S t J ω)) P ≤
      LF ^ 2 * frozenVB S F * ∑ j ∈ Finset.range (J + 1), emaW F.β j ^ 2 := by
  classical
  set ν : Measure (Vec m × Vec n) := (Muon.Foundations.stdGaussianPi m).prod
    (Muon.Foundations.stdGaussianPi n) with hν
  let c : Fin (J + 1) × Fin B → ℝ := fun k => emaW F.β k.1 * (B : ℝ)⁻¹
  let Sx : (Fin (J + 1) × Fin B → Vec m × Vec n) → Mat m n := fun x => ∑ k, c k • Tm F (x k)
  let arr : Ω → (Fin (J + 1) × Fin B → Vec m × Vec n) := fun ω k =>
    S.zw (t + 1 - ((k.1 : ℕ) : ℤ)) k.2 ω
  have hSx : Continuous Sx := by
    refine continuous_finsetSum _ fun k _ => ?_
    have h1 : Continuous fun x : Fin (J + 1) × Fin B → Vec m × Vec n => Tm F (x k) :=
      (Tm_cont F).comp (continuous_apply k)
    exact h1.const_smul (c k)
  have harr : Measurable arr := measurable_pi_iff.2 fun k => S.meas _ _
  have htr : ∀ ω, truncBuf F S t J ω = Sx (arr ω) := fun ω => trunc_eq_sum F S t J ω
  have hlaw : P.map arr = Measure.pi (fun _ : Fin (J + 1) × Fin B => ν) := by
    have hind : iIndepFun (fun k : Fin (J + 1) × Fin B => S.zw (t + 1 - ((k.1 : ℕ) : ℤ)) k.2) P := by
      have hinj : Function.Injective
          (fun k : Fin (J + 1) × Fin B => ((t + 1 - ((k.1 : ℕ) : ℤ)), k.2)) := by
        intro k k' h
        simp only [Prod.mk.injEq] at h
        refine Prod.ext (Fin.ext ?_) h.2
        have := h.1
        omega
      exact S.indep.precomp hinj
    rw [(iIndepFun_iff_map_fun_eq_pi_map (fun k => (S.meas _ _).aemeasurable)).1 hind]
    congr 1
    funext k
    exact S.law _ _
  have hΦc := Phi_cont LF Φ hΦ
  have hYmem : MemLp (fun ω => Φ (Sx (arr ω))) 2 P := by
    simp_rw [← htr]
    exact memLp_Phi LF Φ hΦ (truncBuf_aesm F S t J) (trunc_fro_int F S t J)
  have hf : MemLp (fun x => Φ (Sx x)) 2 (Measure.pi fun _ : Fin (J + 1) × Fin B => ν) := by
    rw [← hlaw]
    exact (memLp_map_measure_iff (hΦc.comp hSx).aestronglyMeasurable harr.aemeasurable).2 hYmem
  have hvar : variance (fun ω => Φ (truncBuf F S t J ω)) P
      = variance (fun x => Φ (Sx x)) (Measure.pi fun _ : Fin (J + 1) × Fin B => ν) := by
    rw [← hlaw, variance_map (X := fun x => Φ (Sx x)) (hΦc.comp hSx).measurable.aemeasurable
      harr.aemeasurable]
    congr 1
    funext ω
    simp [htr]
  rw [hvar]
  refine (Muon.Foundations.efron_stein (fun _ : Fin (J + 1) × Fin B => ν) _ hf).trans ?_
  have hcoord : ∀ i : Fin (J + 1) × Fin B,
      ∫ p, (Φ (Sx p.1) - Φ (Sx (Function.update p.1 i (p.2 i)))) ^ 2
        ∂((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
          (Measure.pi fun _ : Fin (J + 1) × Fin B => ν))
      ≤ 2 * (LF ^ 2 * c i ^ 2 * vv F) := by
    intro i
    have hmp1 : MeasureTheory.MeasurePreserving
        (fun p : (Fin (J + 1) × Fin B → Vec m × Vec n) × (Fin (J + 1) × Fin B → Vec m × Vec n) =>
          p.1 i)
        ((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
          (Measure.pi fun _ : Fin (J + 1) × Fin B => ν)) ν :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin (J + 1) × Fin B => ν) i).comp
        MeasureTheory.measurePreserving_fst
    have hmp2 : MeasureTheory.MeasurePreserving
        (fun p : (Fin (J + 1) × Fin B → Vec m × Vec n) × (Fin (J + 1) × Fin B → Vec m × Vec n) =>
          p.2 i)
        ((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
          (Measure.pi fun _ : Fin (J + 1) × Fin B => ν)) ν :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin (J + 1) × Fin B => ν) i).comp
        MeasureTheory.measurePreserving_snd
    have hind : IndepFun
        (fun p : (Fin (J + 1) × Fin B → Vec m × Vec n) × (Fin (J + 1) × Fin B → Vec m × Vec n) =>
          p.1 i)
        (fun p : (Fin (J + 1) × Fin B → Vec m × Vec n) × (Fin (J + 1) × Fin B → Vec m × Vec n) =>
          p.2 i)
        ((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
          (Measure.pi fun _ : Fin (J + 1) × Fin B => ν)) :=
      indepFun_prod (X := fun x : Fin (J + 1) × Fin B → Vec m × Vec n => x i)
        (Y := fun x : Fin (J + 1) × Fin B → Vec m × Vec n => x i)
        (measurable_pi_apply i) (measurable_pi_apply i)
    have hP := pair_int F hmp1.measurable hmp2.measurable hmp1.map_eq hmp2.map_eq hind
    have hI : Integrable (fun p : (Fin (J + 1) × Fin B → Vec m × Vec n) ×
        (Fin (J + 1) × Fin B → Vec m × Vec n) => fro (Tm F (p.1 i) - Tm F (p.2 i)) ^ 2)
        ((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
          (Measure.pi fun _ : Fin (J + 1) × Fin B => ν)) :=
      integrable_fro_sq_of_memLp fun a b =>
        (Tm_memLp F hmp1.measurable hmp1.map_eq a b).sub
          (Tm_memLp F hmp2.measurable hmp2.map_eq a b)
    have hpw : ∀ p : (Fin (J + 1) × Fin B → Vec m × Vec n) ×
        (Fin (J + 1) × Fin B → Vec m × Vec n),
        (Φ (Sx p.1) - Φ (Sx (Function.update p.1 i (p.2 i)))) ^ 2
          ≤ LF ^ 2 * c i ^ 2 * fro (Tm F (p.1 i) - Tm F (p.2 i)) ^ 2 := by
      intro p
      have hdiff : Sx p.1 - Sx (Function.update p.1 i (p.2 i))
          = c i • (Tm F (p.1 i) - Tm F (p.2 i)) := by
        simp only [Sx]
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
        · simp [smul_sub]
        · intro k _ hk
          simp [Function.update_of_ne hk]
        · simp
      have h1 := hΦ (Sx p.1) (Sx (Function.update p.1 i (p.2 i)))
      rw [hdiff] at h1
      have h2 : (Φ (Sx p.1) - Φ (Sx (Function.update p.1 i (p.2 i)))) ^ 2
          ≤ (LF * fro (c i • (Tm F (p.1 i) - Tm F (p.2 i)))) ^ 2 := by
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) h1 2
      refine h2.trans (le_of_eq ?_)
      rw [mul_pow, fro_smul_sq]
      ring
    have := integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => sq_nonneg _)
      (hI.const_mul (LF ^ 2 * c i ^ 2)) (Filter.Eventually.of_forall hpw)
    rw [integral_const_mul, hP] at this
    linarith
  have hsum : ∑ k : Fin (J + 1) × Fin B, c k ^ 2
      = (B : ℝ)⁻¹ * ∑ j ∈ Finset.range (J + 1), emaW F.β j ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_range]
    simp only [c, mul_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hB : (B : ℝ) = 0
    · simp [hB]
    · field_simp
  calc (1 / 2) * ∑ i, ∫ p, (Φ (Sx p.1) - Φ (Sx (Function.update p.1 i (p.2 i)))) ^ 2
          ∂((Measure.pi fun _ : Fin (J + 1) × Fin B => ν).prod
            (Measure.pi fun _ : Fin (J + 1) × Fin B => ν))
      ≤ (1 / 2) * ∑ i : Fin (J + 1) × Fin B, 2 * (LF ^ 2 * c i ^ 2 * vv F) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) (by norm_num)
    _ = LF ^ 2 * vv F * ∑ k, c k ^ 2 := by
        have e : ∀ i : Fin (J + 1) × Fin B, 2 * (LF ^ 2 * c i ^ 2 * vv F)
            = 2 * (LF ^ 2 * vv F) * c i ^ 2 := fun i => by ring
        simp_rw [e, ← Finset.mul_sum]
        ring
    _ = LF ^ 2 * frozenVB S F * ∑ j ∈ Finset.range (J + 1), emaW F.β j ^ 2 := by
        rw [hsum, frozenVB_eq]
        ring

private lemma var_young [IsProbabilityMeasure P] {A D : Ω → ℝ} (hA : MemLp A 2 P)
    (hD : MemLp D 2 P) (ε : ℝ) (hε : 0 < ε) :
    variance (fun ω => A ω + D ω) P ≤
      (1 + ε) * variance A P + (1 + ε⁻¹) * ∫ ω, D ω ^ 2 ∂P := by
  have hAD : MemLp (fun ω => A ω + D ω) 2 P := hA.add hD
  have e1 := variance_eq_integral hAD.aemeasurable (μ := P)
  have e2 := variance_eq_integral hA.aemeasurable (μ := P)
  have e3 := variance_eq_integral hD.aemeasurable (μ := P)
  have hIA : Integrable (fun ω => (A ω - P[A]) ^ 2) P :=
    (hA.sub (memLp_const (P[A]))).integrable_sq
  have hID : Integrable (fun ω => (D ω - P[D]) ^ 2) P :=
    (hD.sub (memLp_const (P[D]))).integrable_sq
  have hmean : P[fun ω => A ω + D ω] = P[A] + P[D] :=
    integral_add (hA.integrable one_le_two) (hD.integrable one_le_two)
  rw [e1, hmean]
  have hle : ∫ ω, (A ω + D ω - (P[A] + P[D])) ^ 2 ∂P
      ≤ ∫ ω, ((1 + ε) * (A ω - P[A]) ^ 2 + (1 + ε⁻¹) * (D ω - P[D]) ^ 2) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => sq_nonneg _)
      ((hIA.const_mul _).add (hID.const_mul _)) (Filter.Eventually.of_forall fun ω => ?_)
    show (A ω + D ω - (P[A] + P[D])) ^ 2 ≤
      (1 + ε) * (A ω - P[A]) ^ 2 + (1 + ε⁻¹) * (D ω - P[D]) ^ 2
    have := young_sq (A ω - P[A] + (D ω - P[D])) (A ω - P[A]) ε hε
    have h2 : A ω - P[A] + (D ω - P[D]) - (A ω - P[A]) = D ω - P[D] := by ring
    rw [h2] at this
    have h3 : A ω + D ω - (P[A] + P[D]) = A ω - P[A] + (D ω - P[D]) := by ring
    rw [h3]
    exact this
  rw [integral_add (hIA.const_mul _) (hID.const_mul _), integral_const_mul,
    integral_const_mul] at hle
  have hvD : variance D P ≤ ∫ ω, D ω ^ 2 ∂P := variance_le_expectation_sq hD.aestronglyMeasurable
  rw [← e2, ← e3] at hle
  have hq : (0 : ℝ) ≤ 1 + ε⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hvD hq]

private lemma ema_sq_summable {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    Summable (fun j : ℕ => emaW β j ^ 2) := by
  have h := (summable_geometric_of_lt_one (sq_nonneg β)
    (by nlinarith : β ^ 2 < 1)).mul_left ((1 - β) ^ 2)
  refine h.congr (fun j => ?_)
  simp only [emaW]
  ring

private lemma batchOf_copy_ne (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (C : IndepCopy S) (s : ℤ) (a : Fin B) (s' : ℤ) (h : s' ≠ s) (ω : Ω) :
    batchOf F (copySamples S C s a) s' ω = frozenBatchG F S s' ω := by
  unfold batchOf copySamples frozenBatchG
  simp [Function.update_of_ne h]

private lemma batchOf_copy_eq (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (C : IndepCopy S) (s : ℤ) (a : Fin B) (ω : Ω) :
    batchOf F (copySamples S C s a) s ω = frozenBatchG F S s ω
      + (B : ℝ)⁻¹ • (Tm F (C.zw' s a ω) - Tm F (S.zw s a ω)) := by
  rw [batch_eq_Tm, ← smul_add]
  show (B : ℝ)⁻¹ • ∑ b : Fin B, Tm F ((copySamples S C s a) s b ω) = _
  congr 1
  have : ∑ b : Fin B, Tm F ((copySamples S C s a) s b ω) - ∑ b : Fin B, Tm F (S.zw s b ω)
      = Tm F (C.zw' s a ω) - Tm F (S.zw s a ω) := by
    rw [← Finset.sum_sub_distrib, Finset.sum_eq_single a]
    · simp [copySamples]
    · intro b _ hb
      simp [copySamples, Function.update_of_ne hb]
    · simp
  rw [← this]
  abel

private lemma copy_buf_ae [IsProbabilityMeasure P] (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (C : IndepCopy S) (j : ℕ) (a : Fin B) :
    ∀ᵐ ω ∂P, bufOf F (copySamples S C (t + 1 - (j : ℤ)) a) t ω = frozenBuf F S t ω
      + (emaW F.β j * (B : ℝ)⁻¹) •
        (Tm F (C.zw' (t + 1 - (j : ℤ)) a ω) - Tm F (S.zw (t + 1 - (j : ℤ)) a ω)) := by
  filter_upwards [(lem_app_setup_ema_law_i F S).1] with ω hω
  have hs : Summable (fun j' : ℕ => emaW F.β j' • frozenBatchG F S (t + 1 - (j' : ℤ)) ω) :=
    summable_mat_of_fro _ (hω t)
  set f : ℕ → Mat m n := fun j' => emaW F.β j' • frozenBatchG F S (t + 1 - (j' : ℤ)) ω with hf
  set δ : Mat m n := Tm F (C.zw' (t + 1 - (j : ℤ)) a ω) - Tm F (S.zw (t + 1 - (j : ℤ)) a ω)
    with hδ
  have hf' : (fun j' : ℕ => emaW F.β j' •
      batchOf F (copySamples S C (t + 1 - (j : ℤ)) a) (t + 1 - (j' : ℤ)) ω)
      = Function.update f j (f j + (emaW F.β j * (B : ℝ)⁻¹) • δ) := by
    funext j'
    by_cases h : j' = j
    · subst h
      rw [Function.update_self, batchOf_copy_eq, smul_add, smul_smul]
    · rw [Function.update_of_ne h, batchOf_copy_ne]
      intro h2
      apply h
      have : (j' : ℤ) = j := by omega
      exact_mod_cast this
  have hH := hs.hasSum.update j (f j + (emaW F.β j * (B : ℝ)⁻¹) • δ)
  unfold bufOf
  rw [hf', hH.tsum_eq]
  show _ = ∑' j' : ℕ, f j' + _
  rw [← hs.hasSum.tsum_eq]
  abel

/-- `lem:app-setup-truncation`(iii), snapshot `cr-2026-10-23`. Declaration of record of the replacement clause of part (iii). The full environment, verbatim from `section.tex` (l.868–886):
```latex
\begin{lemma}[History truncation and sample sensitivity]\label{lem:app-setup-truncation}
In the frozen-state model let $M^{(J)}\defeq\sum_{j=0}^J\emaw jG_{t+1-j}$ for
$J\ge0$, and let $\ridge>0$.
\begin{enumerate}[label=(\roman*)]
\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item $\EE\norm{\Qridge\ridge(\Mt)-\Qridge\ridge(M^{(J)})}_\F^2\le\ridge^{-1}\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item Let $F:\R^{\Nout\times\Nin}\to\R$ be Lipschitz in Frobenius norm with
constant $L_F$, and let $\Mt^{[ja]}$ denote the buffer with the sample
$(z_{ja},w_{ja})$ replaced by an independent copy. Then
\[
\EE\big|F(\Mt)-F(\Mt^{[ja]})\big|^2\le\frac{2L_F^2\,\emaw j^2\,\mathsf V_B}{B},\qquad
\Var F(\Mt)\le L_F^2\,\sw2\,\mathsf V_B .
\]
\item If $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ then
$\norm{\EE\Gt}_\F\le C_\Sigma$ and
$\mathsf V_B\le C_\Sigma^2\,(\Nout\Nin+2\Nout+2\Nin+3)/B$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_truncation_iii [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (LF : ℝ) (hLF : 0 ≤ LF) (Φ : Mat m n → ℝ)
    (hΦ : ∀ K L : Mat m n, |Φ K - Φ L| ≤ LF * fro (K - L))
    (C : IndepCopy S) (j : ℕ) (a : Fin B) :
    MemLp (fun ω => Φ (bufOf F (copySamples S C (t + 1 - (j : ℤ)) a) t ω)) 2 P ∧
      ∫ ω, (Φ (frozenBuf F S t ω) - Φ (bufOf F (copySamples S C (t + 1 - (j : ℤ)) a) t ω)) ^ 2 ∂P
        ≤ 2 * LF ^ 2 * (emaW F.β j) ^ 2 * frozenVB S F / (B : ℝ) := by
  classical
  have hae := copy_buf_ae F S t C j a
  have hX : Measurable (S.zw (t + 1 - (j : ℤ)) a) := S.meas _ a
  have hX' : Measurable (C.zw' (t + 1 - (j : ℤ)) a) := C.meas _ a
  have hl := S.law (t + 1 - (j : ℤ)) a
  have hl' := C.law (t + 1 - (j : ℤ)) a
  have hind : IndepFun (S.zw (t + 1 - (j : ℤ)) a) (C.zw' (t + 1 - (j : ℤ)) a) P := by
    have := C.indep.indepFun (i := (false, ((t + 1 - (j : ℤ)), a)))
      (j := (true, ((t + 1 - (j : ℤ)), a))) (by simp)
    simpa using this
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = emaW F.β j * (B : ℝ)⁻¹ := ⟨_, rfl⟩
  obtain ⟨Δ, hΔ⟩ : ∃ Δ : Ω → Mat m n, Δ = fun ω => c •
      (Tm F (C.zw' (t + 1 - (j : ℤ)) a ω) - Tm F (S.zw (t + 1 - (j : ℤ)) a ω)) := ⟨_, rfl⟩
  have hae' : ∀ᵐ ω ∂P, bufOf F (copySamples S C (t + 1 - (j : ℤ)) a) t ω
      = frozenBuf F S t ω + Δ ω := hae.mono fun ω h => by rw [hΔ, hc]; exact h
  have hD : ∀ i k, MemLp (fun ω => Tm F (C.zw' (t + 1 - (j : ℤ)) a ω) i k
      - Tm F (S.zw (t + 1 - (j : ℤ)) a ω) i k) 2 P := fun i k =>
    (Tm_memLp F hX' hl' i k).sub (Tm_memLp F hX hl i k)
  have hDint : Integrable (fun ω => fro (Tm F (C.zw' (t + 1 - (j : ℤ)) a ω)
      - Tm F (S.zw (t + 1 - (j : ℤ)) a ω)) ^ 2) P :=
    integrable_fro_sq_of_memLp fun i k => by simpa [Matrix.sub_apply] using hD i k
  have hΔint : Integrable (fun ω => fro (Δ ω) ^ 2) P := by
    simp_rw [hΔ, fro_smul_sq]
    exact hDint.const_mul _
  have hΔaesm : AEStronglyMeasurable Δ P := by
    rw [hΔ]
    refine AEStronglyMeasurable.const_smul ?_ c
    exact (((Tm_cont F).comp_stronglyMeasurable hX'.stronglyMeasurable).sub
      ((Tm_cont F).comp_stronglyMeasurable hX.stronglyMeasurable)).aestronglyMeasurable
  have hKaesm : AEStronglyMeasurable (fun ω => frozenBuf F S t ω + Δ ω) P :=
    (frozenBuf_aesm F S t).add hΔaesm
  have hKint : Integrable (fun ω => fro (frozenBuf F S t ω + Δ ω) ^ 2) P := by
    have hm : AEStronglyMeasurable (fun ω => fro (frozenBuf F S t ω + Δ ω) ^ 2) P :=
      continuous_fro_sq.comp_aestronglyMeasurable hKaesm
    refine Integrable.mono' (((buf_fro_int F S t).const_mul 2).add (hΔint.const_mul 2)) hm
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have := young_fro (frozenBuf F S t ω + Δ ω) (frozenBuf F S t ω) 1 one_pos
    rw [add_sub_cancel_left] at this
    simp only [Pi.add_apply]
    norm_num at this ⊢
    linarith
  have hmem : MemLp (fun ω => Φ (frozenBuf F S t ω + Δ ω)) 2 P :=
    memLp_Phi LF Φ hΦ hKaesm hKint
  refine ⟨hmem.ae_eq (hae'.mono fun ω h => by simp only [h]), ?_⟩
  have hcongr : ∫ ω, (Φ (frozenBuf F S t ω)
      - Φ (bufOf F (copySamples S C (t + 1 - (j : ℤ)) a) t ω)) ^ 2 ∂P
      = ∫ ω, (Φ (frozenBuf F S t ω) - Φ (frozenBuf F S t ω + Δ ω)) ^ 2 ∂P :=
    integral_congr_ae (hae'.mono fun ω h => by simp only [h])
  rw [hcongr]
  have hpair := pair_int F hX' hX hl' hl hind.symm
  have hm := integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun ω => sq_nonneg (Φ (frozenBuf F S t ω)
      - Φ (frozenBuf F S t ω + Δ ω)))
    (hΔint.const_mul (LF ^ 2)) (Filter.Eventually.of_forall fun ω => ?_)
  · rw [integral_const_mul] at hm
    refine hm.trans (le_of_eq ?_)
    have e : ∫ ω, fro (Δ ω) ^ 2 ∂P = c ^ 2 * (2 * vv F) := by
      simp_rw [hΔ, fro_smul_sq]
      rw [integral_const_mul, hpair]
    rw [e, frozenVB_eq, hc]
    ring
  · show (Φ (frozenBuf F S t ω) - Φ (frozenBuf F S t ω + Δ ω)) ^ 2 ≤ LF ^ 2 * fro (Δ ω) ^ 2
    have h4 := hΦ (frozenBuf F S t ω + Δ ω) (frozenBuf F S t ω)
    rw [add_sub_cancel_left] at h4
    have h5 : (Φ (frozenBuf F S t ω + Δ ω) - Φ (frozenBuf F S t ω)) ^ 2
        ≤ (LF * fro (Δ ω)) ^ 2 := by
      rw [← sq_abs (Φ (frozenBuf F S t ω + Δ ω) - Φ (frozenBuf F S t ω))]
      exact pow_le_pow_left₀ (abs_nonneg _) h4 2
    calc _ = (Φ (frozenBuf F S t ω + Δ ω) - Φ (frozenBuf F S t ω)) ^ 2 := by ring
      _ ≤ _ := h5
      _ = _ := by ring

/-- `lem:app-setup-truncation`(iii), snapshot `cr-2026-10-23`. Declaration of record of the variance clause of part (iii), split out so that it does not depend on the independent-copy hypothesis (`_b`). The full environment, verbatim from `section.tex` (l.868–886):
```latex
\begin{lemma}[History truncation and sample sensitivity]\label{lem:app-setup-truncation}
In the frozen-state model let $M^{(J)}\defeq\sum_{j=0}^J\emaw jG_{t+1-j}$ for
$J\ge0$, and let $\ridge>0$.
\begin{enumerate}[label=(\roman*)]
\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item $\EE\norm{\Qridge\ridge(\Mt)-\Qridge\ridge(M^{(J)})}_\F^2\le\ridge^{-1}\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item Let $F:\R^{\Nout\times\Nin}\to\R$ be Lipschitz in Frobenius norm with
constant $L_F$, and let $\Mt^{[ja]}$ denote the buffer with the sample
$(z_{ja},w_{ja})$ replaced by an independent copy. Then
\[
\EE\big|F(\Mt)-F(\Mt^{[ja]})\big|^2\le\frac{2L_F^2\,\emaw j^2\,\mathsf V_B}{B},\qquad
\Var F(\Mt)\le L_F^2\,\sw2\,\mathsf V_B .
\]
\item If $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ then
$\norm{\EE\Gt}_\F\le C_\Sigma$ and
$\mathsf V_B\le C_\Sigma^2\,(\Nout\Nin+2\Nout+2\Nin+3)/B$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_truncation_iii_b [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (LF : ℝ) (hLF : 0 ≤ LF) (Φ : Mat m n → ℝ)
    (hΦ : ∀ K L : Mat m n, |Φ K - Φ L| ≤ LF * fro (K - L)) :
    MemLp (fun ω => Φ (frozenBuf F S t ω)) 2 P ∧
      variance (fun ω => Φ (frozenBuf F S t ω)) P ≤ LF ^ 2 * sPow F.β 2 * frozenVB S F := by
  have hβ0 := F.hβ.1
  have hβ1 := F.hβ.2
  have hY : MemLp (fun ω => Φ (frozenBuf F S t ω)) 2 P :=
    memLp_Phi LF Φ hΦ (frozenBuf_aesm F S t) (buf_fro_int F S t)
  refine ⟨hY, ?_⟩
  have hV0 : 0 ≤ frozenVB S F := integral_nonneg fun ω => sq_nonneg _
  have hw2s := ema_sq_summable hβ0 hβ1
  have hS : ∀ J : ℕ, ∑ j ∈ Finset.range (J + 1), emaW F.β j ^ 2 ≤ sPow F.β 2 := fun J =>
    hw2s.sum_le_tsum _ (fun _ _ => sq_nonneg _)
  have hR0 : 0 ≤ LF ^ 2 * sPow F.β 2 * frozenVB S F := by
    have : 0 ≤ sPow F.β 2 := tsum_nonneg fun j => sq_nonneg _
    positivity
  refine le_of_forall_mul hR0 fun ε hε => ?_
  set cJ : ℕ → ℝ := fun J => LF ^ 2 * (F.β ^ (2 * (J + 1)) *
    (fro (mean P (frozenBatchG F S (t + 1))) ^ 2 + sPow F.β 2 * frozenVB S F)) with hcJ
  have hbound : ∀ J : ℕ, variance (fun ω => Φ (frozenBuf F S t ω)) P ≤
      (1 + ε) * (LF ^ 2 * sPow F.β 2 * frozenVB S F) + (1 + ε⁻¹) * cJ J := by
    intro J
    obtain ⟨hint, -, hval⟩ := truncation_i_core F S t J
    have hYJ : MemLp (fun ω => Φ (truncBuf F S t J ω)) 2 P :=
      memLp_Phi LF Φ hΦ (truncBuf_aesm F S t J) (trunc_fro_int F S t J)
    have hD : MemLp (fun ω => Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω)) 2 P := hY.sub hYJ
    have hsplit : (fun ω => Φ (frozenBuf F S t ω)) = fun ω => Φ (truncBuf F S t J ω)
        + (Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω)) := by
      funext ω; ring
    have h1 := var_young hYJ hD ε hε
    rw [← hsplit] at h1
    have h2 := var_trunc_le F S t LF Φ hΦ J
    have hVJ : variance (fun ω => Φ (truncBuf F S t J ω)) P
        ≤ LF ^ 2 * sPow F.β 2 * frozenVB S F := by
      refine h2.trans ?_
      have : 0 ≤ LF ^ 2 * frozenVB S F := by positivity
      calc LF ^ 2 * frozenVB S F * ∑ j ∈ Finset.range (J + 1), emaW F.β j ^ 2
          ≤ LF ^ 2 * frozenVB S F * sPow F.β 2 := mul_le_mul_of_nonneg_left (hS J) this
        _ = _ := by ring
    have h3 : ∫ ω, (Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω)) ^ 2 ∂P ≤ cJ J := by
      have hm := integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => sq_nonneg (Φ (frozenBuf F S t ω)
          - Φ (truncBuf F S t J ω)))
        (hint.const_mul (LF ^ 2)) (Filter.Eventually.of_forall fun ω => ?_)
      · rw [integral_const_mul, hval] at hm
        exact hm
      · show (Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω)) ^ 2
          ≤ LF ^ 2 * fro (frozenBuf F S t ω - truncBuf F S t J ω) ^ 2
        have h4 := hΦ (frozenBuf F S t ω) (truncBuf F S t J ω)
        have h5 : (Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω)) ^ 2
            ≤ (LF * fro (frozenBuf F S t ω - truncBuf F S t J ω)) ^ 2 := by
          rw [← sq_abs (Φ (frozenBuf F S t ω) - Φ (truncBuf F S t J ω))]
          exact pow_le_pow_left₀ (abs_nonneg _) h4 2
        calc _ ≤ _ := h5
          _ = _ := by ring
    have hq : (0 : ℝ) ≤ 1 + ε⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h3 hq, mul_le_mul_of_nonneg_left hVJ (by positivity : (0:ℝ) ≤ 1 + ε)]
  have hβ2 : Tendsto (fun J : ℕ => F.β ^ (2 * (J + 1))) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg F.β)
      (by nlinarith : F.β ^ 2 < 1)).comp (tendsto_add_atTop_nat 1)
    refine h.congr (fun J => ?_)
    simp only [Function.comp, ← pow_mul]
  have hlim : Tendsto (fun J : ℕ => (1 + ε) * (LF ^ 2 * sPow F.β 2 * frozenVB S F)
      + (1 + ε⁻¹) * cJ J) atTop
      (𝓝 ((1 + ε) * (LF ^ 2 * sPow F.β 2 * frozenVB S F) + (1 + ε⁻¹) * 0)) := by
    refine tendsto_const_nhds.add (Tendsto.const_mul _ ?_)
    have := (hβ2.mul_const (fro (mean P (frozenBatchG F S (t + 1))) ^ 2
      + sPow F.β 2 * frozenVB S F)).const_mul (LF ^ 2)
    simpa using this
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

/-- Private copy of `Muon.Foundations.sum_sq_mulVec_le` (private there). -/
private lemma tr_sum_sq_mulVec_le {m n : ℕ} (U : Mat m n) (x : Fin n → ℝ) :
    ∑ k, (U *ᵥ x) k ^ 2 ≤ opNorm U ^ 2 * ∑ i, x i ^ 2 := by
  have hb : ‖Matrix.toEuclideanLin U (WithLp.toLp 2 x)‖ ≤ opNorm U * ‖WithLp.toLp 2 x‖ :=
    (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin U)).le_opNorm (WithLp.toLp 2 x)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity)] at hsq
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Real.norm_eq_abs, sq_abs] using hsq

private lemma tr_opNorm_nonneg {a b : ℕ} (K : Mat a b) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

/-- Cauchy–Schwarz form: `cᵀ S c ≤ ‖S‖ ‖c‖²` for a real matrix `S`. -/
private lemma tr_dot_mulVec_le {k : ℕ} (S : Mat k k) (c : Fin k → ℝ) :
    ∑ i, c i * (S *ᵥ c) i ≤ opNorm S * ∑ i, c i ^ 2 := by
  have hq := tr_sum_sq_mulVec_le S c
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (S *ᵥ c)
  have hp : 0 ≤ ∑ i, c i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM := tr_opNorm_nonneg S
  have hMp : 0 ≤ opNorm S * ∑ i, c i ^ 2 := mul_nonneg hM hp
  have hd2 : (∑ i, c i * (S *ᵥ c) i) ^ 2 ≤ (opNorm S * ∑ i, c i ^ 2) ^ 2 := by
    calc (∑ i, c i * (S *ᵥ c) i) ^ 2 ≤ (∑ i, c i ^ 2) * ∑ i, (S *ᵥ c) i ^ 2 := hcs
      _ ≤ (∑ i, c i ^ 2) * (opNorm S ^ 2 * ∑ i, c i ^ 2) :=
          mul_le_mul_of_nonneg_left hq hp
      _ = (opNorm S * ∑ i, c i ^ 2) ^ 2 := by ring
  nlinarith [hd2, hMp]

/-- `tr(Xᵀ S X) ≤ ‖S‖ ‖X‖_F²`. -/
private lemma tr_quad_le {k n : ℕ} (S : Mat k k) (X : Mat k n) :
    Matrix.trace (Xᵀ * S * X) ≤ opNorm S * fro X ^ 2 := by
  have hdiag : ∀ j : Fin n, (Xᵀ * S * X) j j
      = ∑ i, X i j * (S *ᵥ (fun i => X i j)) i := by
    intro j
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have htr : Matrix.trace (Xᵀ * S * X)
      = ∑ j, ∑ i, X i j * (S *ᵥ (fun i => X i j)) i := by
    rw [Matrix.trace]; exact Finset.sum_congr rfl fun j _ => hdiag j
  rw [htr]
  calc ∑ j : Fin n, ∑ i, X i j * (S *ᵥ (fun i => X i j)) i
      ≤ ∑ j : Fin n, opNorm S * ∑ i, X i j ^ 2 :=
        Finset.sum_le_sum fun j _ => tr_dot_mulVec_le S (fun i => X i j)
    _ = opNorm S * fro X ^ 2 := by
        rw [fro_sq_eq]; simp only [Finset.mul_sum]; exact Finset.sum_comm

private lemma tr_tt_eq {k n : ℕ} (X : Mat k n) : Matrix.trace (Xᵀ * X) = fro X ^ 2 := by
  rw [fro_sq_eq, Matrix.trace]
  simp only [Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private lemma tr_fro_one (m : ℕ) : fro (1 : Mat m m) ^ 2 = m := by
  rw [fro_sq_eq]
  simp [Matrix.one_apply]

/-- `‖r_out A r_in‖_F² ≤ ‖Σ_out‖ ‖Σ_in‖` (with `r = Σ^{1/2}`). -/
private lemma tr_fro_RAL_sq {m n : ℕ} (C : Covariances m n) (A : Mat m n) (hA : fro A = 1) :
    fro (rOut C * A * rIn C) ^ 2 ≤ opNorm C.Sout * opNorm C.Sin := by
  have hR : rOut C * rOut C = C.Sout :=
    CFC.sqrt_mul_sqrt_self C.Sout (Matrix.nonneg_iff_posSemidef.mpr C.psdOut)
  have hL : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have hTo : (rOut C)ᵀ = rOut C := by
    have h : (CFC.sqrt C.Sout)ᴴ = CFC.sqrt C.Sout :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sout)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hTi : (rIn C)ᵀ = rIn C := by
    have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  have hM : (rOut C * A * rIn C)ᵀ * (rOut C * A * rIn C)
      = (A * rIn C)ᵀ * C.Sout * (A * rIn C) := by
    rw [← hR]
    simp only [Matrix.transpose_mul, hTo, hTi, Matrix.mul_assoc]
  have h1 : fro (rOut C * A * rIn C) ^ 2 = Matrix.trace ((A * rIn C)ᵀ * C.Sout * (A * rIn C)) := by
    rw [← tr_tt_eq, hM]
  have h2 := tr_quad_le C.Sout (A * rIn C)
  have hAA : Matrix.trace (A * C.Sin * Aᵀ) ≤ opNorm C.Sin := by
    have h := tr_quad_le C.Sin Aᵀ
    have hfT : fro Aᵀ ^ 2 = 1 := by
      rw [← tr_tt_eq, Matrix.transpose_transpose, Matrix.trace_mul_comm, tr_tt_eq, hA, one_pow]
    rw [Matrix.transpose_transpose, hfT, mul_one] at h
    exact h
  have hXX : (A * rIn C) * (A * rIn C)ᵀ = A * C.Sin * Aᵀ := by
    rw [Matrix.transpose_mul, hTi, ← hL]
    simp only [Matrix.mul_assoc]
  have h3 : fro (A * rIn C) ^ 2 ≤ opNorm C.Sin := by
    rw [← tr_tt_eq, Matrix.trace_mul_comm, hXX]
    exact hAA
  calc fro (rOut C * A * rIn C) ^ 2
      = Matrix.trace ((A * rIn C)ᵀ * C.Sout * (A * rIn C)) := h1
    _ ≤ opNorm C.Sout * fro (A * rIn C) ^ 2 := h2
    _ ≤ opNorm C.Sout * opNorm C.Sin :=
        mul_le_mul_of_nonneg_left h3 (tr_opNorm_nonneg _)

private lemma tr_opNorm_mean_sq {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (s : ℤ) : fro (mean P (frozenBatchG F S s)) ^ 2 ≤ opNorm F.C.Sout * opNorm F.C.Sin := by
  rw [(lem_app_setup_gaussian_moments_iv F S s).1]
  exact tr_fro_RAL_sq F.C F.A F.hA

/-- `lem:app-setup-truncation`(iv), snapshot `cr-2026-10-23`. Declaration of record of part (iv). The full environment, verbatim from `section.tex` (l.868–886):
```latex
\begin{lemma}[History truncation and sample sensitivity]\label{lem:app-setup-truncation}
In the frozen-state model let $M^{(J)}\defeq\sum_{j=0}^J\emaw jG_{t+1-j}$ for
$J\ge0$, and let $\ridge>0$.
\begin{enumerate}[label=(\roman*)]
\item $\EE\big(\Mt-M^{(J)}\big)=\bmom^{J+1}\,\EE\Gt$ and
$\EE\norm{\Mt-M^{(J)}}_\F^2=\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item $\EE\norm{\Qridge\ridge(\Mt)-\Qridge\ridge(M^{(J)})}_\F^2\le\ridge^{-1}\bmom^{2(J+1)}\big(\norm{\EE\Gt}_\F^2+\sw2\mathsf V_B\big)$.
\item Let $F:\R^{\Nout\times\Nin}\to\R$ be Lipschitz in Frobenius norm with
constant $L_F$, and let $\Mt^{[ja]}$ denote the buffer with the sample
$(z_{ja},w_{ja})$ replaced by an independent copy. Then
\[
\EE\big|F(\Mt)-F(\Mt^{[ja]})\big|^2\le\frac{2L_F^2\,\emaw j^2\,\mathsf V_B}{B},\qquad
\Var F(\Mt)\le L_F^2\,\sw2\,\mathsf V_B .
\]
\item If $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$ then
$\norm{\EE\Gt}_\F\le C_\Sigma$ and
$\mathsf V_B\le C_\Sigma^2\,(\Nout\Nin+2\Nout+2\Nin+3)/B$.
\end{enumerate}
\end{lemma}
```
-/
theorem lem_app_setup_truncation_iv [IsProbabilityMeasure P] (ϱ : ℝ) (hϱ : 0 < ϱ)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (CSig : ℝ)
    (hCout : opNorm F.C.Sout ≤ CSig) (hCin : opNorm F.C.Sin ≤ CSig) :
    fro (mean P (frozenBatchG F S (t + 1))) ≤ CSig ∧
      frozenVB S F ≤ CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / (B : ℝ) := by
  have hC0 : 0 ≤ CSig := le_trans (tr_opNorm_nonneg F.C.Sout) hCout
  have hfn : ∀ s : ℤ, fro (mean P (frozenBatchG F S s)) ≤ CSig := by
    intro s
    have hsq : fro (mean P (frozenBatchG F S s)) ^ 2 ≤ CSig ^ 2 := by
      calc _ ≤ opNorm F.C.Sout * opNorm F.C.Sin := tr_opNorm_mean_sq F S s
        _ ≤ CSig * CSig := mul_le_mul hCout hCin (tr_opNorm_nonneg _) hC0
        _ = CSig ^ 2 := by ring
    have hnn : 0 ≤ fro (mean P (frozenBatchG F S s)) := by unfold fro; exact Real.sqrt_nonneg _
    nlinarith [hsq, hnn, hC0]
  refine ⟨hfn (t + 1), ?_⟩
  rw [lem_app_setup_gaussian_moments_v F S]
  have hB : (0 : ℝ) < (B : ℝ) := by exact_mod_cast F.hB
  have hT1 : 0 ≤ Matrix.trace F.C.Sout := Matrix.PosSemidef.trace_nonneg F.C.psdOut
  have hT2 : 0 ≤ Matrix.trace F.C.Sin := Matrix.PosSemidef.trace_nonneg F.C.psdIn
  have hfA : fro (Matrix.transpose F.A) ^ 2 = 1 := by
    rw [← tr_tt_eq, Matrix.transpose_transpose, Matrix.trace_mul_comm, tr_tt_eq, F.hA, one_pow]
  have b1 : Matrix.trace F.C.Sout ≤ (m : ℝ) * CSig := by
    have h := tr_quad_le F.C.Sout (1 : Mat m m)
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, tr_fro_one] at h
    have := mul_le_mul_of_nonneg_right hCout (Nat.cast_nonneg (α := ℝ) m)
    linarith
  have b2 : Matrix.trace F.C.Sin ≤ (n : ℝ) * CSig := by
    have h := tr_quad_le F.C.Sin (1 : Mat n n)
    simp only [Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, tr_fro_one] at h
    have := mul_le_mul_of_nonneg_right hCin (Nat.cast_nonneg (α := ℝ) n)
    linarith
  have b3 : Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A)) ≤ CSig := by
    have e3 : Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A))
        = Matrix.trace (Matrix.transpose F.A * F.C.Sout * F.A) := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have h := tr_quad_le F.C.Sout F.A
    rw [F.hA, one_pow, mul_one] at h
    rw [e3]
    linarith
  have b4 : Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A)) ≤ CSig := by
    have e4 : Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A))
        = Matrix.trace (Matrix.transpose (Matrix.transpose F.A) * F.C.Sin * Matrix.transpose F.A) := by
      rw [Matrix.transpose_transpose, ← Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
    have h := tr_quad_le F.C.Sin (Matrix.transpose F.A)
    rw [hfA, mul_one] at h
    rw [e4]
    linarith
  have hM2 : fro (mean P (frozenBatchG F S 0)) ^ 2 ≤ CSig ^ 2 :=
    pow_le_pow_left₀ (by unfold fro; exact Real.sqrt_nonneg _) (hfn 0) 2
  have hA1 : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin ≤ ((m : ℝ) * CSig) * ((n : ℝ) * CSig) :=
    mul_le_mul b1 b2 hT2 (mul_nonneg (Nat.cast_nonneg m) hC0)
  have hA2 : Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A)) * Matrix.trace F.C.Sin
      ≤ CSig * ((n : ℝ) * CSig) :=
    calc _ ≤ CSig * Matrix.trace F.C.Sin := mul_le_mul_of_nonneg_right b3 hT2
      _ ≤ CSig * ((n : ℝ) * CSig) := mul_le_mul_of_nonneg_left b2 hC0
  have hA3 : Matrix.trace F.C.Sout * Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A))
      ≤ ((m : ℝ) * CSig) * CSig :=
    calc _ ≤ Matrix.trace F.C.Sout * CSig := mul_le_mul_of_nonneg_left b4 hT1
      _ ≤ ((m : ℝ) * CSig) * CSig := mul_le_mul_of_nonneg_right b1 hC0
  have hX : Matrix.trace F.C.Sout * Matrix.trace F.C.Sin
      + 2 * Matrix.trace (F.C.Sout * (F.A * Matrix.transpose F.A)) * Matrix.trace F.C.Sin
      + 2 * Matrix.trace F.C.Sout * Matrix.trace (F.C.Sin * (Matrix.transpose F.A * F.A))
      + 3 * (fro (mean P (frozenBatchG F S 0))) ^ 2
      ≤ CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) := by
    nlinarith [hA1, hA2, hA3, hM2]
  calc _ ≤ (1 / (B : ℝ)) * (CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3)) :=
        mul_le_mul_of_nonneg_left hX (by positivity)
    _ = CSig ^ 2 * ((m : ℝ) * n + 2 * m + 2 * n + 3) / (B : ℝ) := by ring

end Muon.Setup
