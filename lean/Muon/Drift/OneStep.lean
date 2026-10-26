import Muon.Drift.Mean
import Muon.Setup.Regime
import Muon.Setup.Basic

/-!
# Muon.Drift: one-step risk drift and the half-anisotropic row drift (work package L-C.11)

Interface draft (statements only; each `_weights` proof is `sorry`, each EMA record is a term
over its `_weights` helper) for `prop:app-drift-onestep` and clause (ii) of
`cor:app-drift-halfaniso` of `sections/03-drift/CARD.md` §3, snapshot `cr-2026-10-23`.

Not restated here (owned by L-C.4, `Kernel.lean`): `cor:app-drift-halfaniso`(i), (iii), (iv).
The alias `rem:app-drift-halfaniso` maps to the same declarations (`cor_app_drift_halfaniso_ii`
for clause (ii)).

Representation choices (see the docstrings):
* Each record is a `_weights` declaration for a general `WeightClass w` (card rule (a)); the
  EMA record is a term-proved instance at `emaW R.β` (`emaW_weightClass_regime`, `Mean.lean`).
* Regime sequences carry `Ω : ℕ → Type`, indexed by `k`; the statements are finite-`B`, so
  there is no limit in `k`.
* The frozen-state state `Δ_t` enters as data `Dt` with `F.A = Ahat F.C (Dt)` and
  `riskSigma F.C (Dt) > 0` (as in `Mean.lean`). `ℛ(Δ⁺)` is `riskSigma` of the random matrix
  `Δ⁺ = Dt - lr · Q_ϱ(M_t)` (`WeightedBuf` is `M_t`), i.e. `½‖Δ⁺‖²_Σ` (card §6.9).
* The ridge `ϱ` ranges over `[ϱ₋, ϱ₊]` for both the identity and the bound (card §6.9: the
  ridge is implicit in the interval). Every `⨆` in the bound sits
  under a `BddAbove` conjunct (junk-value rule).
* Integrals appearing in the identity carry `Integrable` conjuncts, because the source writes
  them as expectations, which presuppose existence, and a non-integrable Bochner integral is `0`.
* The quadratic-term bound of the commentary after `prop:app-drift-onestep` (l.216-218) is not a
  conjunct of the record; it is the separate helper `drift_onestep_quadratic_bound_weights`.
-/
set_option linter.style.longLine false
open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv
namespace Muon.Drift

section OsHelpers
variable {m n B : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma os_borel (m n : ℕ) : BorelSpace (Mat m n) :=
  inferInstanceAs (BorelSpace (Fin m → Fin n → ℝ))

private lemma os_sc (m n : ℕ) : SecondCountableTopology (Mat m n) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))

private lemma os_batch_meas (F : FrozenParams m n B) (S : FrozenSamples P m n B) (s : ℤ) :
    Measurable (frozenBatchG F S s) := by
  haveI := os_borel m n
  haveI := os_sc m n
  unfold frozenBatchG
  refine Measurable.const_smul ?_ ((B : ℝ))⁻¹
  refine Finset.measurable_sum _ fun a _ => ?_
  have hc : Continuous (fun p : Vec m × Vec n =>
      (dotProduct p.1 (Matrix.mulVec F.A p.2)) • (rOut F.C * outer p.1 p.2 * rIn F.C)) := by
    fun_prop
  exact hc.measurable.comp (S.meas s a)

private lemma os_buf_meas (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) := os_sc m n
  unfold WeightedBuf
  exact Measurable.tsum fun j => (os_batch_meas F S (t + 1 - (j : ℤ))).const_smul (w j)

private lemma os_Q_meas {ϱ : ℝ} (hϱ : 0 ≤ ϱ) : Measurable (fun K : Mat m n => Q ϱ K) :=
  (measurable_Q (m := m) (n := n)).comp
    ((measurable_const (a := (⟨ϱ, hϱ⟩ : Set.Ici (0 : ℝ)))).prodMk measurable_id)

private lemma os_abs_entry_le_fro (K : Mat m n) (i : Fin m) (j : Fin n) :
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

private lemma os_fro_nn (K : Mat m n) : 0 ≤ fro K := Real.sqrt_nonneg _

private lemma os_fro_Q_le {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (K : Mat m n) :
    fro (Q ϱ K) ≤ Real.sqrt ((min m n : ℕ) : ℝ) := by
  obtain ⟨-, h2, h3, -⟩ := lem_app_setup_filter_i ϱ hϱ K
  have : fro (Q ϱ K) ^ 2 ≤ ((min m n : ℕ) : ℝ) := h2.trans (by exact_mod_cast h3)
  exact Real.le_sqrt_of_sq_le this

private lemma os_pair_bound (C : Covariances m n) (D : ℝ) :
    ∃ K : ℝ, ∀ V W : Mat m n, (∀ i j, |V i j| ≤ D) → (∀ i j, |W i j| ≤ D) →
      |pairSigma C V W| ≤ K := by
  set T : Set (Mat m n) := Set.pi univ (fun _ => Set.pi univ fun _ => Icc (-D) D) with hT
  have hTc : IsCompact T := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have hcont : Continuous (fun p : Mat m n × Mat m n => pairSigma C p.1 p.2) := by
    unfold pairSigma
    fun_prop
  obtain ⟨K, hK⟩ := (hTc.prod hTc).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨K, fun V W hV hW => ?_⟩
  have hmem : ∀ X : Mat m n, (∀ i j, |X i j| ≤ D) → X ∈ T := fun X hX => by
    intro i _ j _
    have := hX i j
    exact ⟨by linarith [neg_abs_le (X i j)], by linarith [le_abs_self (X i j)]⟩
  simpa using hK (V, W) ⟨hmem V hV, hmem W hW⟩

private lemma os_pair_symm (C : Covariances m n) (V W : Mat m n) :
    pairSigma C V W = pairSigma C W V := by
  have h1 : C.Sout.transpose = C.Sout := by
    have := C.psdOut.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have h2 : C.Sin.transpose = C.Sin := by
    have := C.psdIn.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  unfold pairSigma
  rw [← Matrix.trace_transpose]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, h1, h2]
  simp only [Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm C.Sout]
  simp only [Matrix.mul_assoc]

private lemma os_pair_expand (C : Covariances m n) (D Q : Mat m n) (l : ℝ) :
    pairSigma C (D - l • Q) (D - l • Q) =
      pairSigma C D D - 2 * l * pairSigma C D Q + l ^ 2 * pairSigma C Q Q := by
  have hs := os_pair_symm C Q D
  unfold pairSigma at hs ⊢
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_sub, Matrix.trace_smul, smul_eq_mul]
  rw [hs]
  ring

private lemma os_pair_entries (C : Covariances m n) (D Q : Mat m n) :
    pairSigma C D Q = ∑ i, ∑ j, (C.Sout * D * C.Sin) i j * Q i j := by
  have key : ∀ A : Mat m n, (A * Qᵀ).trace = ∑ i, ∑ j, A i j * Q i j := by
    intro A
    simp [Matrix.trace, Matrix.mul_apply]
  unfold pairSigma
  rw [← key]

private lemma os_mean_pair [IsProbabilityMeasure P] (C : Covariances m n) (D : Mat m n)
    (X : Ω → Mat m n) (hX : ∀ i j, Integrable (fun ω => X ω i j) P) :
    ∫ ω, pairSigma C D (X ω) ∂P = pairSigma C D (Muon.mean P X) := by
  simp only [os_pair_entries]
  generalize C.Sout * D * C.Sin = A
  have hI : ∀ i, Integrable (fun ω => ∑ j, A i j * X ω i j) P := fun i =>
    integrable_finsetSum Finset.univ fun j _ => (hX i j).const_mul (A i j)
  refine (integral_finsetSum Finset.univ (fun i _ => hI i)).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (integral_finsetSum Finset.univ (fun j _ => (hX i j).const_mul (A i j))).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul]
  simp [Muon.mean]

open scoped MatrixOrder in
private lemma os_cEG {Fp : FrozenParams m n B} {Dt : Mat m n}
    (hDt : Fp.A = Ahat Fp.C Dt) (hR : 0 < riskSigma Fp.C Dt) :
    Real.sqrt (2 * riskSigma Fp.C Dt) • EG Fp = Fp.C.Sout * Dt * Fp.C.Sin := by
  have hc : Real.sqrt (2 * riskSigma Fp.C Dt) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  have h1 : rOut Fp.C * rOut Fp.C = Fp.C.Sout :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr Fp.C.psdOut)
  have h2 : rIn Fp.C * rIn Fp.C = Fp.C.Sin :=
    CFC.sqrt_mul_sqrt_self _ (Matrix.nonneg_iff_posSemidef.mpr Fp.C.psdIn)
  unfold EG
  rw [hDt]
  unfold Ahat Arot
  rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  calc rOut Fp.C * (rOut Fp.C * Dt * rIn Fp.C) * rIn Fp.C
      = (rOut Fp.C * rOut Fp.C) * Dt * (rIn Fp.C * rIn Fp.C) := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, h2]

private lemma os_tr {Fp : FrozenParams m n B} {Dt : Mat m n}
    (hDt : Fp.A = Ahat Fp.C Dt) (hR : 0 < riskSigma Fp.C Dt) (E : Mat m n) :
    Real.sqrt (2 * riskSigma Fp.C Dt) * (EG Fp * Eᵀ).trace = pairSigma Fp.C Dt E := by
  unfold pairSigma
  rw [← os_cEG hDt hR, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

open scoped Matrix.Norms.L2Operator in
private lemma os_eig_le {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (x : Fin p → ℝ) (μ : ℝ)
    (hx : ∑ a, x a * x a = 1) (hA : A *ᵥ x = μ • x) : μ ≤ opNorm A := by
  rw [opNorm_eq_norm]
  have h1 := Matrix.l2_opNorm_mulVec A ((EuclideanSpace.equiv (Fin p) ℝ).symm x)
  have hX : ‖(EuclideanSpace.equiv (Fin p) ℝ).symm x‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [EuclideanSpace.equiv, Real.norm_eq_abs, sq_abs]
    change √(∑ a, x a ^ 2) = 1
    simp only [sq]
    rw [hx, Real.sqrt_one]
  have hAx : (EuclideanSpace.equiv (Fin p) ℝ).symm (A *ᵥ ((EuclideanSpace.equiv (Fin p) ℝ).symm x)) =
      μ • (EuclideanSpace.equiv (Fin p) ℝ).symm x := by
    ext i
    change (A *ᵥ x) i = μ * x i
    rw [hA]; rfl
  rw [hAx, norm_smul, hX] at h1
  simp only [mul_one, Real.norm_eq_abs] at h1
  exact le_trans (le_abs_self μ) h1

private lemma os_mu_le {C : Covariances m n} (SD : SpectralData C) (i : Fin m) (c : ℝ)
    (h : opNorm C.Sout ≤ c) : SD.μ i ≤ c :=
  (os_eig_le C.Sout (SD.u i) (SD.μ i) (sum_col_sq_eq_one SD.uOut SD.huOut i) (eig_u SD i)).trans h

private lemma os_lam_le {C : Covariances m n} (SD : SpectralData C) (j : Fin n) (c : ℝ)
    (h : opNorm C.Sin ≤ c) : SD.lam j ≤ c :=
  (os_eig_le C.Sin (SD.v j) (SD.lam j) (sum_col_sq_eq_one SD.vIn SD.hvIn j) (eig_v SD j)).trans h


private lemma os_cs (μ : Fin m → ℝ) (lam : Fin n → ℝ) (hμ : ∀ i, 0 ≤ μ i) (hl : ∀ j, 0 ≤ lam j)
    (c : ℝ) (hc : 0 ≤ c) (hb : ∀ i j, μ i * lam j ≤ c ^ 2) (a e : Fin m → Fin n → ℝ) :
    |∑ i, ∑ j, μ i * lam j * a i j * e i j| ≤
      Real.sqrt (∑ i, ∑ j, μ i * lam j * (a i j * a i j)) * c * Real.sqrt (∑ i, ∑ j, e i j ^ 2) := by
  have hw : ∀ i j, 0 ≤ μ i * lam j := fun i j => mul_nonneg (hμ i) (hl j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => Real.sqrt (μ p.1 * lam p.2) * a p.1 p.2) (fun p => Real.sqrt (μ p.1 * lam p.2) * e p.1 p.2)
  have hA : ∑ p : Fin m × Fin n, (Real.sqrt (μ p.1 * lam p.2) * a p.1 p.2) *
      (Real.sqrt (μ p.1 * lam p.2) * e p.1 p.2) = ∑ i, ∑ j, μ i * lam j * a i j * e i j := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have := Real.mul_self_sqrt (hw i j)
    calc _ = (Real.sqrt (μ i * lam j) * Real.sqrt (μ i * lam j)) * a i j * e i j := by ring
      _ = _ := by rw [this]
  have hB : ∑ p : Fin m × Fin n, (Real.sqrt (μ p.1 * lam p.2) * a p.1 p.2) ^ 2 =
      ∑ i, ∑ j, μ i * lam j * (a i j * a i j) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw i j)]; ring
  have hC : ∑ p : Fin m × Fin n, (Real.sqrt (μ p.1 * lam p.2) * e p.1 p.2) ^ 2 ≤
      c ^ 2 * ∑ i, ∑ j, e i j ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [mul_pow, Real.sq_sqrt (hw i j)]
    exact mul_le_mul_of_nonneg_right (hb i j) (sq_nonneg _)
  rw [hA, hB] at hcs
  have hA0 : 0 ≤ ∑ i, ∑ j, μ i * lam j * (a i j * a i j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => mul_nonneg (hw i j) (mul_self_nonneg _)
  have h2 : (∑ i, ∑ j, μ i * lam j * a i j * e i j) ^ 2 ≤
      (∑ i, ∑ j, μ i * lam j * (a i j * a i j)) * (c ^ 2 * ∑ i, ∑ j, e i j ^ 2) :=
    hcs.trans (mul_le_mul_of_nonneg_left hC hA0)
  have h3 := Real.abs_le_sqrt h2
  refine h3.trans (le_of_eq ?_)
  rw [Real.sqrt_mul hA0, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  ring


private lemma os_pair_meas {α : Type*} [MeasurableSpace α] (C : Covariances m n)
    (f g : α → Mat m n) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => pairSigma C (f x) (g x)) := by
  haveI := os_borel m n
  haveI := os_sc m n
  have hcont : Continuous (fun p : Mat m n × Mat m n => pairSigma C p.1 p.2) := by
    unfold pairSigma
    fun_prop
  have h := (hcont.measurable).comp (hf.prodMk hg)
  exact h

private lemma os_pair_integrable [IsProbabilityMeasure P] (C : Covariances m n)
    (X Y : Ω → Mat m n) (hX : Measurable X) (hY : Measurable Y) (D : ℝ)
    (hXD : ∀ ω i j, |X ω i j| ≤ D) (hYD : ∀ ω i j, |Y ω i j| ≤ D) :
    Integrable (fun ω => pairSigma C (X ω) (Y ω)) P := by
  obtain ⟨K, hK⟩ := os_pair_bound C D
  exact Integrable.of_bound (C := K) (os_pair_meas C X Y hX hY).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hK _ _ (hXD ω) (hYD ω))

private lemma os_entry_integrable [IsProbabilityMeasure P] (X : Ω → Mat m n) (hX : Measurable X)
    (D : ℝ) (hD : ∀ ω i j, |X ω i j| ≤ D) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => X ω i j) P :=
  Integrable.of_bound (C := D)
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hX)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hD ω i j)



private lemma os_mean_dot [IsProbabilityMeasure P] (X : Ω → Mat m n)
    (hX : ∀ i j, Integrable (fun ω => X ω i j) P) (x : Fin m → ℝ) (y : Fin n → ℝ) :
    ∫ ω, dotProduct x (X ω *ᵥ y) ∂P = dotProduct x (Muon.mean P X *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec]
  have hI : ∀ a, Integrable (fun ω => x a * ∑ b, X ω a b * y b) P := fun a =>
    (integrable_finsetSum Finset.univ fun b _ => (hX a b).mul_const (y b)).const_mul (x a)
  refine (integral_finsetSum Finset.univ (fun a _ => hI a)).trans ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_const_mul]
  congr 1
  refine (integral_finsetSum Finset.univ (fun b _ => (hX a b).mul_const (y b))).trans ?_
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [integral_mul_const]
  simp [Muon.mean]

private lemma os_Q_entry_int [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (i : Fin m) (j : Fin n) :
    Integrable (fun ω => Q ϱ (WeightedBuf w F S t ω) i j) P :=
  os_entry_integrable (fun ω => Q ϱ (WeightedBuf w F S t ω))
    ((os_Q_meas hϱ).comp (os_buf_meas w F S t)) _
    (fun ω i j => (os_abs_entry_le_fro _ i j).trans (os_fro_Q_le hϱ _)) i j

private lemma os_le_biSup {f : ℝ → ℝ} {s : Set ℝ} (hb : BddAbove (f '' s)) {x : ℝ} (hx : x ∈ s) :
    f x ≤ ⨆ y ∈ s, f y := by
  obtain ⟨M, hM⟩ := hb
  have hbd : BddAbove (range fun y => ⨆ (_ : y ∈ s), f y) := by
    refine ⟨max M 0, ?_⟩
    rintro _ ⟨y, rfl⟩
    beta_reduce
    by_cases hy : y ∈ s
    · rw [ciSup_pos hy]
      exact (hM ⟨y, hy, rfl⟩).trans (le_max_left _ _)
    · haveI : IsEmpty (y ∈ s) := ⟨hy⟩
      rw [Real.iSup_of_isEmpty]
      exact le_max_right _ _
  calc f x = ⨆ (_ : x ∈ s), f x := (ciSup_pos (f := fun _ : x ∈ s => f x) hx).symm
    _ ≤ ⨆ y, ⨆ (_ : y ∈ s), f y := le_ciSup (f := fun y => ⨆ (_ : y ∈ s), f y) hbd x

private lemma os2_fro_nn {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma os2_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  exact Finset.sum_comm

private lemma os2_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  open scoped Matrix.Norms.L2Operator in
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma os2_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm
  exact norm_nonneg _

private lemma os2_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

private lemma os2_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
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
    rw [os2_fro_sq, mul_pow, os2_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (os2_fro_nn _) (mul_nonneg (os2_opNorm_nonneg M) (os2_fro_nn N))
    two_ne_zero).mp hfro

private lemma os2_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := os2_fro_mul_le_left Nᵀ Mᵀ
  rw [os2_opNorm_transpose, os2_fro_transpose, ← Matrix.transpose_mul, os2_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

private lemma os2_trace_mul_transpose_le {m n : ℕ} (X C : Mat m n) :
    |Matrix.trace (X * Cᵀ)| ≤ fro X * fro C := by
  have htr : Matrix.trace (X * Cᵀ) = ∑ p : Fin m × Fin n, X p.1 p.2 * C p.1 p.2 := by
    simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  rw [htr]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin m × Fin n))
    (fun p => X p.1 p.2) (fun p => C p.1 p.2)
  have hX : ∑ p : Fin m × Fin n, X p.1 p.2 ^ 2 = fro X ^ 2 := by
    rw [os2_fro_sq, Fintype.sum_prod_type]
  have hC : ∑ p : Fin m × Fin n, C p.1 p.2 ^ 2 = fro C ^ 2 := by
    rw [os2_fro_sq, Fintype.sum_prod_type]
  rw [hX, hC] at cs
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (mul_nonneg (os2_fro_nn X) (os2_fro_nn C))
    two_ne_zero).mp ?_
  rw [sq_abs, mul_pow]
  exact cs


/-- Pairing bound `|⟨V, W⟩_Σ| ≤ CSig² ‖V‖_F ‖W‖_F` when `‖Σ_out‖, ‖Σ_in‖ ≤ CSig`. -/
private lemma os2_pS_le {m n : ℕ} (C : Covariances m n) (CSig : ℝ)
    (hO : opNorm C.Sout ≤ CSig) (hI : opNorm C.Sin ≤ CSig) (V W : Mat m n) :
    |Muon.Setup.pairSigma C V W| ≤ CSig ^ 2 * (fro V * fro W) := by
  have hCS : 0 ≤ CSig := (os2_opNorm_nonneg _).trans hO
  have h1 : fro (C.Sout * V * C.Sin) ≤ CSig * fro V * CSig := by
    calc fro (C.Sout * V * C.Sin) ≤ fro (C.Sout * V) * opNorm C.Sin := os2_fro_mul_le_right _ _
      _ ≤ (opNorm C.Sout * fro V) * opNorm C.Sin :=
          mul_le_mul_of_nonneg_right (os2_fro_mul_le_left _ _) (os2_opNorm_nonneg _)
      _ ≤ (CSig * fro V) * CSig :=
          mul_le_mul (mul_le_mul_of_nonneg_right hO (os2_fro_nn _)) hI (os2_opNorm_nonneg _)
            (mul_nonneg hCS (os2_fro_nn _))
      _ = CSig * fro V * CSig := rfl
  have h2 := os2_trace_mul_transpose_le (C.Sout * V * C.Sin) W
  unfold Muon.Setup.pairSigma
  calc |Matrix.trace (C.Sout * V * C.Sin * Wᵀ)| ≤ fro (C.Sout * V * C.Sin) * fro W := h2
    _ ≤ (CSig * fro V * CSig) * fro W := mul_le_mul_of_nonneg_right h1 (os2_fro_nn _)
    _ = CSig ^ 2 * (fro V * fro W) := by ring

end OsHelpers

/-- `prop:app-drift-onestep`, snapshot `cr-2026-10-23`. One-step risk drift in the frozen state, general weight class `w` (`_weights` helper): the identity, the integrability of its two expectations, and the deterministic-equivalent bound with `ε_B`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[One-step risk drift in the frozen state]\label{prop:app-drift-onestep}
Under \cref{assum:app-setup-regime}, let $\lr\ge0$ be deterministic and put
$\Delta^+\defeq\Dt-\lr\,\Gtilde$ with $\Gtilde=\Qridge\ridge(\Mt)$. Then
\begin{equation}\label{eqn:app-drift-onestep}
\EE\big[\cR(\Delta^+)\big]-\cR(t)=-\lr\,\sqrt{2\cR(t)}\,\big\langle\EE\Gt,\EE\Gtilde\big\rangle+\frac{\lr^2}{2}\,\EE\norm{\Gtilde}_\Sigma^2 ,
\end{equation}
and the linear term satisfies
\begin{equation}\label{eqn:app-drift-onestep-de}
\Big|\sqrt{2\cR(t)}\,\big\langle\EE\Gt,\EE\Gtilde\big\rangle-\frac{1}{\sqrt{\cR(t)}}\sum_{i,j}\mu_i\lambda_j\,\mathfrak d_{ij}\,\CMscr Q_{ij}(t)\Big|
\le\sqrt{2\cR(t)}\,C_\Sigma\,\varepsilon_B .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_drift_onestep_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k))
    (lr : ℕ → ℝ) (hlr : ∀ k, 0 ≤ lr k) :
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      Integrable (fun ω => riskSigma (R.F k).C (Dt k - lr k • Q ϱ (WeightedBuf w (R.F k) (S k) t ω))) (P k) ∧
      Integrable (fun ω => pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
        (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))) (P k) ∧
      (∫ ω, riskSigma (R.F k).C (Dt k - lr k • Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) ∂(P k)) -
          riskSigma (R.F k).C (Dt k) =
        -(lr k * Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * (EG (R.F k) * (EQ w (R.F k) (S k) t ϱ)ᵀ).trace) +
          (lr k ^ 2 / 2) * (∫ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
            (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) ∂(P k))) ∧
    (∀ k, BddAbove ((fun ϱ => fro (EQ w (R.F k) (S k) t ϱ -
        Gbar w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      |Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * (EG (R.F k) * (EQ w (R.F k) (S k) t ϱ)ᵀ).trace -
          1 / Real.sqrt (riskSigma (R.F k).C (Dt k)) *
            (∑ i : Fin (R.m k), ∑ j : Fin (R.n k), (SD k).μ i * (SD k).lam j *
              kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) *
                modeQ (SD k) (Dt k) i j)| ≤
        Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * R.CSig *
          epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) := by
  have hmean := thm_app_drift_mean_weights R P S t w hw
  have hker := cor_app_drift_kernel_i_weights R P S t w hw SD Dt hDt hRt
  refine ⟨?_, hmean.2.1, ?_⟩
  · intro k ϱ hϱ
    have hϱ0 : 0 ≤ ϱ := R.hϱ.1.le.trans hϱ.1
    haveI := os_borel (R.m k) (R.n k)
    haveI := os_sc (R.m k) (R.n k)
    set Qf : Ω k → Mat (R.m k) (R.n k) := fun ω => Q ϱ (WeightedBuf w (R.F k) (S k) t ω) with hQf
    have hQm : Measurable Qf := (os_Q_meas hϱ0).comp (os_buf_meas w _ _ t)
    set s := Real.sqrt ((min (R.m k) (R.n k) : ℕ) : ℝ) with hs
    have hQb : ∀ ω i j, |Qf ω i j| ≤ s := fun ω i j =>
      (os_abs_entry_le_fro _ i j).trans (os_fro_Q_le hϱ0 _)
    set X : Ω k → Mat (R.m k) (R.n k) := fun ω => Dt k - lr k • Qf ω with hX
    have hXm : Measurable X := by
      have hc : Continuous (fun K : Mat (R.m k) (R.n k) => Dt k - lr k • K) := by fun_prop
      exact hc.measurable.comp hQm
    have hXb : ∀ ω i j, |X ω i j| ≤ fro (Dt k) + |lr k| * s := fun ω i j => by
      simp only [hX, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      calc |Dt k i j - lr k * Qf ω i j| ≤ |Dt k i j| + |lr k * Qf ω i j| := abs_sub _ _
        _ ≤ fro (Dt k) + |lr k| * s := by
          rw [abs_mul]
          exact add_le_add (os_abs_entry_le_fro _ i j) (mul_le_mul_of_nonneg_left (hQb ω i j) (abs_nonneg _))
    have hI1 : Integrable (fun ω => pairSigma (R.F k).C (X ω) (X ω)) (P k) :=
      os_pair_integrable _ X X hXm hXm _ hXb hXb
    have hI2 : Integrable (fun ω => pairSigma (R.F k).C (Qf ω) (Qf ω)) (P k) :=
      os_pair_integrable _ Qf Qf hQm hQm s hQb hQb
    have hI3 : Integrable (fun ω => pairSigma (R.F k).C (Dt k) (Qf ω)) (P k) :=
      os_pair_integrable _ (fun _ => Dt k) Qf measurable_const hQm (max (fro (Dt k)) s)
        (fun _ i j => (os_abs_entry_le_fro _ i j).trans (le_max_left _ _))
        (fun ω i j => (hQb ω i j).trans (le_max_right _ _))
    have hQi : ∀ i j, Integrable (fun ω => Qf ω i j) (P k) :=
      os_entry_integrable Qf hQm s hQb
    refine ⟨hI1.div_const 2, hI2, ?_⟩
    have hpt : (fun ω => riskSigma (R.F k).C (X ω)) = fun ω =>
        riskSigma (R.F k).C (Dt k) - lr k * pairSigma (R.F k).C (Dt k) (Qf ω) +
          lr k ^ 2 / 2 * pairSigma (R.F k).C (Qf ω) (Qf ω) := by
      funext ω
      simp only [riskSigma, hX]
      rw [os_pair_expand]
      ring
    have hmp := os_mean_pair (R.F k).C (Dt k) Qf hQi
    have htr := os_tr (hDt k) (hRt k) (EQ w (R.F k) (S k) t ϱ)
    have hEQ : Muon.mean (P k) Qf = EQ w (R.F k) (S k) t ϱ := rfl
    rw [hEQ] at hmp
    have hJ : Integrable (fun ω => riskSigma (R.F k).C (Dt k) - lr k * pairSigma (R.F k).C (Dt k) (Qf ω)) (P k) :=
      (integrable_const _).sub (hI3.const_mul _)
    have hint : ∫ ω, (riskSigma (R.F k).C (Dt k) - lr k * pairSigma (R.F k).C (Dt k) (Qf ω) +
          lr k ^ 2 / 2 * pairSigma (R.F k).C (Qf ω) (Qf ω)) ∂(P k) =
        riskSigma (R.F k).C (Dt k) - lr k * pairSigma (R.F k).C (Dt k) (EQ w (R.F k) (S k) t ϱ) +
          lr k ^ 2 / 2 * ∫ ω, pairSigma (R.F k).C (Qf ω) (Qf ω) ∂(P k) := by
      rw [integral_add hJ (hI2.const_mul _), integral_sub (integrable_const _) (hI3.const_mul _),
        integral_const, integral_const_mul, integral_const_mul, hmp]
      simp
    rw [hpt, hint, ← htr]
    ring
  · intro k ϱ hϱ
    have hϱ0 : 0 ≤ ϱ := R.hϱ.1.le.trans hϱ.1
    obtain ⟨hk1, hk2, -, hk4, -⟩ := hker
    have hEQ : ∀ i j, dotProduct ((SD k).u i) (EQ w (R.F k) (S k) t ϱ *ᵥ (SD k).v j) =
        ∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k) :=
      fun i j => (os_mean_dot (fun ω => Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
        (os_Q_entry_int w (R.F k) (S k) t hϱ0) _ _).symm
    have htr := os_tr (hDt k) (hRt k) (EQ w (R.F k) (S k) t ϱ)
    set c := Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) with hc
    set a : Fin (R.m k) → Fin (R.n k) → ℝ := fun i j => dotProduct ((SD k).u i) (Dt k *ᵥ (SD k).v j) with ha
    set e : Fin (R.m k) → Fin (R.n k) → ℝ := fun i j =>
      Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j with he
    have hmain : c * (EG (R.F k) * (EQ w (R.F k) (S k) t ϱ)ᵀ).trace -
        1 / Real.sqrt (riskSigma (R.F k).C (Dt k)) *
          (∑ i : Fin (R.m k), ∑ j : Fin (R.n k), (SD k).μ i * (SD k).lam j *
            kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) *
              modeQ (SD k) (Dt k) i j) =
        ∑ i, ∑ j, (SD k).μ i * (SD k).lam j * a i j * e i j := by
      rw [htr, pairSigma_eq_sum (SD k), Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h4 := hk4 k i j ϱ hϱ
      rw [← hEQ i j] at h4
      simp only [ha, he]
      linear_combination ((SD k).μ i * (SD k).lam j) * h4
    have hC0 : 0 ≤ R.CSig := by linarith [R.hC]
    have hbd : ∀ i j, (SD k).μ i * (SD k).lam j ≤ R.CSig ^ 2 := fun i j => by
      have h1 := os_mu_le (SD k) i R.CSig (R.normOut k)
      have h2 := os_lam_le (SD k) j R.CSig (R.normIn k)
      have := mul_le_mul h1 h2 (lam_nonneg (SD k) j) hC0
      nlinarith
    have hcs := os_cs (SD k).μ (SD k).lam (μ_nonneg (SD k)) (lam_nonneg (SD k)) R.CSig hC0 hbd a e
    have hpp : ∑ i, ∑ j, (SD k).μ i * (SD k).lam j * (a i j * a i j) =
        2 * riskSigma (R.F k).C (Dt k) := by
      rw [← pairSigma_eq_sum (SD k) (Dt k) (Dt k)]
      simp only [riskSigma]
      ring
    have hE : Real.sqrt (∑ i, ∑ j, e i j ^ 2) ≤
        epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi := by
      obtain ⟨hb, heq⟩ := hk2 k
      rw [← heq]
      exact os_le_biSup (f := fun ϱ => Real.sqrt (∑ i : Fin (R.m k), ∑ j : Fin (R.n k),
        Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j ^ 2)) hb hϱ
    rw [hmain]
    rw [hpp] at hcs
    calc _ ≤ _ := hcs
      _ ≤ c * R.CSig * epsB w (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi :=
        mul_le_mul_of_nonneg_left hE (mul_nonneg (Real.sqrt_nonneg _) hC0)

/-- `prop:app-drift-onestep`, snapshot `cr-2026-10-23`. One-step risk drift in the frozen state, EMA record (`emaW R.β`, `β` fixed by `R.hβ`). Term-proved instance of `prop_app_drift_onestep_weights`.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{proposition}[One-step risk drift in the frozen state]\label{prop:app-drift-onestep}
Under \cref{assum:app-setup-regime}, let $\lr\ge0$ be deterministic and put
$\Delta^+\defeq\Dt-\lr\,\Gtilde$ with $\Gtilde=\Qridge\ridge(\Mt)$. Then
\begin{equation}\label{eqn:app-drift-onestep}
\EE\big[\cR(\Delta^+)\big]-\cR(t)=-\lr\,\sqrt{2\cR(t)}\,\big\langle\EE\Gt,\EE\Gtilde\big\rangle+\frac{\lr^2}{2}\,\EE\norm{\Gtilde}_\Sigma^2 ,
\end{equation}
and the linear term satisfies
\begin{equation}\label{eqn:app-drift-onestep-de}
\Big|\sqrt{2\cR(t)}\,\big\langle\EE\Gt,\EE\Gtilde\big\rangle-\frac{1}{\sqrt{\cR(t)}}\sum_{i,j}\mu_i\lambda_j\,\mathfrak d_{ij}\,\CMscr Q_{ij}(t)\Big|
\le\sqrt{2\cR(t)}\,C_\Sigma\,\varepsilon_B .
\end{equation}
\end{proposition}
```
-/
theorem prop_app_drift_onestep (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k))
    (lr : ℕ → ℝ) (hlr : ∀ k, 0 ≤ lr k) :
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      Integrable (fun ω => riskSigma (R.F k).C (Dt k - lr k • Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω))) (P k) ∧
      Integrable (fun ω => pairSigma (R.F k).C (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω))
        (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω))) (P k) ∧
      (∫ ω, riskSigma (R.F k).C (Dt k - lr k • Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω)) ∂(P k)) -
          riskSigma (R.F k).C (Dt k) =
        -(lr k * Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * (EG (R.F k) * (EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace) +
          (lr k ^ 2 / 2) * (∫ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω))
            (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω)) ∂(P k))) ∧
    (∀ k, BddAbove ((fun ϱ => fro (EQ (emaW R.β) (R.F k) (S k) t ϱ -
        Gbar (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ)) '' Icc R.ϱlo R.ϱhi)) ∧
    (∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      |Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * (EG (R.F k) * (EQ (emaW R.β) (R.F k) (S k) t ϱ)ᵀ).trace -
          1 / Real.sqrt (riskSigma (R.F k).C (Dt k)) *
            (∑ i : Fin (R.m k), ∑ j : Fin (R.n k), (SD k).μ i * (SD k).lam j *
              kernel (emaW R.β) (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) ((SD k).lam j) *
                modeQ (SD k) (Dt k) i j)| ≤
        Real.sqrt (2 * riskSigma (R.F k).C (Dt k)) * R.CSig *
          epsB (emaW R.β) (R.F k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) R.ϱlo R.ϱhi) :=
  prop_app_drift_onestep_weights R P S t (emaW R.β) (emaW_weightClass_regime R) SD Dt hDt hRt lr hlr

/-- Commentary after `prop:app-drift-onestep` (`sections/03-drift/section.tex` l.216-218, snapshot `cr-2026-10-23`), not a declaration of record of that label. Helper: the quadratic term of the one-step identity is bounded in `Σ`-norm by `C_Σ² min(N_out,N_in) lr²/2`.
Source, verbatim (l.216-218):
```latex
to the drift scale $\lr\sqrt{\cR(t)}$ only; it need not be small in absolute
terms along a sequence of physical states whose risk grows. The quadratic
term is an exact second moment, bounded by $C_\Sigma^2\min(\Nout,\Nin)\lr^2/2$
through \cref{lem:app-setup-filter}(i), and its deterministic equivalent is
the subject of the volatility section.
```
-/
theorem drift_onestep_quadratic_bound_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) (lr : ℕ → ℝ) :
    ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (lr k ^ 2 / 2) * (∫ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
        (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) ∂(P k)) ≤
        (lr k ^ 2 / 2) * (R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ)) := by
  intro k ϱ hϱI
  have hϱ : 0 ≤ ϱ := (R.hϱ.1.le).trans hϱI.1
  have hmeas : Measurable (fun ω => Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) :=
    (os_Q_meas hϱ).comp (os_buf_meas w (R.F k) (S k) t)
  have hbd : ∀ ω i j, |Q ϱ (WeightedBuf w (R.F k) (S k) t ω) i j| ≤
      Real.sqrt ((min (R.m k) (R.n k) : ℕ) : ℝ) :=
    fun ω i j => (os_abs_entry_le_fro _ i j).trans (os_fro_Q_le hϱ _)
  have hint : Integrable (fun ω => pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
      (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))) (P k) :=
    os_pair_integrable (P := P k) (R.F k).C _ _ hmeas hmeas _ hbd hbd
  have hpt : ∀ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
      (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) ≤ R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ) := by
    intro ω
    have h1 := os2_pS_le (R.F k).C R.CSig (R.normOut k) (R.normIn k)
      (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
    have hf := os_fro_Q_le (m := R.m k) (n := R.n k) hϱ (WeightedBuf w (R.F k) (S k) t ω)
    have hmm : fro (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) * fro (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
        ≤ ((min (R.m k) (R.n k) : ℕ) : ℝ) := by
      have := mul_le_mul hf hf (os_fro_nn _) (Real.sqrt_nonneg _)
      rwa [Real.mul_self_sqrt (Nat.cast_nonneg _)] at this
    have hC2 : 0 ≤ R.CSig ^ 2 := sq_nonneg _
    calc _ ≤ |pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
          (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))| := le_abs_self _
      _ ≤ R.CSig ^ 2 * (fro (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) *
          fro (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))) := h1
      _ ≤ R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hmm hC2
  have hI : (∫ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf w (R.F k) (S k) t ω))
      (Q ϱ (WeightedBuf w (R.F k) (S k) t ω)) ∂(P k)) ≤
      R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ) := by
    calc _ ≤ ∫ ω, R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ) ∂(P k) :=
          integral_mono hint (integrable_const _) hpt
      _ = R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ) := by simp
  exact mul_le_mul_of_nonneg_left hI (by positivity)

/-- Commentary after `prop:app-drift-onestep` (`sections/03-drift/section.tex` l.216-218, snapshot `cr-2026-10-23`), not a declaration of record. EMA form (`emaW R.β`) of `drift_onestep_quadratic_bound_weights`, term-proved.
-/
theorem drift_onestep_quadratic_bound (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (lr : ℕ → ℝ) :
    ∀ k, ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (lr k ^ 2 / 2) * (∫ ω, pairSigma (R.F k).C (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω))
        (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω)) ∂(P k)) ≤
        (lr k ^ 2 / 2) * (R.CSig ^ 2 * ((min (R.m k) (R.n k) : ℕ) : ℝ)) :=
  drift_onestep_quadratic_bound_weights R P S t (emaW R.β) (emaW_weightClass_regime R) lr

/-- `cor:app-drift-halfaniso`, snapshot `cr-2026-10-23`. Half-anisotropic input, clause (ii) only (the row drift), general weight class `w` (`_weights` helper). Clauses (i), (iii), (iv) are `Muon.Drift.cor_app_drift_halfaniso_i/_iii/_iv` (L-C.4).
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{corollary}[Half-anisotropic input]\label{cor:app-drift-halfaniso}\label{rem:app-drift-halfaniso}
Under \cref{assum:app-setup-regime}, assume $\Sigmain=\Id_{\Nin}$, let
$\ridge\in[\ridge_-,\ridge_+]$, write $z=\ridge+u^2$, and put
$\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ the kernel is $\mathfrak d_{ij}=\mathfrak d_i$, and
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{z\,\Lw(q(-z))\,\tilde\sigma(-z)\,\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item The row drift of \cref{eqn:app-setup-row} is, with $E_\ridge$ as in
\cref{cor:app-drift-kernel},
\[
\sum_j\cD_{ij}(t)=\frac{\mathfrak d_i}{\sqrt{\cR(t)}}\,\CMscr Q_i(t)+\sum_j(u_i^\T\Dt v_j)(E_\ridge)_{ij}.
\]
\item At $\bmom=0$,
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{\tilde s_1(-z)\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item At $\bmom=0$, if $\zeta\mapsto(\tilde s_1(\zeta)\mu_i-\zeta)^{-1}$ is the
Stieltjes transform of a probability measure $\rho_i$ on $[0,\infty)$, then
\[
\mathfrak d_i=\frac{B}{\sqrt2\,\Nin}\int_{[0,\infty)}\frac{x}{\sqrt{x+\ridge}}\,\rho_i(dx).
\]
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_halfaniso_ii_weights (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (w : ℕ → ℝ) (hw : WeightClass w) (hSin : ∀ k, (R.F k).C.Sin = 1)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k)) :
    ∀ k, ∀ i : Fin (R.m k), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∑ j : Fin (R.n k), (dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
          (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)))) =
        dIdx w (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) (SD k) ϱ i /
            Real.sqrt (riskSigma (R.F k).C (Dt k)) * rowQ (SD k) (Dt k) i +
          ∑ j : Fin (R.n k), dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
            Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j := by
  have hker := cor_app_drift_kernel_i_weights R P S t w hw SD Dt hDt hRt
  intro k i ϱ hϱ
  have hlam : ∀ j, (SD k).lam j = 1 := by
    intro j
    have h1 : (SD k).v j = (SD k).lam j • (SD k).v j := by
      have h := (SD k).eigIn j
      rw [hSin k, Matrix.one_mulVec] at h
      exact h
    have h2 : (SD k).v j ⬝ᵥ (SD k).v j = 1 :=
      sum_col_sq_eq_one (SD k).vIn (SD k).hvIn j
    have h3 := congrArg (fun v => (SD k).v j ⬝ᵥ v) h1
    simp only [dotProduct_smul, smul_eq_mul, h2, mul_one] at h3
    exact h3.symm
  have hrow : rowQ (SD k) (Dt k) i = ∑ j, (dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j)) ^ 2 :=
    lem_app_setup_decomposition_i (SD k) (Dt k) i
  have hj : ∀ j, dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
      (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf w (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)) =
      dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
        (kernel w (specOutFM (R.F k)) (specInFM (R.F k)) ϱ ((SD k).μ i) 1 /
            Real.sqrt (riskSigma (R.F k).C (Dt k)) * dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) +
          Erho w (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j) := by
    intro j
    rw [(hker.1 k i j ϱ hϱ).2, hlam j]
  unfold dIdx
  simp only [hj]
  rw [hrow, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `cor:app-drift-halfaniso`, snapshot `cr-2026-10-23`. Half-anisotropic input, clause (ii), EMA record (`emaW R.β`). Term-proved instance of `cor_app_drift_halfaniso_ii_weights`. The label's alias `rem:app-drift-halfaniso` has the same declaration.
Source, verbatim (`sections/03-drift/section.tex`):
```latex
\begin{corollary}[Half-anisotropic input]\label{cor:app-drift-halfaniso}\label{rem:app-drift-halfaniso}
Under \cref{assum:app-setup-regime}, assume $\Sigmain=\Id_{\Nin}$, let
$\ridge\in[\ridge_-,\ridge_+]$, write $z=\ridge+u^2$, and put
$\mathfrak d_i\defeq\mathfrak d(\mu_i,1)$.
\begin{enumerate}[label=(\roman*)]
\item For every pair $(i,j)$ the kernel is $\mathfrak d_{ij}=\mathfrak d_i$, and
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{z\,\Lw(q(-z))\,\tilde\sigma(-z)\,\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item The row drift of \cref{eqn:app-setup-row} is, with $E_\ridge$ as in
\cref{cor:app-drift-kernel},
\[
\sum_j\cD_{ij}(t)=\frac{\mathfrak d_i}{\sqrt{\cR(t)}}\,\CMscr Q_i(t)+\sum_j(u_i^\T\Dt v_j)(E_\ridge)_{ij}.
\]
\item At $\bmom=0$,
\[
\mathfrak d_i=\frac{\sqrt2\,B}{\pi\,\Nin}\int_0^\infty\frac{\tilde s_1(-z)\mu_i}{z+\tilde s_1(-z)\mu_i}\,du .
\]
\item At $\bmom=0$, if $\zeta\mapsto(\tilde s_1(\zeta)\mu_i-\zeta)^{-1}$ is the
Stieltjes transform of a probability measure $\rho_i$ on $[0,\infty)$, then
\[
\mathfrak d_i=\frac{B}{\sqrt2\,\Nin}\int_{[0,\infty)}\frac{x}{\sqrt{x+\ridge}}\,\rho_i(dx).
\]
\end{enumerate}
\end{corollary}
```
-/
theorem cor_app_drift_halfaniso_ii (R : Muon.Setup.SetupRegime) {Ω : ℕ → Type} [∀ k, MeasurableSpace (Ω k)]
    (P : ∀ k, Measure (Ω k)) [∀ k, IsProbabilityMeasure (P k)]
    (S : ∀ k, FrozenSamples (P k) (R.m k) (R.n k) (R.B k)) (t : ℤ)
    (hSin : ∀ k, (R.F k).C.Sin = 1)
    (SD : ∀ k, SpectralData (R.F k).C) (Dt : ∀ k, Mat (R.m k) (R.n k))
    (hDt : ∀ k, (R.F k).A = Ahat (R.F k).C (Dt k)) (hRt : ∀ k, 0 < riskSigma (R.F k).C (Dt k)) :
    ∀ k, ∀ i : Fin (R.m k), ∀ ϱ ∈ Icc R.ϱlo R.ϱhi,
      (∑ j : Fin (R.n k), (dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
          (∫ ω, dotProduct ((SD k).u i) (Q ϱ (WeightedBuf (emaW R.β) (R.F k) (S k) t ω) *ᵥ (SD k).v j) ∂(P k)))) =
        dIdx (emaW R.β) (R.F k) (specOutFM (R.F k)) (specInFM (R.F k)) (SD k) ϱ i /
            Real.sqrt (riskSigma (R.F k).C (Dt k)) * rowQ (SD k) (Dt k) i +
          ∑ j : Fin (R.n k), dotProduct ((SD k).u i) ((Dt k) *ᵥ (SD k).v j) *
            Erho (emaW R.β) (R.F k) (SD k) (S k) t (specOutFM (R.F k)) (specInFM (R.F k)) ϱ i j :=
  cor_app_drift_halfaniso_ii_weights R P S t (emaW R.β) (emaW_weightClass_regime R) hSin SD Dt hDt hRt

end Muon.Drift
