import Muon.Drift.Coefficients

/-!
# Muon.Drift: covariance of the Gram coefficient and the mixed resolvent (work package L-C.6)

Interface of `lem:app-drift-covariance` (`sections/03-drift/section.tex` l.493–501), snapshot
`cr-2026-10-23`. The statement is the coefficient covariance `𝒞_j` of `Muon.Drift.Defs`
(`eqn:app-drift-Cj`), `Cj`, in the frozen-state model `FrozenParams m n B` / `FrozenSamples P m n B`
with `𝒢_{j1} = sigmaOthers F S t j`.

Two declarations:
* `lem_app_drift_covariance_weights`: the source's claim for a general weight sequence `w` satisfying
  the source's own class `eqn:app-drift-weights` (`0 ≤ w_j ≤ 1`, `∑ w_j ≤ 1`, summable and
  nonnegative). The branch-only "not all zero" condition of `WeightClass` is deliberately not
  imposed: the source's lemma does not state it (card §6.2 is a pending clarifying correction).
* `lem_app_drift_covariance`: the source's literal statement at the EMA weights `emaW β`, `β ∈ [0,1)`,
  with `sw2 = sPow β 2`; a reduction of the general one.

Constants. `∃ C` is placed before all model data (`Ω`, the σ-algebra, `P`, `m n B`, `F`, `S`, `t`, `w`),
depending only on `(s₀, C_Σ, γ⋆)` through the bounds `‖Σ_out‖, ‖Σ_in‖ ≤ C_Σ`, `m, n ≤ γ⋆ B`.
The finite-dimensional hypotheses and `‖Â‖_F = 1` (`F.hA`) are those of `Muon.Drift.Coefficients`.

Junk values. `condExp`, the Bochner integral `Cj` and `tsum` return junk outside their domain. The
per-age bound therefore comes with the integrability of the summand (entrywise), and the summed bound
comes with `Summable`. `s^{3/2}` is written `s * √s` (equal for `s ≥ 0`).
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

noncomputable section

namespace Muon.Drift

/-- The source weight class controls its squared weights. -/
private lemma cv_summable_sq (w : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (hw1 : ∀ j, w j ≤ 1) :
    Summable (fun j => w j ^ 2) := by
  exact Summable.of_nonneg_of_le (fun j => sq_nonneg (w j))
    (fun j => by nlinarith [hw0 j, hw1 j]) hw

/-- Summation of any nonnegative per-age bound with the source weights. -/
private lemma cv_sum_of_sq_bound (w f : ℕ → ℝ) (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (hw1 : ∀ j, w j ≤ 1) (K : ℝ)
    (hf0 : ∀ j, 0 ≤ f j) (hf : ∀ j, f j ≤ K * w j ^ 2) :
    Summable f ∧ (∑' j, f j) ≤ K * sumPow w 2 := by
  have hsq := cv_summable_sq w hw0 hw hw1
  have hmajor := hsq.mul_left K
  have hsum := Summable.of_nonneg_of_le hf0 hf hmajor
  refine ⟨hsum, ?_⟩
  calc (∑' j, f j) ≤ ∑' j, K * w j ^ 2 := hsum.tsum_le_tsum hf hmajor
    _ = K * sumPow w 2 := by rw [tsum_mul_left]; rfl

private lemma cv_sample_measurable {m n B : ℕ} (F : FrozenParams m n B) :
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

private lemma cv_del_measurable {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := cv_sample_measurable F
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

/-- A buffer with a set of slots deleted is measurable without any deleted slot. -/
private lemma cv_masked_buf_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (U : Finset (ℤ × Fin B)) (p : ℤ × Fin B)
    (hp : p ∈ U) :
    Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance]
      (fun ω => ∑' k : ℕ, w k • ((B : ℝ)⁻¹ • ∑ b : Fin B,
        if (t + 1 - (k : ℤ), b) ∈ U then 0
        else sampleTerm F S (t + 1 - (k : ℤ)) b ω)) := by
  classical
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  have hzw : ∀ q : ℤ × Fin B, q ≠ p → Measurable[G] (S.zw q.1 q.2) := by
    intro q hq
    exact (comap_measurable (S.zw q.1 q.2)).mono
      (le_iSup_of_le q (le_iSup_of_le hq le_rfl)) le_rfl
  letI : MeasurableSpace Ω := G
  refine Measurable.tsum fun k => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w k)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : (t + 1 - (k : ℤ), b) ∈ U
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]
    have hne : (t + 1 - (k : ℤ), b) ≠ p := by
      intro he; exact h (he.symm ▸ hp)
    exact (cv_sample_measurable F).comp (hzw _ hne)

/-- Removing one further slot is a finite modification of the buffer series. -/
private lemma cv_masked_delete {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (U : Finset (ℤ × Fin B))
    (k : ℕ) (a : Fin B) (ω : Ω) (hp : (t + 1 - (k : ℤ), a) ∉ U)
    (hsum : Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω))) :
    Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) ∧
    (∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) =
    (∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
      if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
      else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) +
      w k • ((B : ℝ)⁻¹ • sampleTerm F S (t + 1 - (k : ℤ)) a ω) := by
  classical
  let f := fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  let g := fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  let v := w k • ((B : ℝ)⁻¹ • sampleTerm F S (t + 1 - (k : ℤ)) a ω)
  have hterm : ∀ l, f l = g l + if l = k then v else 0 := by
    intro l
    by_cases hl : l = k
    · subst l
      have hbatch : (∑ b : Fin B,
          if (t + 1 - (k : ℤ), b) ∈ U then (0 : Mat m n)
          else sampleTerm F S (t + 1 - (k : ℤ)) b ω) =
          (∑ b : Fin B,
          if (t + 1 - (k : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U then 0
          else sampleTerm F S (t + 1 - (k : ℤ)) b ω) +
            sampleTerm F S (t + 1 - (k : ℤ)) a ω := by
        have he : ∀ b : Fin B,
            (if (t + 1 - (k : ℤ), b) ∈ insert (t + 1 - (k : ℤ), a) U
              then (0 : Mat m n) else sampleTerm F S (t + 1 - (k : ℤ)) b ω) =
            (if (t + 1 - (k : ℤ), b) ∈ U then 0
              else sampleTerm F S (t + 1 - (k : ℤ)) b ω) -
            (if b = a then sampleTerm F S (t + 1 - (k : ℤ)) b ω else 0) := by
          intro b
          by_cases hb : b = a
          · subst b; simp [hp]
          · simp [Finset.mem_insert, Prod.mk.injEq, hb]
        simp_rw [he, Finset.sum_sub_distrib]
        simp
      change _ = _ + if k = k then v else 0
      rw [if_pos rfl]
      dsimp [f, g, v]
      rw [hbatch, smul_add, smul_add]
    · have hne : ∀ b : Fin B,
          (t + 1 - (l : ℤ), b) ≠ (t + 1 - (k : ℤ), a) := by
        intro b he; apply hl
        have he' := congrArg Prod.fst he
        omega
      simp [f, g, hl, Finset.mem_insert, hne]
  have hi : Summable (fun l : ℕ => if l = k then v else 0) :=
    (hasSum_ite_eq k v).summable
  have hg : Summable g := (hsum.sub hi).congr (fun l => by
    change f l - _ = g l
    rw [hterm l, add_sub_cancel_right])
  refine ⟨hg, ?_⟩
  change (∑' l, f l) = (∑' l, g l) + v
  rw [tsum_congr hterm, hg.tsum_add hi, tsum_ite_eq]

open scoped MatrixOrder in
private lemma cv_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
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

private lemma cv_sample {Ω : Type*} [MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
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
    rw [cv_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

/-- The double-deleted buffer is measurable without either removed sample, and adding the
second sample back recovers the distinguished minor almost surely. -/
private lemma cv_double_deletion {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (hw : WeightSeq w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j k : ℕ) (a : Fin B)
    (hne : (t + 1 - (k : ℤ), a) ≠ (t + 1 - (j : ℤ), slotOne F.hB)) :
    ∃ Z : Ω → Mat m n,
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z ∧
      Measurable[sigmaOthers F S t j] Z ∧
      ∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω)) := by
  classical
  let U : Finset (ℤ × Fin B) :=
    insert (t + 1 - (k : ℤ), a) {(t + 1 - (j : ℤ), slotOne F.hB)}
  let Z : Ω → Mat m n := fun ω => ∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
    if (t + 1 - (l : ℤ), b) ∈ U then 0
    else sampleTerm F S (t + 1 - (l : ℤ)) b ω)
  refine ⟨Z, cv_masked_buf_measurable w F S t U _ (Finset.mem_insert_self _ _), ?_, ?_⟩
  · exact cv_masked_buf_measurable w F S t U _
      (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  · filter_upwards [weightedBuf_summable_ae w hw F S] with ω hω
    have hsum0 : Summable (fun l : ℕ => w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
        if (t + 1 - (l : ℤ), b) ∈ (∅ : Finset (ℤ × Fin B)) then 0
        else sampleTerm F S (t + 1 - (l : ℤ)) b ω)) := by
      simpa only [Finset.notMem_empty, ↓reduceIte, ← frozenBatchG_eq_sum] using hω t
    have hsum1 := (cv_masked_delete w F S t ∅ j (slotOne F.hB) ω
      (Finset.notMem_empty _) hsum0).1
    simp only [Finset.insert_empty] at hsum1
    have hdec := (cv_masked_delete w F S t {(t + 1 - (j : ℤ), slotOne F.hB)}
      k a ω (by simpa only [Finset.mem_singleton] using hne) hsum1).2
    have he : delBufAge w F S t j ω =
        ∑' l : ℕ, w l • ((B : ℝ)⁻¹ • ∑ b : Fin B,
          if (t + 1 - (l : ℤ), b) ∈ ({(t + 1 - (j : ℤ), slotOne F.hB)} : Finset (ℤ × Fin B)) then 0
          else sampleTerm F S (t + 1 - (l : ℤ)) b ω) := by
      simp only [delBufAge, WeightedBufDel, Finset.mem_singleton, Prod.mk.injEq]
    rw [he]
    simpa only [cv_sample, smul_smul, Z, U] using hdec

private lemma cv_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
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

private lemma cv_abs_entry_le {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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

private lemma cv_Rts_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rts M s) := by
  have e : (fun M : Mat m n => Rts M s) = fun M => Rs Mᵀ s := by
    funext M; simp [Rts, Rs]
  rw [e]
  exact (cv_Rs_continuous s hs).comp continuous_id.matrix_transpose

private lemma cv_alpha_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha1 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha2 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha3 q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
  have hR := cv_Rs_continuous (m := m) (n := n) s hs
  have hRt := cv_Rts_continuous (m := m) (n := n) s hs
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

/-- The distinguished Gaussian pair is independent of all other samples. -/
private lemma cv_others_indep {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Indep (sigmaOthers F S t j)
      (MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance) P := by
  let X := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)
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

/-- The covariance integrand is integrable at every positive regularization. -/
private lemma cv_integrable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s : ℝ) (hs : 0 < s) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => (phiJ w F S t j s ω - bj w F S t j s) *
      Xs (delBufAge w F S t j ω) s i k) P := by
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM : Measurable (delBufAge w F S t j) :=
    (cv_del_measurable w F S t j).mono hG le_rfl
  have hc : Continuous (fun M : Mat m n => Xs M s) := by
    unfold Xs
    exact (cv_Rs_continuous s hs).matrix_mul continuous_id
  have hm : Measurable (fun ω => Xs (delBufAge w F S t j ω) s i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp (hc.measurable.comp hM))
  have hphi : Integrable (phiJ w F S t j s) P := integrable_condExp
  refine (hphi.sub (integrable_const _)).mul_bdd hm.aestronglyMeasurable
    (c := 1 / (2 * Real.sqrt s)) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  exact (cv_abs_entry_le _ i k).trans ((lem_app_de_resolvent _ s hs).2.2.1)

/-- Once the per-age estimate is supplied, all summation conclusions follow. -/
private lemma cv_covariance_sum {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (s C : ℝ) (hw0 : ∀ j, 0 ≤ w j) (hw : Summable w)
    (hw1 : ∀ j, w j ≤ 1)
    (hper : ∀ j, fro (Cj w F S t j s) ≤
      C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) :
    Summable (fun j => fro (Cj w F S t j s)) ∧
      (∑' j, fro (Cj w F S t j s)) ≤
        C * sumPow w 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
  have h := cv_sum_of_sq_bound w (fun j => fro (Cj w F S t j s)) hw0 hw hw1
    (C / (s * Real.sqrt s * Real.sqrt (B : ℝ))) (fun _ => Real.sqrt_nonneg _)
    (fun j => by simpa only [div_mul_eq_mul_div] using hper j)
  simpa only [div_mul_eq_mul_div] using h

/-- The coefficient conditional expectation is uniformly bounded at each age. -/
private lemma cv_phi_bound (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (w : ℕ → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ w j → w j ≤ 1 → ∀ s : ℝ, s0 ≤ s →
        ∀ᵐ ω ∂P, |phiJ w F S t j s ω| ≤ C * w j ^ 2 / s := by
  obtain ⟨C, hC⟩ := lem_app_drift_coeffmoments 1 le_rfl s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S t j w hSo hSi hm hn hw0 hw1 s hs
  have h := hC Ω m n B P F S t j (delBufAge w F S t j) (w j)
    hSo hSi hm hn hw0 hw1 (cv_del_measurable w F S t j) s hs
  have hbound : ∀ᵐ ω ∂P, condExp (sigmaOthers F S t j) P
      (fun ω => |delAlpha2 w F S t j s ω|) ω ≤ C * w j ^ 2 / s := by
    simpa only [pow_one, ageAlpha2, delAlpha2] using h.2.2.2.2
  exact (abs_condExp_ae_le_condExp_abs (m := sigmaOthers F S t j)
    (delAlpha2 w F S t j s)).trans hbound

/-- The actual deleted-sample coefficient has a finite first moment. -/
private lemma cv_alpha2_integrable {Ω : Type} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s CS γ : ℝ) (hs : 0 < s) (hγ : 0 ≤ γ)
    (hSo : opNorm F.C.Sout ≤ CS) (hSi : opNorm F.C.Sin ≤ CS)
    (hm : (m : ℝ) ≤ γ * B) (hn : (n : ℝ) ≤ γ * B)
    (hw0 : 0 ≤ w j) (hw1 : w j ≤ 1) :
    Integrable (delAlpha2 w F S t j s) P := by
  obtain ⟨C, hC⟩ := lem_app_drift_coeffmoments 1 le_rfl s hs CS γ hγ
  have h := hC Ω m n B P F S t j (delBufAge w F S t j) (w j)
    hSo hSi hm hn hw0 hw1 (cv_del_measurable w F S t j) s le_rfl
  have he : (fun ω => |ageAlpha2 F S t j (delBufAge w F S t j) (w j) s ω| ^ 1) =
      delAlpha2 w F S t j s := by
    funext ω
    rw [pow_one, abs_of_nonneg (h.1 ω)]
    rfl
  exact he ▸ h.2.2.2.1

/-- Freezing identifies the conditional coefficient with the fresh-sample coefficient. -/
private lemma cv_phi_eq_fresh {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s : ℝ) (hs : 0 < s)
    (hI : Integrable (delAlpha2 w F S t j s) P) :
    phiJ w F S t j s =ᵐ[P] fun ω => phiFresh F (delBufAge w F S t j ω) (w j) s := by
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  let f : Mat m n → Vec m × Vec n → ℝ := fun K x =>
    Muon.DetEquiv.alpha2 K (w j * dotProduct x.1 (Matrix.mulVec F.A x.2))
      (momU F.C B x) (momV F.C B x) s
  have hf : Measurable (Function.uncurry f) := by
    have hc : Continuous (fun q : Mat m n × (Vec m × Vec n) =>
        (q.1, w j * dotProduct q.2.1 (Matrix.mulVec F.A q.2.2),
          momU F.C B q.2, momV F.C B q.2)) := by
      unfold momU momV
      fun_prop
    exact ((cv_alpha_continuous s hs).2.1.comp hc).measurable
  have h := Muon.Foundations.freezing_condExp (sigmaOthers F S t j) hG
    (cv_del_measurable w F S t j) (S.meas (t + 1 - (j : ℤ)) (slotOne F.hB))
    (cv_others_indep F S t j) hf hI
  have he : (fun ω => f (delBufAge w F S t j ω)
      (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) ω)) = delAlpha2 w F S t j s := rfl
  rw [he, S.law] at h
  exact h

/-- Assembly of the target at fixed model data from its per-age estimate. -/
private lemma cv_assemble {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (s C : ℝ) (hs : 0 < s) (hw0 : ∀ j, 0 ≤ w j)
    (hw : Summable w) (hw1 : ∀ j, w j ≤ 1)
    (hper : ∀ j, fro (Cj w F S t j s) ≤
      C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) :
    (∀ (j : ℕ) (i : Fin m) (k : Fin n),
      Integrable (fun ω => (phiJ w F S t j s ω - bj w F S t j s) *
        Xs (delBufAge w F S t j ω) s i k) P) ∧
    (∀ j, fro (Cj w F S t j s) ≤
      C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) ∧
    Summable (fun j => fro (Cj w F S t j s)) ∧
    (∑' j, fro (Cj w F S t j s)) ≤
      C * sumPow w 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
  exact ⟨fun j i k => cv_integrable w F S t j s hs i k, hper,
    cv_covariance_sum w F S t s C hw0 hw hw1 hper⟩

/-- Mean of a bounded-Frobenius random matrix: `‖𝔼Y‖_F ≤ K` when `‖Y‖_F ≤ K` a.s. -/
private lemma cv_fro_mean_le {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : Ω → Mat m n)
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

/-- A bounded multiplier gives an unconditional one-slot deletion bound. -/
private lemma cv_one_slot_deletion (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → Measurable[sigmaOthers F S t j] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB))
        inferInstance ⊔ sigmaOthers F S t j] h →
      (∀ ω, |h ω| ≤ D) → ∀ s : ℝ, s0 ≤ s →
        fro (Muon.mean P (fun ω => h ω •
          (Xs (ageBuf F S t j M0 ϖ ω) s - Xs (M0 ω) s))) ≤
          C * D * ϖ / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_multiplier_i s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t j M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD s hs
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hbound := hC Ω m n B P F S t j M0 ϖ D h
    hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD s hs
  have htower : Muon.mean P (fun ω => h ω •
      (Xs (ageBuf F S t j M0 ϖ ω) s - Xs (M0 ω) s)) =
      Muon.mean P (Muon.Foundations.condExpMat (sigmaOthers F S t j) P
        (fun ω => h ω • (Xs (ageBuf F S t j M0 ϖ ω) s - Xs (M0 ω) s))) := by
    ext i k
    simp only [Muon.mean, Matrix.of_apply, Muon.Foundations.condExpMat_apply]
    exact (integral_condExp hG).symm
  rw [htower]
  exact cv_fro_mean_le P _ (fun i k => integrable_condExp) _ hbound

/-- The one-slot bound is valid at every batch slot, by reindexing the independent family. -/
private lemma cv_one_slot_deletion_any (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (j : ℕ) (a : Fin B) (M0 : Ω → Mat m n) (ϖ D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] M0 →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ ω, |h ω| ≤ D) → ∀ s : ℝ, s0 ≤ s →
        fro (Muon.mean P (fun ω => h ω •
          (Xs (M0 ω + (ϖ * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
            Muon.outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω))
              (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) s - Xs (M0 ω) s))) ≤
          C * D * ϖ / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := cv_one_slot_deletion s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t j a M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0 hh hD s hs
  let G := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let p0 : ℤ × Fin B := (t + 1 - (j : ℤ), slotOne F.hB)
  let p : ℤ × Fin B := (t + 1 - (j : ℤ), a)
  let e : (ℤ × Fin B) ≃ (ℤ × Fin B) := Equiv.swap p0 p
  let T : FrozenSamples P m n B := {
    zw := fun r b => S.zw (e (r, b)).1 (e (r, b)).2
    meas := fun r b => S.meas _ _
    indep := S.indep.precomp e.injective
    law := fun r b => S.law _ _ }
  have hep : e p0 = p := Equiv.swap_apply_left p0 p
  have hG : sigmaOthers F T t j = G := by
    change (⨆ (q : ℤ × Fin B) (_ : q ≠ p0),
      MeasurableSpace.comap (S.zw (e q).1 (e q).2) inferInstance) =
      ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    calc
      _ = ⨆ (q : ℤ × Fin B) (_ : e q ≠ p),
          MeasurableSpace.comap (S.zw (e q).1 (e q).2) inferInstance := by
        simp only [← hep, e.injective.ne_iff]
      _ = _ := e.iSup_comp (g := fun q : ℤ × Fin B =>
        ⨆ (_ : q ≠ p), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
  have hsample : T.zw (t + 1 - (j : ℤ)) (slotOne F.hB) =
      S.zw (t + 1 - (j : ℤ)) a := by
    change S.zw (e p0).1 (e p0).2 = _
    rw [hep]
  have hM0' : Measurable[sigmaOthers F T t j] M0 := hG.symm ▸ hM0
  have hh' : Measurable[MeasurableSpace.comap
      (T.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔ sigmaOthers F T t j] h := by
    rw [hsample, hG]
    exact hh
  have hbound := hC Ω m n B P F T t j M0 ϖ D h hSo hSi hm hn hϖ0 hϖ1 hM0' hh' hD s hs
  simpa only [ageBuf, ageD, ageU, ageV, sampleD, resid, hsample] using hbound

/-- The multiplier estimate applies to the actual distinguished minor and its double deletion. -/
private lemma cv_minor_deletion_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ ω, |h ω| ≤ D) → ∀ s : ℝ, s0 ≤ s →
      fro (Muon.mean P (fun ω => h ω •
        (Xs (delBufAge w F S t j ω) s - Xs (Z ω) s))) ≤
        C * D * w k / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := cv_one_slot_deletion_any s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD s hs
  have he : Muon.mean P (fun ω => h ω •
      (Xs (delBufAge w F S t j ω) s - Xs (Z ω) s)) =
      Muon.mean P (fun ω => h ω •
        (Xs (Z ω + (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) s - Xs (Z ω) s)) := by
    ext i r
    apply integral_congr_ae
    filter_upwards [hdec] with ω hω
    simp only [hω]
  rw [he]
  exact hC Ω m n B P F S t k a Z (w k) D h hSo hSi hm hn hw0 hw1 hZ hh hD s hs

/-- The multiplier estimate also accepts almost-sure bounds, using a bounded representative. -/
private lemma cv_minor_deletion_bound_ae (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ᵐ ω ∂P, |h ω| ≤ D) → ∀ s : ℝ, s0 ≤ s →
      fro (Muon.mean P (fun ω => h ω •
        (Xs (delBufAge w F S t j ω) s - Xs (Z ω) s))) ≤
        C * D * w k / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := cv_minor_deletion_bound s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD s hs
  classical
  let h' : Ω → ℝ := fun ω => if |h ω| ≤ D then h ω else 0
  have hD0 : 0 ≤ D := by
    obtain ⟨ω, hω⟩ := hD.exists
    exact (abs_nonneg _).trans hω
  have he : h' =ᵐ[P] h := by
    filter_upwards [hD] with ω hω
    simp only [h', if_pos hω]
  have hh' : Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
      ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h' := by
    letI : MeasurableSpace Ω := MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
      ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    exact Measurable.ite (measurableSet_le hh.abs measurable_const) hh measurable_const
  have hb : ∀ ω, |h' ω| ≤ D := by
    intro ω
    by_cases hω : |h ω| ≤ D
    · simpa only [h', if_pos hω] using hω
    · simpa only [h', if_neg hω, abs_zero] using hD0
  have hbnd := hC Ω m n B P F S w t j k a Z D h' hSo hSi hm hn hw0 hw1 hZ hdec hh' hb s hs
  have hmean : Muon.mean P (fun ω => h' ω •
      (Xs (delBufAge w F S t j ω) s - Xs (Z ω) s)) =
      Muon.mean P (fun ω => h ω •
      (Xs (delBufAge w F S t j ω) s - Xs (Z ω) s)) := by
    ext i r
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    simp only [hω]
  rwa [hmean] at hbnd

private lemma cv_rank_add {k l : ℕ} (A B : Mat k l) : (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  have hle : LinearMap.range (Matrix.mulVecLin (A + B)) ≤
      LinearMap.range (Matrix.mulVecLin A) ⊔ LinearMap.range (Matrix.mulVecLin B) := by
    rw [Matrix.mulVecLin_add]
    rintro _ ⟨x, rfl⟩
    exact Submodule.mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
  exact (Submodule.finrank_mono hle).trans (Submodule.finrank_add_le_finrank_add_finrank _ _)

private lemma cv_rank_neg {k l : ℕ} (A : Mat k l) : (-A).rank = A.rank := by
  unfold Matrix.rank
  have : Matrix.mulVecLin (-A) = -Matrix.mulVecLin A := by
    ext x i; simp
  rw [this, LinearMap.range_neg]

private lemma cv_rank_sub {k l : ℕ} (A B : Mat k l) : (A - B).rank ≤ A.rank + B.rank := by
  rw [sub_eq_add_neg]
  have := cv_rank_add A (-B)
  rwa [cv_rank_neg] at this

/-- Replacing one sample changes a matrix by rank at most two. -/
private lemma cv_rank_replace {m n : ℕ} (K : Mat m n) (c c' : ℝ)
    (u u' : Vec m) (v v' : Vec n) :
    Matrix.rank ((K + c • Muon.outer u v) - (K + c' • Muon.outer u' v')) ≤ 2 := by
  have houter : ∀ (d : ℝ) (x : Vec m) (y : Vec n),
      Matrix.rank (d • Muon.outer x y) ≤ 1 := by
    intro d x y
    have heq : d • Muon.outer x y = Muon.outer (d • x) y := by
      ext i k
      simp only [Muon.outer, Matrix.vecMulVec_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq]
    exact Matrix.rank_vecMulVec_le _ _
  have heq : (K + c • Muon.outer u v) - (K + c' • Muon.outer u' v') =
      c • Muon.outer u v - c' • Muon.outer u' v' := by abel
  rw [heq]
  exact (cv_rank_sub _ _).trans (by linarith [houter c u v, houter c' u' v'])

/-- Rank sensitivity specialized to replacing a single sample. -/
private lemma cv_phi_replace_bound (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (m n B : ℕ) (F : FrozenParams m n B) (K : Mat m n)
      (c c' : ℝ) (u u' : Vec m) (v v' : Vec n) (ϖ s : ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ ϖ → ϖ ≤ 1 → s0 ≤ s →
        |phiFresh F (K + c • Muon.outer u v) ϖ s -
          phiFresh F (K + c' • Muon.outer u' v') ϖ s| ≤
          2 * C * ϖ ^ 2 / (Real.sqrt s * B) := by
  obtain ⟨C, hC⟩ := lem_app_drift_rank s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro m n B F K c c' u u' v v' ϖ s hSo hSi hm hn hϖ0 hϖ1 hs
  have h := hC m n B F (K + c • Muon.outer u v) (K + c' • Muon.outer u' v') ϖ s 2
    hSo hSi hm hn hϖ0 hϖ1 hs (cv_rank_replace K c c' u u' v v')
  convert h using 1 <;> ring

/-- Rank sensitivity controls the actual conditional coefficient relative to a double deletion. -/
private lemma cv_phi_minor_difference (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j : ℕ) (Z : Ω → Mat m n)
      (c : Ω → ℝ) (u : Ω → Vec m) (v : Ω → Vec n),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w j → w j ≤ 1 →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω + c ω • Muon.outer (u ω) (v ω)) →
      ∀ s : ℝ, s0 ≤ s →
      ∀ᵐ ω ∂P, |phiJ w F S t j s ω - phiFresh F (Z ω) (w j) s| ≤
        2 * C * w j ^ 2 / (Real.sqrt s * B) := by
  obtain ⟨C, hC⟩ := cv_phi_replace_bound s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S w t j Z c u v hSo hSi hm hn hw0 hw1 hdec s hs
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs
  have hI := cv_alpha2_integrable w F S t j s CS γ hspos hγ hSo hSi hm hn hw0 hw1
  have hfresh := cv_phi_eq_fresh w F S t j s hspos hI
  filter_upwards [hfresh, hdec] with ω hω hωdec
  rw [hω, hωdec]
  simpa only [zero_smul, add_zero] using
    hC m n B F (Z ω) (c ω) 0 (u ω) (u ω) (v ω) (v ω) (w j) s
      hSo hSi hm hn hw0 hw1 hs

/-- A deleted coefficient whose two conditional expectations agree contributes no increment;
its uniformly bounded difference controls the actual martingale increment. -/
private lemma cv_increment_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (G H : MeasurableSpace Ω) (f g : Ω → ℝ) (D : ℝ)
    (hf : Integrable f P) (hg : Integrable g P)
    (hfg : ∀ᵐ ω ∂P, |f ω - g ω| ≤ D)
    (hcancel : condExp H P g =ᵐ[P] condExp G P g) :
    ∀ᵐ ω ∂P, |condExp H P f ω - condExp G P f ω| ≤ 2 * D := by
  have hb : ∀ J : MeasurableSpace Ω, ∀ᵐ ω ∂P, |condExp J P (f - g) ω| ≤ D := by
    intro J
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := J) (μ := P) (f := f - g)
        (by simpa only [Real.norm_eq_abs, Pi.sub_apply] using hfg))
  filter_upwards [condExp_sub hf hg H, condExp_sub hf hg G, hcancel, hb H, hb G]
    with ω hH hG hc hHb hGb
  simp only [Pi.sub_apply] at hH hG
  have he : condExp H P f ω - condExp G P f ω =
      condExp H P (f - g) ω - condExp G P (f - g) ω := by linarith
  rw [he]
  exact (abs_sub _ _).trans (by linarith)

/-- Independence factors integrals on intersections with an independent event. -/
private lemma cv_setIntegral_inter_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (G X : MeasurableSpace Ω)
    (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable[G] f)
    (a x : Set Ω) (ha : MeasurableSet[G] a) (hx : MeasurableSet[X] x) :
    (∫ ω in a ∩ x, f ω ∂P) = P.real x * ∫ ω in a, f ω ∂P := by
  have hi := hf.indicator (hG _ ha)
  have hc := condExp_indep_eq hG hX (hfm.indicator ha) hind
  calc
    _ = ∫ ω in x, a.indicator f ω ∂P := by
      rw [setIntegral_indicator (hG _ ha), Set.inter_comm]
    _ = ∫ ω in x, condExp X P (a.indicator f) ω ∂P :=
      (setIntegral_condExp hX hi hx).symm
    _ = ∫ _ω in x, (∫ ω in a, f ω ∂P) ∂P := by
      apply setIntegral_congr_ae (hX _ hx)
      filter_upwards [hc] with ω hω _
      simpa only [integral_indicator (hG _ ha)] using hω
    _ = _ := by rw [setIntegral_const, smul_eq_mul]

/-- Revealing an independent sigma-field does not change a conditional expectation. -/
private lemma cv_condExp_sup_of_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) (hf : Integrable f P) (hfm : StronglyMeasurable[G] f) :
    condExp (A ⊔ X) P f =ᵐ[P] condExp A P f := by
  have hA : A ≤ mΩ := hAG.trans hG
  have hAX : A ⊔ X ≤ mΩ := sup_le hA hX
  let g := condExp A P f
  have hg : Integrable g P := integrable_condExp
  have hgm : StronglyMeasurable[G] g := stronglyMeasurable_condExp.mono hAG
  let T : Set (Set Ω) := {s | ∃ a x, MeasurableSet[A] a ∧ MeasurableSet[X] x ∧ s = a ∩ x}
  have hgen : A ⊔ X = MeasurableSpace.generateFrom T := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro a ha
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨a, univ, ha, MeasurableSet.univ, by simp⟩
      · intro x hx
        exact MeasurableSpace.measurableSet_generateFrom
          ⟨univ, x, MeasurableSet.univ, hx, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro s ⟨a, x, ha, hx, rfl⟩
      exact ((show A ≤ A ⊔ X from le_sup_left) _ ha).inter
        ((show X ≤ A ⊔ X from le_sup_right) _ hx)
  have hpi : IsPiSystem T := by
    rintro s ⟨a, x, ha, hx, rfl⟩ t ⟨b, y, hb, hy, rfl⟩ _
    exact ⟨a ∩ b, x ∩ y, ha.inter hb, hx.inter hy, by ext ω; simp only [mem_inter_iff]; tauto⟩
  have heq : ∀ a, MeasurableSet[A] a → ∫ ω in a, g ω ∂P = ∫ ω in a, f ω ∂P :=
    fun a ha => setIntegral_condExp hA hf ha
  have hall : ∀ s, MeasurableSet[A ⊔ X] s → ∫ ω in s, g ω ∂P = ∫ ω in s, f ω ∂P := by
    intro s hs
    induction s, hs using MeasurableSpace.induction_on_inter hgen hpi with
    | empty => simp
    | basic s hs =>
      rcases hs with ⟨a, x, ha, hx, rfl⟩
      rw [@cv_setIntegral_inter_of_indep Ω mΩ P _ G X hG hX hind g hg hgm a x (hAG _ ha) hx,
        @cv_setIntegral_inter_of_indep Ω mΩ P _ G X hG hX hind f hf hfm a x (hAG _ ha) hx,
        heq a ha]
    | compl s hs ih =>
      rw [setIntegral_compl (hAX _ hs) hg, setIntegral_compl (hAX _ hs) hf, ih]
      congr 1
      exact integral_condExp hA
    | iUnion u hd hu ih =>
      rw [integral_iUnion (fun k => hAX _ (hu k)) hd hg.integrableOn,
        integral_iUnion (fun k => hAX _ (hu k)) hd hf.integrableOn]
      exact tsum_congr ih
  have hgmAX : StronglyMeasurable[A ⊔ X] g :=
    (show StronglyMeasurable[A] g from stronglyMeasurable_condExp).mono le_sup_left
  exact (ae_eq_condExp_of_forall_setIntegral_eq hAX hf (fun _ _ _ => hg.integrableOn)
    (fun s hs _ => hall s hs)
    hgmAX.aestronglyMeasurable).symm

/-- Conditional expectation is self-adjoint against a bounded scalar test function. -/
private lemma cv_integral_mul_condExp {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : MeasurableSpace Ω) (hA : A ≤ mΩ)
    (f q : Ω → ℝ) (hf : Integrable f P) (hq : Integrable q P)
    (L : ℝ) (hqb : ∀ᵐ ω ∂P, ‖q ω‖ ≤ L) :
    (∫ ω, f ω * condExp A P q ω ∂P) =
      ∫ ω, condExp A P f ω * q ω ∂P := by
  have hcb : ∀ᵐ ω ∂P, ‖condExp A P q ω‖ ≤ L :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hqb
  have hi1 : Integrable (fun ω => f ω * condExp A P q ω) P :=
    hf.mul_bdd (integrable_condExp.aestronglyMeasurable) hcb
  have hi2 : Integrable (fun ω => condExp A P f ω * q ω) P :=
    integrable_condExp.mul_bdd hq.aestronglyMeasurable hqb
  have h1 := condExp_mul_of_stronglyMeasurable_right
    (show StronglyMeasurable[A] (condExp A P q) from stronglyMeasurable_condExp) hi1 hf
  have h2 := condExp_mul_of_stronglyMeasurable_left
    (show StronglyMeasurable[A] (condExp A P f) from stronglyMeasurable_condExp) hi2 hq
  calc
    _ = ∫ ω, condExp A P (fun ω => f ω * condExp A P q ω) ω ∂P :=
      (integral_condExp hA).symm
    _ = ∫ ω, condExp A P f ω * condExp A P q ω ∂P := integral_congr_ae h1
    _ = ∫ ω, condExp A P (fun ω => condExp A P f ω * q ω) ω ∂P :=
      (integral_congr_ae h2).symm
    _ = _ := integral_condExp hA

/-- Conditioning a function of the past and the new sample on all other samples keeps only
its past conditional expectation. -/
private lemma cv_condExp_of_sup_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (h : Ω → ℝ) (hi : Integrable h P) (hm : StronglyMeasurable[A ⊔ X] h) :
    condExp G P h =ᵐ[P] condExp A P h := by
  have hA : A ≤ mΩ := hAG.trans hG
  have hH : A ⊔ X ≤ mΩ := sup_le hA hX
  refine (ae_eq_condExp_of_forall_setIntegral_eq hG hi
    (fun _ _ _ => integrable_condExp.integrableOn) ?_
    ((show StronglyMeasurable[A] (condExp A P h) from
      stronglyMeasurable_condExp).mono hAG).aestronglyMeasurable).symm
  intro s hs _
  let q : Ω → ℝ := s.indicator (fun _ => 1)
  have hqm : StronglyMeasurable[G] q := stronglyMeasurable_const.indicator hs
  have hqi : Integrable q P := (integrable_const 1).indicator (hG _ hs)
  have hqb : ∀ᵐ ω ∂P, ‖q ω‖ ≤ 1 := Eventually.of_forall fun ω => by
    by_cases hω : ω ∈ s <;> simp [q, hω]
  have hc := @cv_condExp_sup_of_indep Ω mΩ P _ A X G hAG hG hX hind q hqi hqm
  have hh : condExp (A ⊔ X) P h =ᵐ[P] h := (condExp_of_stronglyMeasurable hH hm hi).eventuallyEq
  have hindicator : ∀ f : Ω → ℝ, (∫ ω, f ω * q ω ∂P) = ∫ ω in s, f ω ∂P := by
    intro f
    rw [← integral_indicator (hG _ hs)]
    congr 1
    funext ω
    by_cases hω : ω ∈ s <;> simp [q, hω]
  calc
    _ = ∫ ω, condExp A P h ω * q ω ∂P := (hindicator _).symm
    _ = ∫ ω, h ω * condExp A P q ω ∂P :=
      (@cv_integral_mul_condExp Ω mΩ P _ A hA h q hi hqi 1 hqb).symm
    _ = ∫ ω, h ω * condExp (A ⊔ X) P q ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω using congrArg (fun r => h ω * r) hω.symm
    _ = ∫ ω, condExp (A ⊔ X) P h ω * q ω ∂P :=
      @cv_integral_mul_condExp Ω mΩ P _ (A ⊔ X) hH h q hi hqi 1 hqb
    _ = ∫ ω, h ω * q ω ∂P := by
      apply integral_congr_ae
      filter_upwards [hh] with ω hω using congrArg (fun r => r * q ω) hω
    _ = _ := hindicator _

/-- The two conditional expectations commute when one sigma-field adds independent noise. -/
private lemma cv_condExp_condExp_sup_indep {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) :
    condExp G P (condExp (A ⊔ X) P f) =ᵐ[P] condExp A P f := by
  exact (@cv_condExp_of_sup_indep Ω mΩ P _ A X G hAG hG hX hind _
    integrable_condExp stronglyMeasurable_condExp).trans
      (condExp_condExp_of_le le_sup_left (sup_le (hAG.trans hG) hX))

/-- The martingale increment has zero mean conditional on all unrevealed other samples. -/
private lemma cv_independent_increment_zero {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A X G : MeasurableSpace Ω)
    (hAG : A ≤ G) (hG : G ≤ mΩ) (hX : X ≤ mΩ) (hind : Indep G X P)
    (f : Ω → ℝ) :
    condExp G P (condExp (A ⊔ X) P f - condExp A P f) =ᵐ[P]
      fun _ => 0 := by
  have hsub := condExp_sub (m₀ := mΩ) (μ := P)
    (f := condExp (A ⊔ X) P f) (g := condExp A P f)
    integrable_condExp integrable_condExp G
  have hnew := @cv_condExp_condExp_sup_indep Ω mΩ P _ A X G hAG hG hX hind f
  have hold : condExp G P (condExp A P f) = condExp A P f :=
    condExp_of_stronglyMeasurable hG
      ((show StronglyMeasurable[A] (condExp A P f) from
        stronglyMeasurable_condExp).mono hAG) integrable_condExp
  filter_upwards [hsub, hnew] with ω hs hn
  simpa only [Pi.sub_apply, hold, hn, sub_self] using hs

/-- The fresh coefficient is a measurable function of its matrix argument. -/
private lemma cv_phiFresh_measurable {m n B : ℕ} (F : FrozenParams m n B)
    (ϖ s : ℝ) (hs : 0 < s) : Measurable (fun K : Mat m n => phiFresh F K ϖ s) := by
  let f : Mat m n → Vec m × Vec n → ℝ := fun K x =>
    Muon.DetEquiv.alpha2 K (ϖ * dotProduct x.1 (Matrix.mulVec F.A x.2))
      (momU F.C B x) (momV F.C B x) s
  have hc : Continuous (fun q : Mat m n × (Vec m × Vec n) =>
      (q.1, ϖ * dotProduct q.2.1 (Matrix.mulVec F.A q.2.2),
        momU F.C B q.2, momV F.C B q.2)) := by
    unfold momU momV
    fun_prop
  have hf : StronglyMeasurable (Function.uncurry f) :=
    ((cv_alpha_continuous s hs).2.1.comp hc).measurable.stronglyMeasurable
  haveI : IsProbabilityMeasure (freshMeas m n) := by
    change IsProbabilityMeasure (gaussPair m n)
    infer_instance
  exact (hf.integral_prod_right (ν := freshMeas m n)).measurable

/-- Every slot is independent of the sigma-field generated by all remaining slots. -/
private lemma cv_slot_indep {Ω : Type*} [MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (S : FrozenSamples P m n B) (p : ℤ × Fin B) :
    Indep (⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
      (MeasurableSpace.comap (S.zw p.1 p.2) inferInstance) P := by
  have hi := (iIndepFun_iff_iIndep
    (fun _ : ℤ × Fin B => (inferInstance : MeasurableSpace (Vec m × Vec n)))
    (fun q : ℤ × Fin B => fun ω => S.zw q.1 q.2 ω) P).mp S.indep
  have hd : Disjoint {q : ℤ × Fin B | q ≠ p} ({p} : Set (ℤ × Fin B)) := by
    rw [Set.disjoint_singleton_right]
    exact fun h => h rfl
  have key := indep_iSup_of_disjoint (fun q : ℤ × Fin B => (S.meas q.1 q.2).comap_le) hi hd
  exact indep_of_indep_of_le_right key (le_iSup_of_le p
    (le_iSup_of_le (Set.mem_singleton p) le_rfl))

/-- Samples later than the buffer time do not occur in the distinguished minor. -/
private lemma cv_del_measurable_future {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (p : ℤ × Fin B)
    (hp : t + 1 < p.1) :
    Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] (delBufAge w F S t j) := by
  classical
  let U : Finset (ℤ × Fin B) := insert p {(t + 1 - (j : ℤ), slotOne F.hB)}
  have hm := cv_masked_buf_measurable w F S t U p (Finset.mem_insert_self _ _)
  have hne : ∀ (k : ℕ) (a : Fin B), (t + 1 - (k : ℤ), a) ≠ p := by
    intro k a he
    have he1 := congrArg Prod.fst he
    have hk : (0 : ℤ) ≤ k := Int.natCast_nonneg k
    omega
  unfold delBufAge WeightedBufDel
  simpa only [U, Finset.mem_insert, Finset.mem_singleton, hne, false_or,
    Prod.mk.injEq] using hm

/-- A future sample has zero actual coefficient increment. -/
private lemma cv_future_increment_zero {Ω : Type*} (A : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (p : ℤ × Fin B) (hp : t + 1 < p.1)
    (hAG : A ≤ ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
      MeasurableSpace.comap (S.zw q.1 q.2) inferInstance)
    (s : ℝ) (hs : 0 < s) (hI : Integrable (delAlpha2 w F S t j s) P) :
    (fun ω => condExp (A ⊔ MeasurableSpace.comap (S.zw p.1 p.2) inferInstance)
      P (phiJ w F S t j s) ω - condExp A P (phiJ w F S t j s) ω) =ᵐ[P] fun _ => 0 := by
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ p),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let X : MeasurableSpace Ω := MeasurableSpace.comap (S.zw p.1 p.2) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hX : X ≤ mΩ := (S.meas _ _).comap_le
  let g := fun ω => phiFresh F (delBufAge w F S t j ω) (w j) s
  have he : phiJ w F S t j s =ᵐ[P] g := cv_phi_eq_fresh w F S t j s hs hI
  have hgm : StronglyMeasurable[G] g :=
    ((cv_phiFresh_measurable F (w j) s hs).comp
      (cv_del_measurable_future w F S t j p hp)).stronglyMeasurable
  have hgI : Integrable g P := (show Integrable (phiJ w F S t j s) P from integrable_condExp).congr he
  have hc := cv_condExp_sup_of_indep P A X G hAG hG hX (cv_slot_indep S p) g hgI hgm
  have hH := condExp_congr_ae (m := A ⊔ X) he
  have hA := condExp_congr_ae (m := A) he
  filter_upwards [hc, hH, hA] with ω hcω hHω hAω
  change condExp (A ⊔ X) P (phiJ w F S t j s) ω - condExp A P (phiJ w F S t j s) ω = 0
  rw [hHω, hAω, hcω, sub_self]

/-- A double deletion and independence bound the actual conditional coefficient increment. -/
private lemma cv_phi_increment_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) (A X G : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j : ℕ) (Z : Ω → Mat m n)
      (c : Ω → ℝ) (u : Ω → Vec m) (v : Ω → Vec n),
      A ≤ G → G ≤ mΩ → X ≤ mΩ → Indep G X P →
      Measurable[G] Z →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w j → w j ≤ 1 →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω + c ω • Muon.outer (u ω) (v ω)) →
      ∀ s : ℝ, s0 ≤ s →
      ∀ᵐ ω ∂P, |condExp (A ⊔ X) P (phiJ w F S t j s) ω -
        condExp A P (phiJ w F S t j s) ω| ≤
          4 * C * w j ^ 2 / (Real.sqrt s * B) := by
  obtain ⟨C, hC⟩ := cv_phi_minor_difference s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω A X G mΩ m n B P _ F S w t j Z c u v hAG hG hX hind hZ
    hSo hSi hm hn hw0 hw1 hdec s hs
  let f := phiJ w F S t j s
  let g := fun ω => phiFresh F (Z ω) (w j) s
  let D := 2 * C * w j ^ 2 / (Real.sqrt s * B)
  have hf : Integrable f P := by
    dsimp [f, phiJ]
    exact integrable_condExp
  have hgm : StronglyMeasurable[G] g :=
    ((cv_phiFresh_measurable F (w j) s (hs0.trans_le hs)).comp hZ).stronglyMeasurable
  have hfg : ∀ᵐ ω ∂P, |f ω - g ω| ≤ D :=
    hC Ω m n B P F S w t j Z c u v hSo hSi hm hn hw0 hw1 hdec s hs
  have hg : Integrable g P := by
    refine (hf.norm.add (integrable_const D)).mono' (hgm.mono hG).aestronglyMeasurable ?_
    filter_upwards [hfg] with ω hω
    rw [Real.norm_eq_abs]
    have ht : |g ω| ≤ |f ω| + |f ω - g ω| := by
      have := abs_sub (f ω) (f ω - g ω)
      simpa only [sub_sub_cancel] using this
    simpa only [Pi.add_apply, Real.norm_eq_abs] using ht.trans (add_le_add_right hω (|f ω|))
  have hc := @cv_condExp_sup_of_indep Ω mΩ P _ A X G hAG hG hX hind g hg hgm
  have hb := cv_increment_bound P A (A ⊔ X) f g D hf hg hfg hc
  have hD : 2 * D = 4 * C * w j ^ 2 / (Real.sqrt s * B) := by dsimp [D]; ring
  simpa only [hD] using hb

/-- A multiplier with zero conditional mean is orthogonal to a deleted matrix field. -/
private lemma cv_deleted_mean_zero {Ω : Type*} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hG : G ≤ mΩ) (h : Ω → ℝ) (Z : Ω → Mat m n)
    (hI : Integrable h P) (hZ : Measurable[G] Z)
    (hIZ : ∀ i k, Integrable (fun ω => h ω * Z ω i k) P)
    (hz : condExp G P h =ᵐ[P] fun _ => 0) :
    Muon.mean P (fun ω => h ω • Z ω) = 0 := by
  ext i k
  change (∫ ω, h ω * Z ω i k ∂P) = 0
  have hentry : StronglyMeasurable[G] (fun ω => Z ω i k) :=
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hZ)).stronglyMeasurable
  have hpull := condExp_mul_of_stronglyMeasurable_right hentry (hIZ i k) hI
  simp only [Pi.mul_def] at hpull
  have hzero : condExp G P (fun ω => h ω * Z ω i k) =ᵐ[P] fun _ => 0 := by
    filter_upwards [hpull, hz] with ω hω hω0
    simpa only [Pi.mul_apply, hω0, zero_mul] using hω
  calc
    _ = ∫ ω, condExp G P (fun ω => h ω * Z ω i k) ω ∂P := (integral_condExp hG).symm
    _ = 0 := by rw [integral_congr_ae hzero, integral_zero]

/-- Orthogonality converts a covariance term to a deletion term entrywise. -/
private lemma cv_deleted_term_identity {Ω : Type*} (G : MeasurableSpace Ω)
    [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {m n : ℕ} (hG : G ≤ mΩ) (h : Ω → ℝ) (X Z : Ω → Mat m n)
    (hI : Integrable h P) (hZ : Measurable[G] Z)
    (hIX : ∀ i k, Integrable (fun ω => h ω * X ω i k) P)
    (hIZ : ∀ i k, Integrable (fun ω => h ω * Z ω i k) P)
    (hz : condExp G P h =ᵐ[P] fun _ => 0) :
    Muon.mean P (fun ω => h ω • X ω) =
      Muon.mean P (fun ω => h ω • (X ω - Z ω)) := by
  have hzero := cv_deleted_mean_zero G P hG h Z hI hZ hIZ hz
  ext i k
  have hentry := congrArg (fun M : Mat m n => M i k) hzero
  change (∫ ω, h ω * Z ω i k ∂P) = 0 at hentry
  change (∫ ω, h ω * X ω i k ∂P) = ∫ ω, h ω * (X ω i k - Z ω i k) ∂P
  simp_rw [mul_sub]
  rw [integral_sub (hIX i k) (hIZ i k), hentry, sub_zero]

/-- A zero-conditional-mean multiplier turns the covariance term into a deletion term. -/
private lemma cv_minor_covariance_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (t : ℤ) (j k : ℕ) (a : Fin B) (Z : Ω → Mat m n)
      (D : ℝ) (h : Ω → ℝ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → 0 ≤ w k → w k ≤ 1 →
      Measurable[⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] Z →
      (∀ᵐ ω ∂P, delBufAge w F S t j ω = Z ω +
        (w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω)) •
          Muon.outer (momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
            (momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))) →
      Measurable[MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance ⊔
        ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
          MeasurableSpace.comap (S.zw q.1 q.2) inferInstance] h →
      (∀ᵐ ω ∂P, |h ω| ≤ D) → Integrable h P →
      (condExp (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) P h =ᵐ[P] fun _ => 0) → ∀ s : ℝ, s0 ≤ s →
      fro (Muon.mean P (fun ω => h ω •
        Xs (delBufAge w F S t j ω) s)) ≤
        C * D * w k / (s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := cv_minor_deletion_bound_ae s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD hI hz s hs
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hGj : sigmaOthers F S t j ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hspos := hs0.trans_le hs
  have hc : Continuous (fun M : Mat m n => Xs M s) :=
    (cv_Rs_continuous s hspos).matrix_mul continuous_id
  have hXm : Measurable (fun ω => Xs (delBufAge w F S t j ω) s) :=
    hc.measurable.comp ((cv_del_measurable w F S t j).mono hGj le_rfl)
  have hZm : Measurable[G] (fun ω => Xs (Z ω) s) := hc.measurable.comp hZ
  have hbound : ∀ M : Mat m n, ∀ i r, |Xs M s i r| ≤ 1 / (2 * Real.sqrt s) :=
    fun M i r => (cv_abs_entry_le _ i r).trans ((lem_app_de_resolvent M s hspos).2.2.1)
  have hIX : ∀ i r, Integrable (fun ω => h ω * Xs (delBufAge w F S t j ω) s i r) P := by
    intro i r
    exact hI.mul_bdd
      (((measurable_pi_apply r).comp ((measurable_pi_apply i).comp hXm)).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound _ i r)
  have hIZ : ∀ i r, Integrable (fun ω => h ω * Xs (Z ω) s i r) P := by
    intro i r
    exact hI.mul_bdd
      (((measurable_pi_apply r).comp ((measurable_pi_apply i).comp (hZm.mono hG le_rfl))).aestronglyMeasurable)
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound _ i r)
  rw [cv_deleted_term_identity G P hG h _ _ hI hZm hIX hIZ hz]
  exact hC Ω m n B P F S w t j k a Z D h hSo hSi hm hn hw0 hw1 hZ hdec hh hD s hs

/-- Each actual martingale slot contribution satisfies the rank-sensitivity times deletion bound. -/
private lemma cv_martingale_slot_bound (s0 : ℝ) (hs0 : 0 < s0)
    (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) (A : MeasurableSpace Ω) [mΩ : MeasurableSpace Ω]
      (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (w : ℕ → ℝ) (hw : WeightSeq w) (t : ℤ) (j k : ℕ) (a : Fin B),
      (t + 1 - (k : ℤ), a) ≠ (t + 1 - (j : ℤ), slotOne F.hB) →
      A ≤ (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
        MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      0 ≤ w j → w j ≤ 1 → 0 ≤ w k → w k ≤ 1 → ∀ s : ℝ, s0 ≤ s →
      fro (Muon.mean P (fun ω =>
        (condExp (A ⊔ MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance)
          P (phiJ w F S t j s) ω - condExp A P (phiJ w F S t j s) ω) •
          Xs (delBufAge w F S t j ω) s)) ≤
        C * w j ^ 2 * w k / (s * Real.sqrt s * B * Real.sqrt (B : ℝ)) := by
  obtain ⟨CR, hR⟩ := cv_phi_increment_bound s0 hs0 CS γ hγ
  obtain ⟨CM, hM⟩ := cv_minor_covariance_bound s0 hs0 CS γ hγ
  refine ⟨4 * CM * CR, ?_⟩
  intro Ω A mΩ m n B P _ F S w hw t j k a hne hAG hSo hSi hm hn hwj0 hwj1 hwk0 hwk1 s hs
  let G : MeasurableSpace Ω := ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (k : ℤ), a)),
    MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
  letI := mΩ
  let X : MeasurableSpace Ω := MeasurableSpace.comap (S.zw (t + 1 - (k : ℤ)) a) inferInstance
  letI := mΩ
  have hG : G ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hX : X ≤ mΩ := (S.meas _ _).comap_le
  have hind : Indep G X P := cv_slot_indep S _
  obtain ⟨Z, hZ, _, hdec⟩ := cv_double_deletion w hw F S t j k a hne
  let f := phiJ w F S t j s
  let h : Ω → ℝ := condExp (A ⊔ X) P f - condExp A P f
  let D : ℝ := 4 * CR * w j ^ 2 / (Real.sqrt s * B)
  have hbd : ∀ᵐ ω ∂P, |h ω| ≤ D :=
    hR Ω A X G m n B P F S w t j Z
      (fun ω => w k * resid F.A (S.zw (t + 1 - (k : ℤ)) a ω))
      (fun ω => momU F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
      (fun ω => momV F.C B (S.zw (t + 1 - (k : ℤ)) a ω))
      hAG hG hX hind hZ hSo hSi hm hn hwj0 hwj1 hdec s hs
  have hI : Integrable h P :=
    (integrable_condExp (m := A ⊔ X) (μ := P) (f := f)).sub integrable_condExp
  have hz : condExp G P h =ᵐ[P] fun _ => 0 :=
    cv_independent_increment_zero P A X G hAG hG hX hind f
  have hhH : Measurable[A ⊔ X] h :=
    (show StronglyMeasurable[A ⊔ X] (condExp (A ⊔ X) P f) from
      stronglyMeasurable_condExp).measurable.sub
      ((show StronglyMeasurable[A] (condExp A P f) from
        stronglyMeasurable_condExp).mono le_sup_left).measurable
  have hh : Measurable[X ⊔ G] h := hhH.mono
    (sup_le (hAG.trans le_sup_right) le_sup_left) le_rfl
  have hb := hM Ω m n B P F S w t j k a Z D h hSo hSi hm hn hwk0 hwk1 hZ hdec hh hbd hI hz s hs
  calc
    _ ≤ CM * D * w k / (s * Real.sqrt (B : ℝ)) := hb
    _ = _ := by dsimp [D]; simp only [div_eq_mul_inv, _root_.mul_inv_rev]; ring

/-- The bounded scalar covariance admits its martingale expansion on any exhausting filtration. -/
private lemma cv_martingale_expansion {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (A : Filtration ℕ mΩ)
    (hA0 : A 0 = ⊥) (f X : Ω → ℝ) (K L : ℝ)
    (hf : Integrable f P) (hfm : StronglyMeasurable[⨆ l, A l] f)
    (hfbd : ∀ᵐ ω ∂P, |f ω| ≤ K) (hXm : Measurable X) (hXbd : ∀ ω, |X ω| ≤ L) :
    Tendsto (fun N => ∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P f ω - condExp (A l) P f ω) * X ω ∂P)
      atTop (𝓝 (∫ ω, (f ω - ∫ ζ, f ζ ∂P) * X ω ∂P)) := by
  have hcb : ∀ l, ∀ᵐ ω ∂P, |condExp (A l) P f ω| ≤ K := by
    intro l
    simpa only [Real.norm_eq_abs] using
      (ae_bdd_norm_condExp_of_ae_bdd_norm (m := A l) (μ := P) (f := f) (R := K)
        (by simpa only [Real.norm_eq_abs] using hfbd))
  have hprod : ∀ l, Integrable (fun ω => condExp (A l) P f ω * X ω) P := by
    intro l
    exact integrable_condExp.mul_bdd hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hXbd ω)
  have hfprod : Integrable (fun ω => f ω * X ω) P :=
    hf.mul_bdd hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hXbd ω)
  have hcprod : Integrable (fun ω => (∫ ζ, f ζ ∂P) * X ω) P :=
    (integrable_const _).mul_bdd hXm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hXbd ω)
  have hconv : Tendsto (fun N => ∫ ω, condExp (A N) P f ω * X ω ∂P)
      atTop (𝓝 (∫ ω, f ω * X ω ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => K * L)
      (fun l => (hprod l).aestronglyMeasurable) (integrable_const _) ?_ ?_
    · intro l
      filter_upwards [hcb l] with ω hω
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul hω (hXbd ω) (abs_nonneg _) ((abs_nonneg _).trans hω)
    · filter_upwards [hf.tendsto_ae_condExp hfm] with ω hω
      exact hω.mul_const (X ω)
  have hsum : ∀ N, (∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P f ω - condExp (A l) P f ω) * X ω ∂P) =
      (∫ ω, condExp (A N) P f ω * X ω ∂P) -
        ∫ ω, condExp (A 0) P f ω * X ω ∂P := by
    intro N
    calc
      _ = ∑ l ∈ Finset.range N, ((∫ ω, condExp (A (l + 1)) P f ω * X ω ∂P) -
          ∫ ω, condExp (A l) P f ω * X ω ∂P) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        simp_rw [sub_mul]
        exact integral_sub (hprod (l + 1)) (hprod l)
      _ = _ := Finset.sum_range_sub (fun l => ∫ ω, condExp (A l) P f ω * X ω ∂P) N
  have hbot : condExp (A 0) P f = fun _ => ∫ ζ, f ζ ∂P := by
    rw [hA0, condExp_bot]
  have hfinal := hconv.sub_const (∫ ω, (∫ ζ, f ζ ∂P) * X ω ∂P)
  simp_rw [hsum, hbot]
  have heq : (∫ ω, (f ω - ∫ ζ, f ζ ∂P) * X ω ∂P) =
      (∫ ω, f ω * X ω ∂P) - ∫ ω, (∫ ζ, f ζ ∂P) * X ω ∂P := by
    simp_rw [sub_mul]
    exact integral_sub hfprod hcprod
  rw [heq]
  exact hfinal

/-- Reveal the other samples in the order of their encodings; the resulting filtration exhausts
`sigmaOthers` and starts at the trivial sigma-field. -/
private lemma cv_sample_filtration {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    ∃ A : Filtration ℕ mΩ,
      (∀ l, A l = ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) ∧
      A 0 = ⊥ ∧ (⨆ l, A l) = sigmaOthers F S t j := by
  let A : Filtration ℕ mΩ := {
    seq := fun l => ⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
      (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance
    mono' := by
      intro l l' hll'
      refine iSup_le fun q => iSup_le fun hq => iSup_le fun hql => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (lt_of_lt_of_le hql hll') le_rfl))
    le' := by
      intro l
      exact iSup_le fun q => iSup_le fun _ => iSup_le fun _ => (S.meas q.1 q.2).comap_le }
  refine ⟨A, fun _ => rfl, ?_, ?_⟩
  · change (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < 0), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) = ⊥
    simp only [Nat.not_lt_zero, iSup_of_empty, iSup_bot]
  · refine le_antisymm ?_ ?_
    · refine iSup_le fun l => ?_
      change (⨆ (q : ℤ × Fin B) (_ : q ≠ (t + 1 - (j : ℤ), slotOne F.hB))
        (_ : Encodable.encode q < l), MeasurableSpace.comap (S.zw q.1 q.2) inferInstance) ≤ _
      refine iSup_le fun q => iSup_le fun hq => iSup_le fun _ => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq le_rfl)
    · refine iSup_le fun q => iSup_le fun hq => ?_
      refine le_iSup_of_le (Encodable.encode q + 1) ?_
      change MeasurableSpace.comap (S.zw q.1 q.2) inferInstance ≤
        ⨆ (r : ℤ × Fin B) (_ : r ≠ (t + 1 - (j : ℤ), slotOne F.hB))
          (_ : Encodable.encode r < Encodable.encode q + 1),
          MeasurableSpace.comap (S.zw r.1 r.2) inferInstance
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (Nat.lt_succ_self _) le_rfl))

/-- An encoding step reveals exactly its single indexed sigma-field. -/
private lemma cv_encoded_reveal {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d p : ι) (hp : p ≠ d) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p + 1), M q) =
      (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p), M q) ⊔ M p := by
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    by_cases hqp : q = p
    · subst q; exact le_sup_right
    · have hcode : Encodable.encode q ≠ Encodable.encode p :=
        fun h => hqp (Encodable.encode_injective h)
      have hlt : Encodable.encode q < Encodable.encode p := by omega
      exact le_sup_of_le_left (le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le hlt le_rfl)))
  · refine sup_le ?_ ?_
    · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
      exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))
    · exact le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le (Nat.lt_succ_self _) le_rfl))

/-- Before a slot is revealed, the filtration is contained in the sigma-field omitting it. -/
private lemma cv_encoded_past_le {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d p : ι) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < Encodable.encode p), M q) ≤
      ⨆ (q : ι) (_ : q ≠ p), M q := by
  refine iSup_le fun q => iSup_le fun _ => iSup_le fun he => ?_
  have hqp : q ≠ p := by intro h; subst q; exact (lt_irrefl _ he)
  exact le_iSup_of_le q (le_iSup_of_le hqp le_rfl)

/-- An encoding gap (including the excluded distinguished slot) reveals no new information. -/
private lemma cv_encoded_no_reveal {ι Ω : Type*} [Encodable ι]
    (M : ι → MeasurableSpace Ω) (d : ι) (l : ℕ)
    (hgap : ∀ q, q ≠ d → Encodable.encode q ≠ l) :
    (⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < l + 1), M q) =
      ⨆ (q : ι) (_ : q ≠ d) (_ : Encodable.encode q < l), M q := by
  apply le_antisymm
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    have hne := hgap q hq
    exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))
  · refine iSup_le fun q => iSup_le fun hq => iSup_le fun he => ?_
    exact le_iSup_of_le q (le_iSup_of_le hq (le_iSup_of_le (by omega) le_rfl))

/-- Any finite collection of age-slot weights has mass at most `B` times the total age mass. -/
private lemma cv_finite_slot_weight_sum {B : ℕ} (w : ℕ → ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (hw : Summable w) (U : Finset (ℕ × Fin B)) :
    (∑ p ∈ U, w p.1) ≤ (B : ℝ) * ∑' k, w k := by
  classical
  let V := U.image Prod.fst
  have hsub : U ⊆ V ×ˢ Finset.univ := by
    intro p hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨p, hp, rfl⟩, Finset.mem_univ _⟩
  calc
    _ ≤ ∑ p ∈ V ×ˢ Finset.univ, w p.1 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hw0 p.1)
    _ = (B : ℝ) * ∑ k ∈ V, w k := by
      simp only [Finset.sum_product, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hw.sum_le_tsum _ (fun k _ => hw0 k)) (Nat.cast_nonneg B)

/-- Reindex any finite encoding budget by its age-slot pairs. -/
private lemma cv_encoded_weight_budget {B : ℕ} (t : ℤ) (w : ℕ → ℝ)
    (hw0 : ∀ k, 0 ≤ w k) (hw : Summable w) (hws : (∑' k, w k) ≤ 1)
    (f : ℕ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hzero : ∀ l, (∀ (k : ℕ) (a : Fin B),
      Encodable.encode (t + 1 - (k : ℤ), a) ≠ l) → f l = 0)
    (hslot : ∀ (k : ℕ) (a : Fin B),
      f (Encodable.encode (t + 1 - (k : ℤ), a)) ≤ K * w k) (N : ℕ) :
    (∑ l ∈ Finset.range N, f l) ≤ K * B := by
  classical
  let e : ℕ × Fin B → ℕ := fun p => Encodable.encode (t + 1 - (p.1 : ℤ), p.2)
  have he : Function.Injective e := by
    intro p q hpq
    have h := Encodable.encode_injective hpq
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    apply Prod.ext
    · dsimp at h1
      omega
    · exact h2
  let U := (Finset.range N).preimage e he.injOn
  have hsub : U.image e ⊆ Finset.range N := by
    intro l hl
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_preimage.mp hp
  have hreindex : (∑ l ∈ Finset.range N, f l) = ∑ p ∈ U, f (e p) := by
    calc
      _ = ∑ l ∈ U.image e, f l := by
        symm
        apply Finset.sum_subset hsub
        intro l hl hnot
        apply hzero
        intro k a hcode
        apply hnot
        exact Finset.mem_image.mpr ⟨(k, a), Finset.mem_preimage.mpr (by change Encodable.encode (t + 1 - (k : ℤ), a) ∈ Finset.range N; rw [hcode]; exact hl), hcode⟩
      _ = _ := Finset.sum_image he.injOn
  have hbound : (∑ p ∈ U, f (e p)) ≤ K * ∑ p ∈ U, w p.1 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun p _ => hslot p.1 p.2
  have hmass : (∑ p ∈ U, w p.1) ≤ (B : ℝ) := by
    exact (cv_finite_slot_weight_sum w hw0 hw U).trans
      (by simpa using mul_le_mul_of_nonneg_left hws (Nat.cast_nonneg B))
  rw [hreindex]
  exact hbound.trans (mul_le_mul_of_nonneg_left hmass hK)

/-- The entrywise covariance expansion along a filtration exhausting the other samples. -/
private lemma cv_Cj_expansion {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s : ℝ) (hs : 0 < s) (K : ℝ)
    (hphi : ∀ᵐ ω ∂P, |phiJ w F S t j s ω| ≤ K)
    (A : Filtration ℕ mΩ) (hA0 : A 0 = ⊥) (hAe : (⨆ l, A l) = sigmaOthers F S t j)
    (i : Fin m) (k : Fin n) :
    Tendsto (fun N => ∑ l ∈ Finset.range N,
      ∫ ω, (condExp (A (l + 1)) P (phiJ w F S t j s) ω -
        condExp (A l) P (phiJ w F S t j s) ω) *
        Xs (delBufAge w F S t j ω) s i k ∂P)
      atTop (𝓝 (Cj w F S t j s i k)) := by
  have hG : sigmaOthers F S t j ≤ mΩ :=
    iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  have hM : Measurable (delBufAge w F S t j) :=
    (cv_del_measurable w F S t j).mono hG le_rfl
  have hc : Continuous (fun M : Mat m n => Xs M s) := by
    unfold Xs
    exact (cv_Rs_continuous s hs).matrix_mul continuous_id
  have hX : Measurable (fun ω => Xs (delBufAge w F S t j ω) s i k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply i).comp (hc.measurable.comp hM))
  have hfm : StronglyMeasurable[⨆ l, A l] (phiJ w F S t j s) := by
    rw [hAe]
    exact stronglyMeasurable_condExp
  have hbound : ∀ ω, |Xs (delBufAge w F S t j ω) s i k| ≤ 1 / (2 * Real.sqrt s) :=
    fun ω => (cv_abs_entry_le _ i k).trans ((lem_app_de_resolvent _ s hs).2.2.1)
  have h := cv_martingale_expansion P A hA0 (phiJ w F S t j s)
    (fun ω => Xs (delBufAge w F S t j ω) s i k) K (1 / (2 * Real.sqrt s))
    integrable_condExp hfm hphi hX hbound
  simpa only [Cj, bj, Muon.mean, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul] using h

open scoped Matrix.Norms.Frobenius in
/-- Frobenius triangle inequality for a finite family of slot contributions. -/
private lemma cv_fro_sum_le {m n ι : Type*} [Fintype m] [Fintype n]
    (Y : ι → Matrix m n ℝ) (U : Finset ι) :
    Real.sqrt (∑ i, ∑ k, ‖(∑ l ∈ U, Y l) i k‖ ^ 2) ≤
      ∑ l ∈ U, Real.sqrt (∑ i, ∑ k, ‖Y l i k‖ ^ 2) := by
  simpa only [Matrix.frobenius_norm_def, Real.rpow_two, Real.sqrt_eq_rpow] using
    (norm_sum_le U Y)

/-- Entrywise martingale convergence and summable bounds on the slot norms control the limit. -/
private lemma cv_fro_limit_of_sum_bounds {m n : ℕ} (Y : ℕ → Mat m n) (Z : Mat m n)
    (a : ℕ → ℝ) (K : ℝ)
    (hlim : ∀ i k, Tendsto (fun N => ∑ l ∈ Finset.range N, Y l i k) atTop (𝓝 (Z i k)))
    (ha0 : ∀ l, 0 ≤ a l) (ha : Summable a) (hsum : (∑' l, a l) ≤ K)
    (hb : ∀ l, fro (Y l) ≤ a l) : fro Z ≤ K := by
  have hmat : Tendsto (fun N => ∑ l ∈ Finset.range N, Y l) atTop (𝓝 Z) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => ?_
    simpa only [Matrix.sum_apply] using hlim i k
  have hc : Continuous (fun M : Mat m n => fro M) := by unfold fro; fun_prop
  have hfin : ∀ N, fro (∑ l ∈ Finset.range N, Y l) ≤ K := by
    intro N
    calc
      _ ≤ ∑ l ∈ Finset.range N, fro (Y l) := cv_fro_sum_le Y _
      _ ≤ ∑ l ∈ Finset.range N, a l := Finset.sum_le_sum fun l _ => hb l
      _ ≤ ∑' l, a l := ha.sum_le_tsum _ (fun l _ => ha0 l)
      _ ≤ K := hsum
  exact le_of_tendsto (hc.continuousAt.tendsto.comp hmat) (Eventually.of_forall hfin)

/-- A uniform finite budget for the actual slot contributions gives the covariance bound. -/
private lemma cv_Cj_bound_of_finite_slot_budget {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {m n B : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (w : ℕ → ℝ) (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (t : ℤ) (j : ℕ) (s : ℝ) (hs : 0 < s) (L K : ℝ)
    (hphi : ∀ᵐ ω ∂P, |phiJ w F S t j s ω| ≤ L)
    (A : Filtration ℕ mΩ) (hA0 : A 0 = ⊥) (hAe : (⨆ l, A l) = sigmaOthers F S t j)
    (hbudget : ∀ N, (∑ l ∈ Finset.range N, fro (Muon.mean P (fun ω =>
      (condExp (A (l + 1)) P (phiJ w F S t j s) ω -
        condExp (A l) P (phiJ w F S t j s) ω) •
        Xs (delBufAge w F S t j ω) s))) ≤ K) :
    fro (Cj w F S t j s) ≤ K := by
  let Y : ℕ → Mat m n := fun l => Muon.mean P (fun ω =>
    (condExp (A (l + 1)) P (phiJ w F S t j s) ω -
      condExp (A l) P (phiJ w F S t j s) ω) • Xs (delBufAge w F S t j ω) s)
  have hlim : Tendsto (fun N => ∑ l ∈ Finset.range N, Y l) atTop (𝓝 (Cj w F S t j s)) := by
    refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun k => ?_
    simpa only [Y, Muon.mean, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.sum_apply] using
      cv_Cj_expansion w F S t j s hs L hphi A hA0 hAe i k
  have hc : Continuous (fun M : Mat m n => fro M) := by unfold fro; fun_prop
  refine le_of_tendsto (hc.continuousAt.tendsto.comp hlim) (Eventually.of_forall fun N => ?_)
  exact (cv_fro_sum_le Y (Finset.range N)).trans (hbudget N)

/-- An almost surely zero multiplier has zero mean matrix. -/
private lemma cv_fro_mean_smul_zero {Ω : Type*} [MeasurableSpace Ω]
    {m n : ℕ} (P : Measure Ω) (h : Ω → ℝ) (X : Ω → Mat m n)
    (hz : h =ᵐ[P] fun _ => 0) : fro (Muon.mean P (fun ω => h ω • X ω)) = 0 := by
  have he : Muon.mean P (fun ω => h ω • X ω) = (0 : Mat m n) := by
    ext i k
    change (∫ ω, h ω * X ω i k ∂P) = 0
    apply integral_eq_zero_of_ae
    filter_upwards [hz] with ω hω
    simp [hω]
  rw [he]
  simp [fro]

/-- Sum the actual martingale slot estimates to obtain the per-age covariance estimate. -/
private lemma cv_covariance_per_age (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B)
      (t : ℤ) (w : ℕ → ℝ),
      ((∀ k, 0 ≤ w k) ∧ Summable w ∧ (∀ k, w k ≤ 1) ∧ (∑' k, w k) ≤ 1) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B → ∀ s : ℝ, s0 ≤ s → ∀ j,
      fro (Cj w F S t j s) ≤ C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C0, hslot⟩ := cv_martingale_slot_bound s0 hs0 CS γ hγ
  obtain ⟨L, hL⟩ := cv_phi_bound s0 hs0 CS γ hγ
  let C := max C0 0
  have hC : 0 ≤ C := le_max_right _ _
  refine ⟨C, ?_⟩
  intro Ω mΩ m n B P _ F S t w hw hSo hSi hm hn s hs j
  obtain ⟨hw0, hw, hw1, hws⟩ := hw
  have hsp : 0 < s := hs0.trans_le hs
  have hB : 0 < (B : ℝ) := by exact_mod_cast F.hB
  have hphi := hL Ω m n B P F S t j w hSo hSi hm hn (hw0 j) (hw1 j) s hs
  by_cases hwne : ∃ k, w k ≠ 0
  · have hW : WeightSeq w := ⟨hw0, hw, hwne⟩
    have hI := cv_alpha2_integrable w F S t j s CS γ hsp hγ hSo hSi hm hn (hw0 j) (hw1 j)
    obtain ⟨A, hA, hA0, hAe⟩ := cv_sample_filtration F S t j
    let M : ℤ × Fin B → MeasurableSpace Ω := fun p =>
      MeasurableSpace.comap (S.zw p.1 p.2) inferInstance
    let d : ℤ × Fin B := (t + 1 - (j : ℤ), slotOne F.hB)
    let f : ℕ → ℝ := fun l => fro (Muon.mean P (fun ω =>
      (condExp (A (l + 1)) P (phiJ w F S t j s) ω -
        condExp (A l) P (phiJ w F S t j s) ω) • Xs (delBufAge w F S t j ω) s))
    let K := C * w j ^ 2 / (s * Real.sqrt s * B * Real.sqrt (B : ℝ))
    have hK : 0 ≤ K := by dsimp [K]; positivity
    have hreveal : ∀ p, p ≠ d → A (Encodable.encode p + 1) = A (Encodable.encode p) ⊔ M p := by
      intro p hp
      rw [hA, hA]
      exact cv_encoded_reveal M d p hp
    have hpast : ∀ p, A (Encodable.encode p) ≤ ⨆ (q : ℤ × Fin B) (_ : q ≠ p), M q := by
      intro p
      rw [hA]
      exact cv_encoded_past_le M d p
    have hgap : ∀ l, (∀ p, p ≠ d → Encodable.encode p ≠ l) → f l = 0 := by
      intro l hg
      have he : A (l + 1) = A l := by
        rw [hA, hA]
        exact cv_encoded_no_reveal M d l hg
      apply cv_fro_mean_smul_zero
      rw [he]
      exact Eventually.of_forall fun _ => sub_self _
    have hzero : ∀ l, (∀ (k : ℕ) (a : Fin B),
        Encodable.encode (t + 1 - (k : ℤ), a) ≠ l) → f l = 0 := by
      intro l hl
      by_cases hr : ∃ p : ℤ × Fin B, p ≠ d ∧ Encodable.encode p = l
      · obtain ⟨p, hp, hcode⟩ := hr
        have hfuture : t + 1 < p.1 := by
          by_contra hnot
          have ht : p.1 ≤ t + 1 := le_of_not_gt hnot
          have he : (t + 1 - (((t + 1 - p.1).toNat : ℕ) : ℤ), p.2) = p := by
            apply Prod.ext
            · dsimp
              rw [Int.toNat_of_nonneg (sub_nonneg.mpr ht)]
              ring
            · rfl
          apply hl (t + 1 - p.1).toNat p.2
          rw [he]
          exact hcode
        subst l
        apply cv_fro_mean_smul_zero
        rw [hreveal p hp]
        exact cv_future_increment_zero (A (Encodable.encode p)) w F S t j p hfuture
          (hpast p) s hsp hI
      · apply hgap l
        intro p hp he
        exact hr ⟨p, hp, he⟩
    have hper : ∀ (k : ℕ) (a : Fin B),
        f (Encodable.encode (t + 1 - (k : ℤ), a)) ≤ K * w k := by
      intro k a
      let p : ℤ × Fin B := (t + 1 - (k : ℤ), a)
      by_cases hp : p = d
      · have he : f (Encodable.encode p) = 0 := hgap _ (by
          intro q hq hcode
          exact hq ((Encodable.encode_injective hcode).trans hp))
        change f (Encodable.encode p) ≤ K * w k
        rw [he]
        exact mul_nonneg hK (hw0 k)
      · have hb : f (Encodable.encode p) ≤
            C0 * w j ^ 2 * w k / (s * Real.sqrt s * B * Real.sqrt (B : ℝ)) := by
          simpa only [f, hreveal p hp] using
            hslot Ω (A (Encodable.encode p)) m n B P F S w hW t j k a hp
              (hpast p) hSo hSi hm hn (hw0 j) (hw1 j) (hw0 k) (hw1 k) s hs
        calc
          _ ≤ C0 * w j ^ 2 * w k / (s * Real.sqrt s * B * Real.sqrt (B : ℝ)) := hb
          _ ≤ C * w j ^ 2 * w k / (s * Real.sqrt s * B * Real.sqrt (B : ℝ)) := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C0 0) (sq_nonneg (w j))) (hw0 k)
          _ = K * w k := by dsimp [K]; ring
    apply cv_Cj_bound_of_finite_slot_budget w F S t j s hsp (L * w j ^ 2 / s)
      (C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) hphi A hA0 hAe
    intro N
    have hb := cv_encoded_weight_budget t w hw0 hw hws f K hK hzero hper N
    have he : K * B = C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
      dsimp [K]
      field_simp
      <;> ring
    exact hb.trans_eq he
  · have hwj : w j = 0 := by by_contra hj; exact hwne ⟨j, hj⟩
    have hz : phiJ w F S t j s =ᵐ[P] fun _ => 0 := by
      filter_upwards [hphi] with ω hω
      exact abs_eq_zero.mp (le_antisymm (by simpa [hwj] using hω) (abs_nonneg _))
    have hbj : bj w F S t j s = 0 := by
      unfold bj
      rw [integral_congr_ae hz]
      simp
    have he : fro (Cj w F S t j s) = 0 := by
      apply cv_fro_mean_smul_zero
      filter_upwards [hz] with ω hω
      simp [hω, hbj]
    rw [he, hwj]
    simp

/-- lem:app-drift-covariance, general weight sequence (`eqn:app-drift-weights`). Snapshot
`cr-2026-10-23`. LaTeX (`section.tex` l.493–501, verbatim):

\begin{lemma}[Covariance of the Gram coefficient and the mixed resolvent]\label{lem:app-drift-covariance}
Let $s_\circ>0$. For every age $j$ and every $s\ge s_\circ$,
\begin{equation}\label{eqn:app-drift-covariance}
\norm{\mathcal C_j}_\F\le\frac{C\,\emaw j^2}{s^{3/2}\sqrt B},\qquad\text{hence}\qquad
\sum_{j\ge0}\norm{\mathcal C_j}_\F\le\frac{C\,\sw2}{s^{3/2}\sqrt B},
\end{equation}
with $C$ depending only on $(s_\circ,C_\Sigma,\gamma_\star)$.
\end{lemma}


Weights: `w` nonnegative, summable, `w_j ≤ 1`, `∑ w_j ≤ 1` (`eqn:app-drift-weights`). The conclusion
is the source's two bounds for `𝒞_j = Cj w F S t j s`, each with its integrability/summability claim:
the entrywise integrability of the summand of `𝒞_j` (no junk from `Bochner`), the per-age bound with
`sumPow w 2 = ∑ w_j²` in place of the summed EMA power, and `Summable` of the norms with the summed
bound. The constant `C` depends only on `(s₀, C_Σ, γ⋆)`. -/
theorem lem_app_drift_covariance_weights (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (w : ℕ → ℝ),
      ((∀ j, 0 ≤ w j) ∧ Summable w ∧ (∀ j, w j ≤ 1) ∧ (∑' j, w j) ≤ 1) →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        (∀ (j : ℕ) (i : Fin m) (k : Fin n),
            Integrable (fun ω => (phiJ w F S t j s ω - bj w F S t j s) *
              Xs (delBufAge w F S t j ω) s i k) P) ∧
        (∀ j : ℕ, fro (Cj w F S t j s) ≤ C * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) ∧
        Summable (fun j : ℕ => fro (Cj w F S t j s)) ∧
        (∑' j : ℕ, fro (Cj w F S t j s)) ≤
          C * sumPow w 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := cv_covariance_per_age s0 hs0 CS γ hγ
  refine ⟨C, ?_⟩
  intro Ω _ m n B P _ F S t w hw hSo hSi hm hn s hs
  exact cv_assemble w F S t s C (hs0.trans_le hs) hw.1 hw.2.1 hw.2.2.1
    (hC Ω m n B P F S t w hw hSo hSi hm hn s hs)

/-- lem:app-drift-covariance (`eqn:app-drift-covariance`) at the EMA weights `w_j = emaw j`
(`emaW F.β`, `sw2 = sPow F.β 2`). Snapshot `cr-2026-10-23`. LaTeX (`section.tex` l.493–501,
verbatim):

\begin{lemma}[Covariance of the Gram coefficient and the mixed resolvent]\label{lem:app-drift-covariance}
Let $s_\circ>0$. For every age $j$ and every $s\ge s_\circ$,
\begin{equation}\label{eqn:app-drift-covariance}
\norm{\mathcal C_j}_\F\le\frac{C\,\emaw j^2}{s^{3/2}\sqrt B},\qquad\text{hence}\qquad
\sum_{j\ge0}\norm{\mathcal C_j}_\F\le\frac{C\,\sw2}{s^{3/2}\sqrt B},
\end{equation}
with $C$ depending only on $(s_\circ,C_\Sigma,\gamma_\star)$.
\end{lemma}


Corollary of `lem_app_drift_covariance_weights`: the EMA weights lie in the class
(`emaW_weightClass`, `Muon.DetEquiv.WeightClass` contains the source's conditions). -/
theorem lem_app_drift_covariance (s0 : ℝ) (hs0 : 0 < s0) (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
      (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ),
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS →
      (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, s0 ≤ s →
        (∀ (j : ℕ) (i : Fin m) (k : Fin n),
            Integrable (fun ω => (phiJ (Muon.emaW F.β) F S t j s ω -
              bj (Muon.emaW F.β) F S t j s) *
              Xs (delBufAge (Muon.emaW F.β) F S t j ω) s i k) P) ∧
        (∀ j : ℕ, fro (Cj (Muon.emaW F.β) F S t j s) ≤
          C * Muon.emaW F.β j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))) ∧
        Summable (fun j : ℕ => fro (Cj (Muon.emaW F.β) F S t j s)) ∧
        (∑' j : ℕ, fro (Cj (Muon.emaW F.β) F S t j s)) ≤
          C * Muon.sPow F.β 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) := by
  obtain ⟨C, hC⟩ := lem_app_drift_covariance_weights s0 hs0 CS γ hγ
  refine ⟨C, fun Ω _ m n B P _ F S t hSo hSi hm hn s hs => ?_⟩
  obtain ⟨⟨h0, hsum, _⟩, hle, htsum⟩ := emaW_weightClass F.β F.hβ
  exact hC Ω m n B P F S t (Muon.emaW F.β) ⟨h0, hsum, hle, htsum⟩ hSo hSi hm hn s hs

end Muon.Drift

end
