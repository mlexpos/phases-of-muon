import Muon.Drift.Defs
import Muon.Drift.Kernel
import Muon.Drift.Coefficients
import Muon.Drift.Covariance

/-!
# Muon.Drift: exact mixed identity and tail bound (work package L-C.7)

Statements of `lem:app-drift-exact` and of `thm:app-drift-mixed`(ii), snapshot `cr-2026-10-23`
(`sections/03-drift/section.tex` l.571–576 and l.99–115). Owned declarations:

* `lem_app_drift_exact` (EMA record, `w := Muon.emaW F.β`) and `lem_app_drift_exact_weights`
  (general weight sequence in `WeightClass`, card §5 rule (a)).
* `thm_app_drift_mixed_ii`: the bound `‖𝓗(s)‖_F ≤ C/s` (`s ≥ 1`) together with the `T`-bound
  `‖T(s)‖_F ≤ C_Σ/s` (`s > 0`), the latter from `Muon.Drift.Kernel` (L-C.4). Part (i) of
  `thm:app-drift-mixed` belongs to L-C.9 and is not stated here.

Objects come from `Muon.Drift.Defs` (`Hmix`, `Tcand`, `delAlpha1`, `delAlpha2`, `delBufAge`,
`specOutFM`, `specInFM`); the constant `C` of (ii) is placed before every model datum.
The hypotheses are those of the source: `DriftBound` (`max(N_out,N_in) ≤ γ⋆B`,
`‖Σ_out‖,‖Σ_in‖ ≤ C_Σ`), `‖Â‖_F = 1` (the field `F.hA`), and `WeightClass w`
(`eqn:app-drift-weights`). `WeightClass` includes `WeightSeq`, which contains `∃ j, w j ≠ 0`
("not all zero", CORRECTIONS.md item 6, ruling L2); it removes only the trivial case `w ≡ 0`,
where `𝓗 = T = 0`. The series of the exact identity is stated as `HasSum`, so its convergence is
part of the claim.
-/

-- Docstrings quote the frozen LaTeX verbatim, which has lines over 100 characters.
set_option linter.style.longLine false

open MeasureTheory Filter Topology Set
open scoped Matrix ENNReal
open Matrix
open Muon Muon.Setup Muon.DetEquiv

namespace Muon.Drift

variable {m n B : ℕ}

/-! ### Private helpers for `lem_app_drift_exact_weights` (task P-C.7.P1) -/

section PdxHelpers

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma pdx_opNorm_nonneg {p q : ℕ} (K : Mat p q) : 0 ≤ opNorm K := by
  unfold opNorm; exact norm_nonneg _

private lemma pdx_sq_mulVec {a b : ℕ} (K : Mat a b) (x : Vec b) :
    ∑ i, (K *ᵥ x) i ^ 2 ≤ opNorm K ^ 2 * ∑ i, x i ^ 2 := by
  have h2 : ‖Matrix.toEuclideanLin K (WithLp.toLp 2 x)‖ ≤ opNorm K * ‖WithLp.toLp 2 x‖ := by
    have := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin K)).le_opNorm (WithLp.toLp 2 x)
    simpa [opNorm] using this
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  rw [mul_pow, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
      Real.sq_sqrt (by positivity)] at h3
  simpa [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
      Real.norm_eq_abs, sq_abs] using h3

private lemma pdx_entry_le {a b : ℕ} (K : Mat a b) (x : Vec b) (i : Fin a) :
    |(K *ᵥ x) i| ≤ opNorm K * eucNorm x := by
  have h := pdx_sq_mulVec K x
  have h1 : (K *ᵥ x) i ^ 2 ≤ ∑ k, (K *ᵥ x) k ^ 2 :=
    Finset.single_le_sum (f := fun k => (K *ᵥ x) k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := Real.abs_le_sqrt (h1.trans h)
  refine h2.trans ?_
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pdx_opNorm_nonneg _)]
  rfl

private lemma pdx_coord_le {b : ℕ} (x : Vec b) (i : Fin b) : |x i| ≤ eucNorm x := by
  have h1 : x i ^ 2 ≤ ∑ k, x k ^ 2 :=
    Finset.single_le_sum (f := fun k => x k ^ 2) (fun k _ => sq_nonneg _) (Finset.mem_univ i)
  exact Real.abs_le_sqrt h1

private lemma pdx_L1 [IsProbabilityMeasure P]
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
  have hCS0 : 0 ≤ CSig := (pdx_opNorm_nonneg _).trans hC.1
  have hnn : 0 ≤ 7 * CSig * γ := by positivity
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hq0) hqm.aestronglyMeasurable]
  have h2 : ∫⁻ x, ENNReal.ofReal (q x) ∂(gaussPair m n) = eLpNorm q 1 (gaussPair m n) := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, Real.norm_of_nonneg (hq0 x)]
    all_goals exact hqm.aestronglyMeasurable
  rw [h2]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hl1).trans_eq (ENNReal.toReal_ofReal hnn)

open scoped MatrixOrder in
private lemma pdx_rOut_outer_rIn {m n B : ℕ} (F : FrozenParams m n B) (z : Vec m) (w : Vec n) :
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

/-- One sample term: `B⁻¹ • sampleTerm = d • (u ⊗ v)`. -/
private lemma pdx_sample {m n B : ℕ} (F : FrozenParams m n B) (S : FrozenSamples P m n B)
    (s : ℤ) (a : Fin B) (ω : Ω) :
    (B : ℝ)⁻¹ • sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) • outer (momU F.C B (S.zw s a ω)) (momV F.C B (S.zw s a ω)) := by
  have hB : (0 : ℝ) ≤ B := Nat.cast_nonneg B
  have hcc : (Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹ = (B : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hB]
  have e1 : sampleTerm F S s a ω =
      resid F.A (S.zw s a ω) •
        outer (Matrix.mulVec (rOut F.C) (S.zw s a ω).1)
        (Matrix.mulVec (rIn F.C) (S.zw s a ω).2) := by
    unfold sampleTerm
    rw [pdx_rOut_outer_rIn]
    rfl
  rw [e1]
  unfold momU momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  rw [← hcc]
  ring

private lemma pdx_decomp [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) (a : Fin B) :
    ∀ᵐ ω ∂P, WeightedBuf w F S t ω = WeightedBufDel w F S t (t + 1 - (j : ℤ)) a ω +
      (w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        outer (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h := weightedBuf_eq_del_add w F S t (t + 1 - (j : ℤ)) a j rfl ω (hω t)
  rw [h, pdx_sample, smul_smul]

end PdxHelpers

section PdxHelpers2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma pdx_term_eq {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (M : Mat m n) (s : ℝ) (j : ℕ) (t : ℤ) (ω : Ω) :
    Rs M s * (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω) =
      ∑ a : Fin B, outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs M s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) := by
  rw [frozenBatchG_eq_sum, Finset.smul_sum, Finset.smul_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [pdx_sample, Matrix.mul_smul, Matrix.mul_smul, Muon.outer, Matrix.mul_vecMulVec]
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply, Pi.smul_apply]
  ring

private lemma pdx_series [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) :
    ∀ᵐ ω ∂P, HasSum (fun j : ℕ => ∑ a : Fin B,
      outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) (Xs (WeightedBuf w F S t ω) s) := by
  filter_upwards [weightedBuf_summable_ae w hw.1 F S] with ω hω
  have h1 : HasSum (fun j : ℕ => w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω)
      (WeightedBuf w F S t ω) := (hω t).hasSum
  let f : Mat m n →+ Mat m n :=
    { toFun := fun N => Rs (WeightedBuf w F S t ω) s * N
      map_zero' := Matrix.mul_zero _
      map_add' := fun _ _ => Matrix.mul_add _ _ _ }
  have h2 : HasSum (fun j : ℕ => Rs (WeightedBuf w F S t ω) s *
      (w j • frozenBatchG F S (t + 1 - (j : ℤ)) ω))
      (Rs (WeightedBuf w F S t ω) s * WeightedBuf w F S t ω) :=
    h1.map f (continuous_const.matrix_mul continuous_id)
  simp only [pdx_term_eq] at h2
  exact h2

end PdxHelpers2

section PdxHelpers3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma pdx_hQ {m n B : ℕ} (F : FrozenParams m n B) :
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

private lemma pdx_meas_WB {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) : Measurable (WeightedBuf w F S t) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := pdx_hQ F
  unfold WeightedBuf
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul ?_ (w j)
  show Measurable (fun ω => ((B : ℝ))⁻¹ • ∑ a : Fin B,
    (dotProduct (S.zw (t + 1 - (j : ℤ)) a ω).1 (Matrix.mulVec F.A (S.zw (t + 1 - (j : ℤ)) a ω).2)) •
      (rOut F.C * outer (S.zw (t + 1 - (j : ℤ)) a ω).1 (S.zw (t + 1 - (j : ℤ)) a ω).2 * rIn F.C))
  exact (Finset.measurable_sum _ fun a _ => hQ.comp (S.meas _ _)).const_smul ((B : ℝ)⁻¹)

private lemma pdx_meas_del {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t s : ℤ) (a : Fin B) :
    Measurable (WeightedBufDel w F S t s a) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := pdx_hQ F
  unfold WeightedBufDel
  refine Measurable.tsum fun j => ?_
  refine Measurable.const_smul (Measurable.const_smul ?_ ((B : ℝ)⁻¹)) (w j)
  refine Finset.measurable_sum _ fun b _ => ?_
  by_cases h : t + 1 - (j : ℤ) = s ∧ b = a
  · simp only [if_pos h]; exact measurable_const
  · simp only [if_neg h]; exact hQ.comp (S.meas _ _)

private lemma pdx_Rs_measurable {a b : ℕ} (s : ℝ) : Measurable (fun M : Mat a b => Rs M s) := by
  have hdet : Measurable (fun X : Mat a a => X.det) := (continuous_id.matrix_det).measurable
  have hadj : Measurable (fun X : Mat a a => X.adjugate) :=
    (continuous_id.matrix_adjugate).measurable
  have hinv : (fun X : Mat a a => X⁻¹) = fun X => Ring.inverse X.det • X.adjugate :=
    funext fun X => Matrix.inv_def X
  have h1 : Measurable (fun X : Mat a a => Ring.inverse X.det) := by
    simp only [Ring.inverse_eq_inv]
    exact hdet.inv
  have hinvm : Measurable (fun X : Mat a a => X⁻¹) := by
    rw [hinv]
    exact h1.smul hadj
  have hc : Continuous (fun M : Mat a b => M * Mᵀ + s • (1 : Mat a a)) := by fun_prop
  exact hinvm.comp hc.measurable

private lemma pdx_mv {α : Type*} [MeasurableSpace α] {a b : ℕ} (K : α → Mat a b) (x : α → Vec b)
    (hK : Measurable K) (hx : Measurable x) : Measurable (fun q => K q *ᵥ x q) := by
  refine measurable_pi_iff.2 fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.measurable_sum _ fun l _ =>
    ((measurable_pi_apply l).comp ((measurable_pi_apply i).comp hK)).mul
      ((measurable_pi_apply l).comp hx)

end PdxHelpers3

section PdxHelpers4

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma pdx_pt_bound {m n : ℕ} (M : Mat m n) (s c : ℝ) (hs : 0 < s) (u : Vec m) (v : Vec n)
    (i : Fin m) (k : Fin n) :
    |(outer (c • (Rs M s *ᵥ u)) v) i k| ≤ |c| / s * (eucNorm u * eucNorm v) := by
  simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  have h1 := pdx_entry_le (Rs M s) u i
  have h3 : opNorm (Rs M s) ≤ 1 / s := (lem_app_de_resolvent M s hs).1
  have h2 := pdx_coord_le v k
  have hu0 : 0 ≤ eucNorm u := Real.sqrt_nonneg _
  have hv0 : 0 ≤ eucNorm v := Real.sqrt_nonneg _
  rw [abs_mul, abs_mul]
  have h4 : |(Rs M s *ᵥ u) i| ≤ 1 / s * eucNorm u :=
    h1.trans (mul_le_mul_of_nonneg_right h3 hu0)
  calc |c| * |(Rs M s *ᵥ u) i| * |v k|
      ≤ |c| * (1 / s * eucNorm u) * eucNorm v :=
        mul_le_mul (mul_le_mul_of_nonneg_left h4 (abs_nonneg _)) h2 (abs_nonneg _)
          (mul_nonneg (abs_nonneg _) (by positivity))
    _ = |c| / s * (eucNorm u * eucNorm v) := by ring

private lemma pdx_term_meas {m n B : ℕ} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) (j : ℕ) (a : Fin B) (i : Fin m) (k : Fin n) :
    Measurable (fun ω => (outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k) := by
  have hdm : Measurable (fun ω => resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp (S.meas _ _)
  have hum : Measurable (fun ω => momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp (S.meas _ _)
  have hvm : Measurable (fun ω => momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) :=
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp (S.meas _ _)
  have hR : Measurable (fun ω => Rs (WeightedBuf w F S t ω) s) :=
    (pdx_Rs_measurable s).comp (pdx_meas_WB w F S t)
  have hmv := pdx_mv _ _ hR hum
  simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  exact ((measurable_const.mul hdm).mul ((measurable_pi_apply i).comp hmv)).mul
    ((measurable_pi_apply k).comp hvm)

private lemma pdx_term_int [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s)
    (γ CSig : ℝ) (hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ)) (hγ : 0 ≤ γ)
    (hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig)
    (j : ℕ) (a : Fin B) (i : Fin m) (k : Fin n) :
    Integrable (fun ω => (outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k) P := by
  have hL1 := (pdx_L1 F S γ CSig hdim hγ hC (t + 1 - (j : ℤ)) a).1
  refine (hL1.const_mul (w j / s)).mono' (pdx_term_meas w F S t s j a i k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs]
  refine (pdx_pt_bound _ s _ hs _ _ i k).trans (le_of_eq ?_)
  rw [abs_mul, abs_of_nonneg (hw.1.1 j)]
  ring

end PdxHelpers4

section PdxHelpers5

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

private lemma pdx_Phi_meas {m n B : ℕ} (F : FrozenParams m n B) (c s : ℝ) (i : Fin m) (k : Fin n) :
    Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      (outer ((c * resid F.A q.2) •
        (Rs (q.1 + (c * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) s *ᵥ
          momU F.C B q.2)) (momV F.C B q.2)) i k) := by
  have hd : Measurable (fun q : Mat m n × (Vec m × Vec n) => resid F.A q.2) :=
    (by unfold resid; fun_prop : Measurable fun x : Vec m × Vec n => resid F.A x).comp measurable_snd
  have hu : Measurable (fun q : Mat m n × (Vec m × Vec n) => momU F.C B q.2) :=
    (by unfold momU; fun_prop : Measurable (momU F.C B)).comp measurable_snd
  have hv : Measurable (fun q : Mat m n × (Vec m × Vec n) => momV F.C B q.2) :=
    (by unfold momV; fun_prop : Measurable (momV F.C B)).comp measurable_snd
  have hM : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      q.1 + (c * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) := by
    refine measurable_pi_iff.2 fun i' => measurable_pi_iff.2 fun k' => ?_
    simp only [Matrix.add_apply, Matrix.smul_apply, Muon.outer, Matrix.vecMulVec_apply, smul_eq_mul]
    have h1 : Measurable (fun q : Mat m n × (Vec m × Vec n) => q.1 i' k') :=
      (measurable_pi_apply k').comp ((measurable_pi_apply i').comp measurable_fst)
    have h2 : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
        c * resid F.A q.2 * (momU F.C B q.2 i' * momV F.C B q.2 k')) :=
      ((measurable_const (a := c)).mul hd).mul
        (((measurable_pi_apply i').comp hu).mul ((measurable_pi_apply k').comp hv))
    exact h1.add h2
  have hR : Measurable (fun q : Mat m n × (Vec m × Vec n) =>
      Rs (q.1 + (c * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) s) :=
    (pdx_Rs_measurable s).comp hM
  have hmv := pdx_mv _ _ hR hu
  simp only [Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  exact ((measurable_const.mul hd).mul ((measurable_pi_apply i).comp hmv)).mul
    ((measurable_pi_apply k).comp hv)

private lemma pdx_slot [IsProbabilityMeasure P] {m n B : ℕ} (w : ℕ → ℝ) (hw : WeightClass w)
    (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ) {s : ℝ} (hs : 0 < s) (j : ℕ)
    (a : Fin B) (i : Fin m) (k : Fin n) :
    ∫ ω, (outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k ∂P =
      ∫ ω, (delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) i k ∂P := by
  set s' : ℤ := t + 1 - (j : ℤ) with hs'
  set Φ : Mat m n × (Vec m × Vec n) → ℝ := fun q =>
    (outer ((w j * resid F.A q.2) •
        (Rs (q.1 + (w j * resid F.A q.2) • outer (momU F.C B q.2) (momV F.C B q.2)) s *ᵥ
          momU F.C B q.2)) (momV F.C B q.2)) i k with hΦ
  have hΦm : Measurable Φ := pdx_Phi_meas F (w j) s i k
  have hpair : ∀ b : Fin B, Measurable (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω)) :=
    fun b => (pdx_meas_del w F S t s' b).prodMk (S.meas _ _)
  have step1 : ∀ b : Fin B, ∫ ω, (outer ((w j * resid F.A (S.zw s' b ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw s' b ω)))
        (momV F.C B (S.zw s' b ω))) i k ∂P =
      ∫ ω, Φ (WeightedBufDel w F S t s' b ω, S.zw s' b ω) ∂P := by
    intro b
    refine integral_congr_ae ?_
    filter_upwards [pdx_decomp w hw F S t j b] with ω hω
    simp only [hΦ]
    rw [hω]
  have step2 : ∀ b : Fin B, ∫ ω, Φ (WeightedBufDel w F S t s' b ω, S.zw s' b ω) ∂P =
      ∫ q, Φ q ∂(P.map (fun ω => (WeightedBufDel w F S t s' b ω, S.zw s' b ω))) := by
    intro b
    rw [integral_map (hpair b).aemeasurable hΦm.aestronglyMeasurable]
  have step3 : ∫ ω, Φ (WeightedBufDel w F S t s' (slotOne F.hB) ω,
      S.zw s' (slotOne F.hB) ω) ∂P = ∫ ω, (delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) i k ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hcol := (lem_app_drift_column (WeightedBufDel w F S t s' (slotOne F.hB) ω +
        (w j * resid F.A (S.zw s' (slotOne F.hB) ω)) •
          outer (momU F.C B (S.zw s' (slotOne F.hB) ω)) (momV F.C B (S.zw s' (slotOne F.hB) ω)))
      (WeightedBufDel w F S t s' (slotOne F.hB) ω) (w j * resid F.A (S.zw s' (slotOne F.hB) ω)) s
      (momU F.C B (S.zw s' (slotOne F.hB) ω)) (momV F.C B (S.zw s' (slotOne F.hB) ω)) rfl hs).1
    simp only [hΦ]
    rw [hcol]
    simp only [delAlpha1, delAlpha2, delBufAge, ageU, ageV, ageD, sampleD, Muon.outer,
      Matrix.mul_vecMulVec, Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
      Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    simp only [resid]
    ring
  rw [step1 a, step2 a, weightedBufDel_law_slot_invariant w hw F S t s' a (slotOne F.hB),
    ← step2 (slotOne F.hB), step3]

end PdxHelpers5

private theorem pdx_main {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {m n B : ℕ} {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) (hs : 0 < s) :
    HasSum (fun j : ℕ => (B : ℝ) • Muon.mean P (fun ω =>
        delAlpha1 w F S t j s ω • (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 w F S t j s ω • (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))))
      (Hmix w F S t s) := by
  have hBpos : (0 : ℝ) < B := by exact_mod_cast F.hB
  set γ : ℝ := ((m : ℝ) + n) / B with hγdef
  set CSig : ℝ := opNorm F.C.Sout + opNorm F.C.Sin with hCdef
  have hγ : 0 ≤ γ := by positivity
  have hdim : (m : ℝ) ≤ γ * (B : ℝ) ∧ (n : ℝ) ≤ γ * (B : ℝ) := by
    have : γ * (B : ℝ) = (m : ℝ) + n := by rw [hγdef]; field_simp
    rw [this]
    exact ⟨by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)], by linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]⟩
  have hC : opNorm F.C.Sout ≤ CSig ∧ opNorm F.C.Sin ≤ CSig :=
    ⟨by linarith [pdx_opNorm_nonneg F.C.Sin], by linarith [pdx_opNorm_nonneg F.C.Sout]⟩
  have hCS0 : 0 ≤ CSig := add_nonneg (pdx_opNorm_nonneg _) (pdx_opNorm_nonneg _)
  have hw0 := hw.1.1
  refine Pi.hasSum.2 fun i => Pi.hasSum.2 fun k => ?_
  set Tm : ℕ → Fin B → Ω → ℝ := fun j a ω => (outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
        (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
        (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k with hTm
  set qa : ℕ → Fin B → Ω → ℝ := fun j a ω =>
    |resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)| * eucNorm (momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) *
      eucNorm (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω)) with hqa
  have hL1 := fun j a => pdx_L1 F S γ CSig hdim hγ hC (t + 1 - (j : ℤ)) a
  have hTint : ∀ j a, Integrable (Tm j a) P := fun j a =>
    pdx_term_int w hw F S t hs γ CSig hdim hγ hC j a i k
  have hbd : ∀ j ω, |∑ a : Fin B, Tm j a ω| ≤ ∑ a : Fin B, w j / s * qa j a ω := by
    intro j ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    refine (pdx_pt_bound _ s _ hs _ _ i k).trans (le_of_eq ?_)
    simp only [hqa]
    rw [abs_mul, abs_of_nonneg (hw0 j)]
    ring
  have hFint : ∀ j, Integrable (fun ω => ∑ a : Fin B, Tm j a ω) P := fun j =>
    integrable_finsetSum _ fun a _ => hTint j a
  have hgi : ∀ j, Integrable (fun ω => ∑ a : Fin B, w j / s * qa j a ω) P := fun j =>
    integrable_finsetSum _ fun a _ => (hL1 j a).1.const_mul _
  have hnormle : ∀ j, ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P ≤ (B * (7 * CSig * γ) / s) * w j := by
    intro j
    calc ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P ≤ ∫ ω, ∑ a : Fin B, w j / s * qa j a ω ∂P :=
          integral_mono (hFint j).norm (hgi j) fun ω => by
            rw [Real.norm_eq_abs]; exact hbd j ω
      _ = ∑ a : Fin B, w j / s * (∫ ω, qa j a ω ∂P) := by
          rw [integral_finsetSum _ fun a _ => (hL1 j a).1.const_mul _]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [integral_const_mul]
      _ ≤ ∑ a : Fin B, w j / s * (7 * CSig * γ) := by
          refine Finset.sum_le_sum fun a _ => ?_
          exact mul_le_mul_of_nonneg_left (hL1 j a).2 (div_nonneg (hw0 j) hs.le)
      _ = (B * (7 * CSig * γ) / s) * w j := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hsum : Summable fun j => ∫ ω, ‖∑ a : Fin B, Tm j a ω‖ ∂P :=
    Summable.of_nonneg_of_le (fun j => integral_nonneg fun ω => norm_nonneg _) hnormle
      (hw.1.2.1.mul_left _)
  have hHS := hasSum_integral_of_summable_integral_norm hFint hsum
  have hE : ∫ ω, ∑' j, ∑ a : Fin B, Tm j a ω ∂P = Hmix w F S t s i k := by
    unfold Hmix Muon.mean
    simp only [Matrix.of_apply]
    refine integral_congr_ae ?_
    filter_upwards [pdx_series w hw F S t s] with ω hω
    have h' : HasSum (fun j => ∑ a : Fin B, Tm j a ω) (Xs (WeightedBuf w F S t ω) s i k) := by
      let f : Mat m n →+ ℝ :=
        { toFun := fun X => X i k, map_zero' := rfl, map_add' := fun _ _ => rfl }
      have h2 : HasSum (fun j => (∑ a : Fin B, outer ((w j * resid F.A (S.zw (t + 1 - (j : ℤ)) a ω)) •
          (Rs (WeightedBuf w F S t ω) s *ᵥ momU F.C B (S.zw (t + 1 - (j : ℤ)) a ω)))
          (momV F.C B (S.zw (t + 1 - (j : ℤ)) a ω))) i k) (Xs (WeightedBuf w F S t ω) s i k) :=
        hω.map f ((continuous_apply k).comp (continuous_apply i))
      simpa only [hTm, Matrix.sum_apply] using h2
    exact h'.tsum_eq
  rw [hE] at hHS
  convert hHS using 1
  funext j
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.mean, Matrix.of_apply]
  rw [integral_finsetSum _ fun a _ => hTint j a]
  rw [Finset.sum_congr rfl fun a _ => pdx_slot w hw F S t hs j a i k]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- `lem:app-drift-exact`, snapshot `cr-2026-10-23`. Source, verbatim:
```latex
\begin{lemma}[Exact mixed identity]\label{lem:app-drift-exact}
In the frozen-state model, for every $s>0$,
\begin{equation}\label{eqn:app-drift-exact}
\mathcal H(s)=B\sum_{j\ge0}\EE\Big[\alpha_{1,j}\,R_0^{(j)}(\mathsf u_j\tensor\mathsf v_j)-\alpha_{2,j}\,\mathsf X_0^{(j)}(\mathsf v_j\tensor\mathsf v_j)\Big].
\end{equation}
\end{lemma}
```
Record: the EMA case `w = Muon.emaW F.β` of the frozen-state model. -/
theorem lem_app_drift_exact {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
    (s : ℝ) (hs : 0 < s) :
    HasSum (fun j : ℕ => (B : ℝ) • Muon.mean P (fun ω =>
        delAlpha1 (Muon.emaW F.β) F S t j s ω •
            (Rs (delBufAge (Muon.emaW F.β) F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 (Muon.emaW F.β) F S t j s ω •
            (Xs (delBufAge (Muon.emaW F.β) F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))))
      (Hmix (Muon.emaW F.β) F S t s) := by
  exact pdx_main (emaW_weightClass F.β F.hβ) F S t s hs

/-- `lem:app-drift-exact` for a general weight sequence `w` in `eqn:app-drift-weights`
(card §5 rule (a): helper of the record `lem_app_drift_exact`). Source as in
`lem_app_drift_exact`, verbatim:
```latex
\begin{lemma}[Exact mixed identity]\label{lem:app-drift-exact}
In the frozen-state model, for every $s>0$,
\begin{equation}\label{eqn:app-drift-exact}
\mathcal H(s)=B\sum_{j\ge0}\EE\Big[\alpha_{1,j}\,R_0^{(j)}(\mathsf u_j\tensor\mathsf v_j)-\alpha_{2,j}\,\mathsf X_0^{(j)}(\mathsf v_j\tensor\mathsf v_j)\Big].
\end{equation}
\end{lemma}
```
-/
theorem lem_app_drift_exact_weights {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {w : ℕ → ℝ} (hw : WeightClass w) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (s : ℝ) (hs : 0 < s) :
    HasSum (fun j : ℕ => (B : ℝ) • Muon.mean P (fun ω =>
        delAlpha1 w F S t j s ω • (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 w F S t j s ω • (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))))
      (Hmix w F S t s) := by
  exact pdx_main hw F S t s hs

/-! ### Private helpers for `thm_app_drift_mixed_ii` (task P-C.7.P2) -/

section TlHelpers
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
open scoped MatrixOrder

private lemma tlb_opNorm_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ opNorm A := by
  unfold opNorm; exact norm_nonneg _

private lemma tlb_fro_nonneg {k l : ℕ} (A : Mat k l) : 0 ≤ fro A := Real.sqrt_nonneg _

private lemma tlb_fro_sq {k l : ℕ} (A : Mat k l) : fro A ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
  unfold fro
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

open scoped Matrix.Norms.L2Operator in
private lemma tlb_fro_mul_le_left {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
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
    rw [tlb_fro_sq, mul_pow, tlb_fro_sq, Finset.sum_comm]
    calc ∑ j, ∑ i, (M * N) i j ^ 2 ≤ ∑ j : Fin r, opNorm M ^ 2 * ∑ k, N k j ^ 2 :=
          Finset.sum_le_sum fun j _ => hcol j
      _ = opNorm M ^ 2 * ∑ k, ∑ j, N k j ^ 2 := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
  exact (pow_le_pow_iff_left₀ (tlb_fro_nonneg _) (mul_nonneg (tlb_opNorm_nonneg M)
    (tlb_fro_nonneg N)) two_ne_zero).mp hfro

open scoped Matrix.Norms.L2Operator in
private lemma tlb_opNorm_transpose {k l : ℕ} (A : Mat k l) : opNorm Aᵀ = opNorm A := by
  rw [opNorm_eq_norm, opNorm_eq_norm, ← Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.l2_opNorm_conjTranspose]

private lemma tlb_fro_transpose {k l : ℕ} (A : Mat k l) : fro Aᵀ = fro A := by
  unfold fro
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private lemma tlb_fro_mul_le_right {p q r : ℕ} (M : Mat p q) (N : Mat q r) :
    fro (M * N) ≤ fro M * opNorm N := by
  have h := tlb_fro_mul_le_left Nᵀ Mᵀ
  rw [← Matrix.transpose_mul, tlb_fro_transpose, tlb_opNorm_transpose, tlb_fro_transpose] at h
  linarith [mul_comm (opNorm N) (fro M)]

open scoped Matrix.Norms.L2Operator in
private lemma tlb_opNorm_mul_le {a b c : ℕ} (A : Mat a b) (B : Mat b c) :
    opNorm (A * B) ≤ opNorm A * opNorm B := by
  rw [opNorm_eq_norm, opNorm_eq_norm, opNorm_eq_norm]
  exact Matrix.l2_opNorm_mul A B

open scoped Matrix.Norms.L2Operator in
/-- `‖r_out‖² = ‖Σ_out‖` for the regularized square root `r_out`. -/
private lemma tlb_opNorm_rOut_mul_self {m n : ℕ} (C : Covariances m n) :
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
/-- The `r_in` analogue of `tlb_opNorm_rOut_mul_self`. -/
private lemma tlb_opNorm_rIn_mul_self {m n : ℕ} (C : Covariances m n) :
    opNorm (rIn C) * opNorm (rIn C) = opNorm C.Sin := by
  have hh : (rIn C)ᴴ = rIn C :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  have hsq : rIn C * rIn C = C.Sin :=
    CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)
  have := Matrix.l2_opNorm_conjTranspose_mul_self (rIn C)
  rw [hh, hsq] at this
  rw [opNorm_eq_norm, opNorm_eq_norm]
  exact this.symm

private lemma tlb_fro_one {m : ℕ} : fro (1 : Mat m m) = Real.sqrt m := by
  unfold fro
  simp [Matrix.one_apply]

/-- `‖S‖_F ≤ √m ‖S‖` for `S` square of size `m` (the factor `√m` of the Id term). -/
private lemma tlb_fro_le_sqrt_mul_opNorm {m : ℕ} (S : Mat m m) :
    fro S ≤ Real.sqrt m * opNorm S := by
  have h := tlb_fro_mul_le_left S (1 : Mat m m)
  rw [Matrix.mul_one, tlb_fro_one] at h
  linarith [mul_comm (opNorm S) (Real.sqrt m)]

/-- Conditional Jensen for the square: `(E_𝒢 e)² ≤ E_𝒢 e²` a.e. -/
private lemma tlb_jensen_sq (P : Measure Ω) [IsProbabilityMeasure P]
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

private lemma tlb_gmono {n k : ℕ} (c : Fin k → Fin n) :
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

private lemma tlb_gtwo {n : ℕ} (p q : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q) (stdGaussianPi n) := by
  have h := tlb_gmono (n := n) ![p, q]
  simpa [Fin.prod_univ_two] using h

private lemma tlb_gfour {n : ℕ} (p q r s : Fin n) :
    Integrable (fun z : Fin n → ℝ => z p * z q * z r * z s) (stdGaussianPi n) := by
  have h := tlb_gmono (n := n) ![p, q, r, s]
  simpa [Fin.prod_univ_four] using h

private lemma tlb_gfam1_memLp (m n : ℕ) (a : Fin m × Fin n) :
    MemLp (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) 2 (gaussPair m n) := by
  have hm : Measurable (fun x : Vec m × Vec n => x.1 a.1 * x.2 a.2) := by fun_prop
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  have h := Integrable.mul_prod (tlb_gtwo a.1 a.1) (tlb_gtwo a.2 a.2)
  unfold gaussPair
  convert h using 2 with x
  ring

private lemma tlb_gsq_memLp (d : ℕ) (a : Fin d × Fin d) :
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
  exact ((tlb_gfour _ _ _ _).sub ((tlb_gtwo _ _).const_mul _)).add (integrable_const _)

private lemma tlb_aem {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n : ℕ}
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

private lemma tlb_sq_memLp {Ω : Type*} {mΩ : MeasurableSpace Ω} {m n d : ℕ}
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n)
    (π : Vec m × Vec n → Vec d) (hπ : Measurable π)
    (hmap : (gaussPair m n).map π = stdGaussianPi d) (a : Fin d × Fin d) :
    MemLp (fun w => (π (X w)) a.1 * (π (X w)) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 P := by
  have h1 : MemLp (fun z : Vec d => z a.1 * z a.2 - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2
      (Measure.map π (gaussPair m n)) := by rw [hmap]; exact tlb_gsq_memLp d a
  have h2 := h1.comp_of_map hπ.aemeasurable
  have hg : MemLp (fun x : Vec m × Vec n => (π x) a.1 * (π x) a.2
      - (1 : Matrix (Fin d) (Fin d) ℝ) a.1 a.2) 2 (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact h2
  exact hg.comp_of_map (tlb_aem P X hX)

end BfCopies

/-- Conditional expectation of a finite weighted sum of integrable functions. -/
private lemma tlb_condExp_sum {ι : Type*} [Fintype ι] (P : Measure Ω) (G : MeasurableSpace Ω)
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

private lemma tlb_memLp_sq_fst {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin m) :
    MemLp (fun ω => (X ω).1 a * (X ω).1 b - (1 : Mat m m) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.fst = Muon.Foundations.stdGaussianPi m := by
    unfold gaussPair
    rw [Measure.map_fst_prod]; simp
  exact tlb_sq_memLp P X hX Prod.fst measurable_fst hmap (a, b)

private lemma tlb_memLp_sq_snd {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a b : Fin n) :
    MemLp (fun ω => (X ω).2 a * (X ω).2 b - (1 : Mat n n) a b) 2 P := by
  have hmap : (gaussPair m n).map Prod.snd = Muon.Foundations.stdGaussianPi n := by
    unfold gaussPair
    rw [Measure.map_snd_prod]; simp
  exact tlb_sq_memLp P X hX Prod.snd measurable_snd hmap (a, b)

private lemma tlb_memLp_cross {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (a : Fin m) (b : Fin n) :
    MemLp (fun ω => (X ω).1 a * (X ω).2 b) 2 P := by
  have hg : MemLp (fun x : Vec m × Vec n => x.1 a * x.2 b) 2
      (@Measure.map Ω (Vec m × Vec n) mΩ _ X P) := by
    rw [hX]; exact tlb_gfam1_memLp m n (a, b)
  exact hg.comp_of_map (tlb_aem P X hX)

private lemma tlb_integrable_mul {f g : Ω → ℝ} {P : Measure Ω} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg

open scoped Matrix.Norms.Frobenius in
private lemma tlb_fro_add {k l : ℕ} (A B' : Mat k l) : fro (A + B') ≤ fro A + fro B' := by
  rw [fro_eq_norm, fro_eq_norm, fro_eq_norm]; exact norm_add_le _ _

open scoped Matrix.Norms.Frobenius in
private lemma tlb_fro_smul {k l : ℕ} (c : ℝ) (A : Mat k l) : fro (c • A) = |c| * fro A := by
  rw [fro_eq_norm, fro_eq_norm, norm_smul, Real.norm_eq_abs]

private lemma tlc_Rs_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
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

private lemma tlc_Rts_continuous {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun M : Mat m n => Rts M s) := by
  have e : (fun M : Mat m n => Rts M s) = fun M => Rs Mᵀ s := by
    funext M; simp [Rts, Rs]
  rw [e]
  exact (tlc_Rs_continuous s hs).comp continuous_id.matrix_transpose

private lemma tlc_alpha_cont {m n : ℕ} (s : ℝ) (hs : 0 < s) :
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha1 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha2 q.1 q.2.1 q.2.2.1 q.2.2.2 s) ∧
    Continuous (fun q : Mat m n × ℝ × Vec m × Vec n =>
      Muon.DetEquiv.alpha3 q.1 q.2.1 q.2.2.1 q.2.2.2 s) := by
  have hR := tlc_Rs_continuous (m := m) (n := n) s hs
  have hRt := tlc_Rts_continuous (m := m) (n := n) s hs
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
/-- Matrix product entry as a sum over the index pairs of the middle factor. -/
private lemma tlc_mul3_apply {p q r t : ℕ} (A : Mat p q) (B : Mat q r) (C : Mat r t) (i : Fin p)
    (j : Fin t) :
    (A * B * C) i j = ∑ x : Fin q × Fin r, (A i x.1 * C x.2 j) * B x.1 x.2 := by
  simp only [Matrix.mul_apply, Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

/-- Entrywise pull-out of bounded `𝒢`-measurable matrix factors from `condExpMat`. -/
private lemma tlc_condExpMat_pull {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
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
      funext fun ω => tlc_mul3_apply _ _ _ _ _
    rw [Muon.Foundations.condExpMat_apply, e2, h1ζ, Finset.sum_apply, tlc_mul3_apply]
    exact Finset.sum_congr rfl fun x _ => h2ζ x
  filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun j => hentry i j] with ζ hζ
  ext i j
  exact hζ i j

/-- Operator-norm bound on matrix entries (copy of the trace-file helper). -/
private lemma tlc_abs_entry_le {p q : ℕ} (K : Mat p q) (i : Fin p) (j : Fin q) :
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
private lemma tlc_int_outer {d d' : ℕ} (P : Measure Ω) (x : Ω → Vec d) (y : Ω → Vec d')
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
private lemma tlc_int_LFR {p q r t : ℕ} (P : Measure Ω) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (L : Ω → Mat p q) (R : Ω → Mat r t) (cL cR : ℝ) (hcL : 0 ≤ cL)
    (hL : ∀ i j, Measurable[G] (fun ω => L ω i j))
    (hR : ∀ i j, Measurable[G] (fun ω => R ω i j))
    (hLb : ∀ ω i j, |L ω i j| ≤ cL) (hRb : ∀ ω i j, |R ω i j| ≤ cR)
    (F : Ω → Mat q r) (hF : ∀ k l, Integrable (fun ω => F ω k l) P) (i : Fin p) (j : Fin t) :
    Integrable (fun ω => (L ω * F ω * R ω) i j) P := by
  have e : (fun ω => (L ω * F ω * R ω) i j) =
      fun ω => ∑ x : Fin q × Fin r, (L ω i x.1 * R ω x.2 j) * F ω x.1 x.2 :=
    funext fun ω => tlc_mul3_apply _ _ _ _ _
  rw [e]
  refine integrable_finset_sum _ fun x _ => ?_
  refine Integrable.bdd_mul (c := cL * cR) (hF x.1 x.2)
    (((hL i x.1).mul (hR x.2 j)).mono hG le_rfl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (hLb ω i x.1) (hRb ω x.2 j) (abs_nonneg _) hcL

/-- Entrywise additivity of `condExpMat`. -/
private lemma tlc_condExpMat_add {p q : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
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
private lemma tlc_fro_sandwich {p q r t : ℕ} (L : Mat p q) (K : Mat q r) (R : Mat r t) :
    fro (L * K * R) ≤ opNorm L * fro K * opNorm R :=
  (tlb_fro_mul_le_right _ _).trans
    (mul_le_mul_of_nonneg_right (tlb_fro_mul_le_left _ _) (tlb_opNorm_nonneg _))

/-- Frobenius bound for a pulled-out sandwich `L (condExp F) R` under a Bessel bound on `F`. -/
private lemma tlc_term {p q r t : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
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
  filter_upwards [tlc_condExpMat_pull (mΩ := mΩ) P G hG L R cL cR hcL hcR hL hR hLb hRb F hF, hK]
    with ζ h1 h2
  rw [h1]
  refine (tlc_fro_sandwich _ _ _).trans ?_
  exact mul_le_mul (mul_le_mul (haL ζ) h2 (tlb_fro_nonneg _) haL0) (haR ζ) (tlb_opNorm_nonneg _)
    (mul_nonneg haL0 hK0)

/-- Conditional second moment of `e` from a pointwise bound `|e| ≤ D |a|`. -/
private lemma tlc_cond_sq (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
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



/-- `L²` membership from a pointwise domination by an `L²` function. -/
private lemma tlc_memLp2 (P : Measure Ω) (e a : Ω → ℝ) (D : ℝ) (he : Measurable[mΩ] e)
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

end TlHelpers

section TlGen
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_fro_eq {m n : ℕ} (a : Mat m n) :
    fro a = Real.sqrt (∑ x : Fin m × Fin n, a x.1 x.2 ^ 2) := by
  unfold fro
  simp [Fintype.sum_prod_type, Real.norm_eq_abs, sq_abs]

private lemma tl_inner_le {m n : ℕ} (a b : Mat m n) :
    ∑ i, ∑ k, a i k * b i k ≤ fro a * fro b := by
  rw [tl_fro_eq, tl_fro_eq]
  have := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin m × Fin n))
    (fun x => a x.1 x.2) (fun x => b x.1 x.2)
  simpa [Fintype.sum_prod_type] using this

lemma tl_mean_fro_le (P : Measure Ω) [IsProbabilityMeasure P] {m n : ℕ}
    (F : Ω → Mat m n) (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (c : ℝ)
    (hc : ∀ᵐ ω ∂P, fro (F ω) ≤ c) : fro (Muon.mean P F) ≤ c := by
  set E := Muon.mean P F with hE
  have hc0 : 0 ≤ c := by
    obtain ⟨ω, h⟩ := hc.exists
    exact (tlb_fro_nonneg _).trans h
  have hint : ∀ i k, Integrable (fun ω => E i k * F ω i k) P := fun i k => (hF i k).const_mul _
  have h1 : fro E ^ 2 = ∫ ω, ∑ i, ∑ k, E i k * F ω i k ∂P := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun k _ => hint i k))]
    rw [tlb_fro_sq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun k _ => hint i k)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]
    simp only [hE, Muon.mean, Matrix.of_apply]
    ring
  have h2 : ∫ ω, ∑ i, ∑ k, E i k * F ω i k ∂P ≤ ∫ _ω, fro E * c ∂P := by
    refine integral_mono_ae (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
      hint i k) (integrable_const _) ?_
    filter_upwards [hc] with ω hω
    exact (tl_inner_le E (F ω)).trans (mul_le_mul_of_nonneg_left hω (tlb_fro_nonneg _))
  rw [integral_const, probReal_univ, one_smul] at h2
  have h3 : fro E ^ 2 ≤ fro E * c := h1 ▸ h2
  by_contra h
  push Not at h
  nlinarith [tlb_fro_nonneg E]

end TlGen

section TlGen2
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma tl_meas_del {m n B : ℕ} {P : Measure Ω} (w : ℕ → ℝ) (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    Measurable[sigmaOthers F S t j] (delBufAge w F S t j) := by
  haveI : TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Mat m n) :=
    inferInstanceAs (TopologicalSpace.IsCompletelyPseudoMetrizableSpace (Fin m → Fin n → ℝ))
  haveI : SecondCountableTopology (Mat m n) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin n → ℝ))
  haveI : MeasurableAdd₂ (Mat m n) := inferInstanceAs (MeasurableAdd₂ (Fin m → Fin n → ℝ))
  have hQ := pdx_hQ F
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

end TlGen2

section TlMean
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_mean_tower (P : Measure Ω) [IsProbabilityMeasure P] (G : MeasurableSpace Ω)
    (hG : G ≤ mΩ) {m n : ℕ} (F : Ω → Mat m n) :
    @Muon.mean Ω mΩ _ _ P F = @Muon.mean Ω mΩ _ _ P (Muon.Foundations.condExpMat G P F) := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Muon.Foundations.condExpMat_apply]
  exact (integral_condExp hG).symm

private lemma tl_mean_congr (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (h : ∀ᵐ ω ∂P, F ω = F' ω) : Muon.mean P F = Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply]
  exact integral_congr_ae (h.mono fun ω hω => by simp only [hω])

private lemma tl_mean_smul (P : Measure Ω) {m n : ℕ} (c : ℝ) (F : Ω → Mat m n) :
    Muon.mean P (fun ω => c • F ω) = c • Muon.mean P F := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
  exact integral_const_mul _ _

private lemma tl_mean_add (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    Muon.mean P (fun ω => F ω + F' ω) = Muon.mean P F + Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.add_apply]
  exact integral_add (hF i k) (hF' i k)

private lemma tl_mean_sub (P : Measure Ω) {m n : ℕ} (F F' : Ω → Mat m n)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) (hF' : ∀ i k, Integrable (fun ω => F' ω i k) P) :
    Muon.mean P (fun ω => F ω - F' ω) = Muon.mean P F - Muon.mean P F' := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.sub_apply]
  exact integral_sub (hF i k) (hF' i k)

private lemma tl_mean_mul_right (P : Measure Ω) {m n r : ℕ} (F : Ω → Mat m n) (A : Mat n r)
    (hF : ∀ i k, Integrable (fun ω => F ω i k) P) :
    Muon.mean P (fun ω => F ω * A) = Muon.mean P F * A := by
  ext i k
  simp only [Muon.mean, Matrix.of_apply, Matrix.mul_apply]
  rw [integral_finsetSum _ (fun l _ => (hF i l).mul_const _)]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact integral_mul_const _ _

end TlMean

section TlFacts
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_indep {m n B : ℕ} {P : Measure Ω} (F : FrozenParams m n B)
    (S : FrozenSamples P m n B) (t : ℤ) (j : ℕ) :
    sigmaOthers F S t j ≤ mΩ ∧
    Indep (MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance)
      (sigmaOthers F S t j) P := by
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  have hG : sigmaOthers F S t j ≤ mΩ := iSup₂_le fun q _ => (S.meas q.1 q.2).comap_le
  refine ⟨hG, ?_⟩
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
  exact hind.symm

end TlFacts

section TlFacts2
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_sqrt_le (P : Measure Ω) (G : MeasurableSpace Ω) (e : Ω → ℝ) (y : ℝ)
    (hc : ∀ᵐ ζ ∂P, condExp G P (fun ω => |e ω| ^ 2) ζ ≤ y ^ 2) :
    ∀ᵐ ζ ∂P, Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ) ≤ |y| := by
  filter_upwards [hc] with ζ h
  have e1 : (fun ω => |e ω| ^ 2) = fun ω => e ω ^ 2 := by funext ω; exact sq_abs _
  rw [e1] at h
  calc _ ≤ Real.sqrt (y ^ 2) := Real.sqrt_le_sqrt h
    _ = _ := Real.sqrt_sq_eq_abs _

theorem tl_facts (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Cc : ℝ, 0 ≤ Cc ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, 1 ≤ s →
        (∀ ω, 0 ≤ delAlpha2 w F S t j s ω) ∧
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlpha1 w F S t j s) ∧
        Measurable[MeasurableSpace.comap (S.zw (t + 1 - (j : ℤ)) (slotOne F.hB)) inferInstance ⊔
          sigmaOthers F S t j] (delAlpha2 w F S t j s) ∧
        MemLp (delAlpha1 w F S t j s) 2 P ∧ MemLp (delAlpha2 w F S t j s) 2 P ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => delAlpha1 w F S t j s ω ^ 2) ζ) ≤ Cc * w j) ∧
        (∀ᵐ ζ ∂P, Real.sqrt (condExp (sigmaOthers F S t j) P
          (fun ω => delAlpha2 w F S t j s ω ^ 2) ζ) ≤ Cc * w j ^ 2 / s) ∧
        Integrable (delAlpha2 w F S t j s) P ∧
        (∀ᵐ ζ ∂P, condExp (sigmaOthers F S t j) P (delAlpha2 w F S t j s) ζ ≤ Cc * w j ^ 2 / s) := by
  obtain ⟨C1, hC1⟩ := lem_app_drift_coeffmoments 1 le_rfl 1 one_pos CS γ hγ
  obtain ⟨C2, hC2⟩ := lem_app_drift_coeffmoments 2 (by norm_num) 1 one_pos CS γ hγ
  refine ⟨|C1| + |C2|, by positivity, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hM0 := tl_meas_del w F S t j
  obtain ⟨-, -, -, ⟨i2a, c2a⟩⟩ :=
    hC1 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1 hM0 s hs
  obtain ⟨hnn, ⟨i1, c1⟩, -, ⟨i2, c2⟩⟩ :=
    hC2 Ω m n B P F S t j (delBufAge w F S t j) (w j) hCo hCi hm hn hw0 hw1 hM0 s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hX : Measurable X := S.meas _ _
  obtain ⟨hG, -⟩ := tl_indep F S t j
  have hGc : MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j ≤ inst :=
    sup_le hX.comap_le hG
  have hXc : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j] X :=
    (comap_measurable X).mono le_sup_left le_rfl
  have hM0c : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delBufAge w F S t j) := hM0.mono le_sup_right le_rfl
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
      (fun ω => w j * resid F.A (X ω)) := (hdm.comp hXc).const_mul (w j)
  have hq : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (fun ω => (delBufAge w F S t j ω, w j * resid F.A (X ω), momU F.C B (X ω),
        momV F.C B (X ω))) :=
    hM0c.prodMk (hDm.prodMk (hUm.prodMk hVm))
  obtain ⟨c1', c2', -⟩ := tlc_alpha_cont (m := m) (n := n) s hspos
  have hA1 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlpha1 w F S t j s) := c1'.measurable.comp hq
  have hA2 : Measurable[MeasurableSpace.comap X inferInstance ⊔ sigmaOthers F S t j]
      (delAlpha2 w F S t j s) := c2'.measurable.comp hq
  have hn2 : ∀ ω, 0 ≤ delAlpha2 w F S t j s ω := hnn
  have L1 : MemLp (delAlpha1 w F S t j s) 2 P :=
    tlc_memLp2 P _ (delAlpha1 w F S t j s) 1 (hA1.mono hGc le_rfl) (fun ω => by rw [one_mul]) i1
  have L2 : MemLp (delAlpha2 w F S t j s) 2 P :=
    tlc_memLp2 P _ (delAlpha2 w F S t j s) 1 (hA2.mono hGc le_rfl) (fun ω => by rw [one_mul]) i2
  have hCc0 : 0 ≤ |C1| + |C2| := by positivity
  refine ⟨hn2, hA1, hA2, L1, L2, ?_, ?_, ?_, ?_⟩
  · filter_upwards [tl_sqrt_le P (sigmaOthers F S t j) (delAlpha1 w F S t j s) (C2 * w j) c1]
      with ζ h
    refine h.trans ?_
    rw [abs_mul, abs_of_nonneg hw0]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) hw0
  · filter_upwards [tl_sqrt_le P (sigmaOthers F S t j) (delAlpha2 w F S t j s) (C2 * w j ^ 2 / s) c2]
      with ζ h
    refine h.trans ?_
    have hw2 : 0 ≤ w j ^ 2 := sq_nonneg _
    rw [abs_div, abs_mul, abs_of_nonneg hw2, abs_of_pos hspos, mul_div_assoc]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg C1]) (by positivity)
  · exact L2.integrable one_le_two
  · have e2 : (fun ω => |delAlpha2 w F S t j s ω| ^ 1) = delAlpha2 w F S t j s := by
      funext ω; rw [pow_one, abs_of_nonneg (hn2 ω)]
    have c2b : ∀ᵐ ζ ∂P, condExp (sigmaOthers F S t j) P
        (fun ω => |delAlpha2 w F S t j s ω| ^ 1) ζ ≤ (C1 * w j ^ 2 / s) ^ 1 := c2a
    rw [e2] at c2b
    filter_upwards [c2b] with ζ h
    refine h.trans ?_
    rw [pow_one, mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self C1, abs_nonneg C2]) (by positivity)

end TlFacts2

section TlS
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

private lemma tl_entm {m n a b : ℕ} (G : MeasurableSpace Ω) (M0 : Ω → Mat m n)
    (hM0 : Measurable[G] M0) (Φ : Mat m n → Mat a b) (hΦ : Continuous Φ) (i : Fin a) (k : Fin b) :
    Measurable[G] (fun ω => Φ (M0 ω) i k) :=
  (((measurable_pi_apply k).comp (measurable_pi_apply i) :
    Measurable (fun f : Mat a b => f i k))).comp (hΦ.measurable.comp hM0)

private lemma tl_opNorm_one_le {n : ℕ} : opNorm (1 : Mat n n) ≤ 1 := by
  unfold opNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => ?_)
  simp [Matrix.toEuclideanLin]


private lemma tl_ent_eq {d d' : ℕ} (e : Ω → ℝ) (u : Ω → Vec d) (v : Ω → Vec d') (k : Fin d)
    (l : Fin d') :
    (fun ω => (e ω • Muon.outer (u ω) (v ω)) k l) = fun ω => e ω * (u ω k * v ω l) := by
  funext ω; simp [Muon.outer, Matrix.vecMulVec_apply]

private lemma tl_int_uv {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k : Fin m) (l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (momU C B (X ω)) (momV C B (X ω))) k l) P := by
  rw [tl_ent_eq]
  exact tlc_int_outer (mΩ := mΩ) P (fun ω => (X ω).1) (fun ω => (X ω).2) (rOut C) (rIn C) _ _
    (fun ω => momU C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (fun p q => tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_cross (mΩ := mΩ) P X hX p q) he) k l

private lemma tl_int_ww {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (X ω).2 (X ω).2) k l) P := by
  rw [tl_ent_eq]
  have h := (tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX k l) he).add
    ((he.integrable one_le_two).const_mul ((1 : Mat n n) k l))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

private lemma tl_int_uu {m n B : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (C : Covariances m n)
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (e : Ω → ℝ) (he : MemLp e 2 P)
    (k l : Fin n) :
    Integrable (fun ω => (e ω • Muon.outer (momV C B (X ω)) (momV C B (X ω))) k l) P := by
  rw [tl_ent_eq]
  refine tlc_int_outer (mΩ := mΩ) P (fun ω => (X ω).2) (fun ω => (X ω).2) (rIn C) (rIn C) _ _
    (fun ω => momV C B (X ω)) (fun ω => momV C B (X ω)) e (fun ω => rfl) (fun ω => rfl)
    (fun p q => ?_) k l
  have h := (tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX p q) he).add
    ((he.integrable one_le_two).const_mul ((1 : Mat n n) p q))
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply]
  ring

end TlS

section TlS2
open ProbabilityTheory

theorem tl_S (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, 1 ≤ s →
        (∀ i k, Integrable (fun ω => (delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) i k) P) ∧
        fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
            (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω)))) ≤
          K * w j / s := by
  obtain ⟨Cc, hCc0, hCc⟩ := tl_facts CS γ hγ
  refine ⟨CS * Cc, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  obtain ⟨-, e1m, -, L1, -, k1, -, -, -⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  have hR0m : ∀ i k, Measurable[sigmaOthers F S t j]
      (fun ω => Rs (delBufAge w F S t j ω) s i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Rs M s) (tlc_Rs_continuous s hspos) i k
  have hRb : ∀ ω, opNorm (Rs (delBufAge w F S t j ω) s) ≤ 1 / s :=
    fun ω => (lem_app_de_resolvent _ s hspos).1
  have hF' := tl_int_uv (B := B) P F.C X hlaw _ L1
  have hmeas1 : ∀ i k, Measurable[sigmaOthers F S t j] (fun ω => (1 : Mat n n) i k) :=
    fun i k => measurable_const
  have hb1 : ∀ (ω : Ω) i k, |(1 : Mat n n) i k| ≤ 1 := fun ω i k =>
    (tlc_abs_entry_le _ i k).trans tl_opNorm_one_le
  have hLb : ∀ ω i k, |Rs (delBufAge w F S t j ω) s i k| ≤ 1 / s :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hRb ω)
  have hrew' : ∀ ω, delAlpha1 w F S t j s ω •
      (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω)) =
      Rs (delBufAge w F S t j ω) s * (delAlpha1 w F S t j s ω •
        Muon.outer (momU F.C B (X ω)) (momV F.C B (X ω))) * (1 : Mat n n) := by
    intro ω
    rw [Matrix.mul_one, Matrix.mul_smul]
    rfl
  have hrew := funext hrew'
  have hint := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Rs (delBufAge w F S t j ω) s) (fun _ => (1 : Mat n n)) (1 / s) 1 (by positivity)
    hR0m hmeas1 hLb hb1 _ hF'
  refine ⟨fun i k => ?_, ?_⟩
  · exact (hint i k).congr (Filter.Eventually.of_forall fun ω => by dsimp only; rw [hrew' ω])
  · rw [hrew]
    have hK := bessel_frob_uv (mΩ := inst) P F.C CS hB hCo hCi X hlaw (sigmaOthers F S t j) hG
      hindc _ e1m L1
    have hT := tlc_term (mΩ := inst) P (sigmaOthers F S t j) hG
      (fun ω => Rs (delBufAge w F S t j ω) s) (fun _ => (1 : Mat n n)) (1 / s) 1 (by positivity)
      zero_le_one hR0m hmeas1 hLb hb1 _ hF' (1 / s) 1 (CS / B * (Cc * w j)) (by positivity)
      zero_le_one (by positivity) hRb (fun _ => tl_opNorm_one_le)
      (by
        filter_upwards [hK.mono fun ζ h => h.1, k1] with ζ h1 h2
        exact h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity)))
    rw [tl_mean_tower P (sigmaOthers F S t j) hG, tlb_fro_smul, abs_of_pos hBr]
    have hc := tl_mean_fro_le P _ (fun i k => by
      simpa only [Muon.Foundations.condExpMat_apply] using integrable_condExp) _ hT
    calc (B : ℝ) * _ ≤ (B : ℝ) * (1 / s * (CS / B * (Cc * w j)) * 1) :=
          mul_le_mul_of_nonneg_left hc hBr.le
      _ = _ := by field_simp

end TlS2

section TlQ0
open ProbabilityTheory
open scoped MatrixOrder

private lemma tl_rIn_symm {m n : ℕ} (C : Covariances m n) : (rIn C)ᵀ = rIn C := by
  have h : (CFC.sqrt C.Sin)ᴴ = CFC.sqrt C.Sin :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg C.Sin)).isHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h

private lemma tl_rIn_sq {m n : ℕ} (C : Covariances m n) : rIn C * rIn C = C.Sin :=
  CFC.sqrt_mul_sqrt_self C.Sin (Matrix.nonneg_iff_posSemidef.mpr C.psdIn)

private lemma tl_B_outer_vv {m n : ℕ} (C : Covariances m n) (B : ℕ) (hB : 0 < B)
    (x : Vec m × Vec n) :
    (B : ℝ) • Muon.outer (momV C B x) (momV C B x) = rIn C * Muon.outer x.2 x.2 * rIn C := by
  have hv : Matrix.vecMul x.2 (rIn C) = Matrix.mulVec (rIn C) x.2 := by
    rw [← Matrix.vecMul_transpose, tl_rIn_symm]
  have h1 : rIn C * Muon.outer x.2 x.2 * rIn C =
      Muon.outer (Matrix.mulVec (rIn C) x.2) (Matrix.mulVec (rIn C) x.2) := by
    rw [Muon.outer, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hv]
  rw [h1]
  unfold momV
  ext i k
  simp only [Matrix.smul_apply, smul_eq_mul, Muon.outer, Matrix.vecMulVec_apply, Pi.smul_apply]
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have haa : (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hBr.le]; exact mul_inv_cancel₀ hBr.ne'
  calc (B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) i * ((Real.sqrt (B : ℝ))⁻¹ * (rIn C *ᵥ x.2) k))
      = ((B : ℝ) * ((Real.sqrt (B : ℝ))⁻¹ * (Real.sqrt (B : ℝ))⁻¹)) *
        ((rIn C *ᵥ x.2) i * (rIn C *ᵥ x.2) k) := by ring
    _ = _ := by rw [haa, one_mul]

end TlQ0

section TlGram
open ProbabilityTheory
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

lemma tl_gram_cond {m n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Vec m × Vec n) (hX : P.map X = gaussPair m n) (G : MeasurableSpace Ω) (hG : G ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap X inferInstance) G P) (e : Ω → ℝ)
    (he : Measurable[MeasurableSpace.comap X inferInstance ⊔ G] e) (he2 : MemLp e 2 P) :
    (∀ᵐ ζ ∂P, Muon.Foundations.condExpMat G P
        (fun ω => e ω • Muon.outer (X ω).2 (X ω).2) ζ =
      condExp G P e ζ • (1 : Mat n n) +
        Muon.Foundations.condExpMat G P (fun ω => e ω • (Muon.outer (X ω).2 (X ω).2 - 1)) ζ) ∧
    (∀ᵐ ζ ∂P, fro (Muon.Foundations.condExpMat G P
        (fun ω => e ω • (Muon.outer (X ω).2 (X ω).2 - 1)) ζ) ≤
      Real.sqrt 2 * Real.sqrt (condExp G P (fun ω => e ω ^ 2) ζ)) := by
  have hei : Integrable e P := he2.integrable one_le_two
  have hi1 : ∀ i k : Fin n, Integrable (fun ω => ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) * e ω) P :=
    fun i k => tlb_integrable_mul (mΩ := mΩ) (tlb_memLp_sq_snd (mΩ := mΩ) P X hX i k) he2
  have hent : ∀ i k : Fin n, (fun ω => (e ω • (Muon.outer (X ω).2 (X ω).2 - 1)) i k) =
      fun ω => ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) * e ω := by
    intro i k; funext ω
    simp [Muon.outer, Matrix.vecMulVec_apply]; ring
  have hent2 : ∀ i k : Fin n, (fun ω => (e ω • Muon.outer (X ω).2 (X ω).2) i k) =
      fun ω => ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) * e ω + (1 : Mat n n) i k * e ω := by
    intro i k; funext ω
    simp [Muon.outer, Matrix.vecMulVec_apply]; ring
  constructor
  · have hall : ∀ i k : Fin n, ∀ᵐ ζ ∂P,
        Muon.Foundations.condExpMat G P (fun ω => e ω • Muon.outer (X ω).2 (X ω).2) ζ i k =
        ((condExp G P e ζ • (1 : Mat n n) +
        Muon.Foundations.condExpMat G P (fun ω => e ω • (Muon.outer (X ω).2 (X ω).2 - 1)) ζ :
          Mat n n)) i k := by
      intro i k
      have h1 : condExp G P (fun ω => ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) * e ω +
          (1 : Mat n n) i k * e ω) =ᵐ[P]
          (condExp G P (fun ω => ((X ω).2 i * (X ω).2 k - (1 : Mat n n) i k) * e ω) +
            condExp G P (fun ω => (1 : Mat n n) i k * e ω)) :=
        condExp_add (hi1 i k) (hei.const_mul ((1 : Mat n n) i k)) G
      have h2 := condExp_smul (μ := P) ((1 : Mat n n) i k) e G
      filter_upwards [h1, h2] with ζ h1ζ h2ζ
      rw [Matrix.add_apply, Matrix.smul_apply, Muon.Foundations.condExpMat_apply,
        Muon.Foundations.condExpMat_apply, hent2 i k, hent i k]
      have h2' : condExp G P (fun ω => (1 : Mat n n) i k * e ω) ζ =
          (1 : Mat n n) i k * condExp G P e ζ := h2ζ
      have h1ζ' := h1ζ
      simp only [Pi.add_apply] at h1ζ'
      rw [h1ζ', h2']
      simp only [smul_eq_mul]
      ring
    filter_upwards [ae_all_iff.2 fun i => ae_all_iff.2 fun k => hall i k] with ζ hζ
    ext i k
    exact hζ i k
  · have hb := lem_app_de_bessel_iii (𝕜 := ℝ) (mΩ := mΩ) P X hX G hG hind e he he2
    filter_upwards [hb] with ζ hζ
    unfold fro
    simp only [Muon.Foundations.condExpMat_apply, hent] at *
    simpa [Real.norm_eq_abs, sq_abs] using hζ

end TlGram

section TlQ
open ProbabilityTheory

theorem tl_Q (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, 1 ≤ s →
        (∀ i k, Integrable (fun ω => (delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) i k) P) ∧
        ∃ Err : Mat m n, fro Err ≤ K * w j ^ 2 / s ∧
          (B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
            (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) =
          (bj w F S t j s • Hj w F S t j s + Cj w F S t j s) * F.C.Sin + Err := by
  obtain ⟨Cc, hCc0, hCc⟩ := tl_facts CS γ hγ
  refine ⟨CS * Cc, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hB : 0 < B := F.hB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  obtain ⟨he2nn, -, e2m, -, L2, -, k2, -, -⟩ :=
    hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  set X : Ω → Vec m × Vec n := S.zw (t + 1 - (j : ℤ)) (slotOne F.hB) with hXdef
  have hlaw : P.map X = gaussPair m n := S.law _ _
  obtain ⟨hG, hindc⟩ := tl_indep F S t j
  have hM0 := tl_meas_del w F S t j
  set e2 := delAlpha2 w F S t j s with he2def
  set r := opNorm (rIn F.C) with hrdef
  have hr0 : 0 ≤ r := tlb_opNorm_nonneg _
  have hrr : r * r ≤ CS := (tlb_opNorm_rIn_mul_self F.C).le.trans hCi
  have hs2 : 0 < 1 / (2 * Real.sqrt s) := by positivity
  -- the factors
  have hXs : Continuous (fun M : Mat m n => Xs M s) := by
    unfold Xs; exact (tlc_Rs_continuous s hspos).matrix_mul continuous_id
  have hLc : Continuous (fun M : Mat m n => Xs M s * rIn F.C) := hXs.matrix_mul continuous_const
  have hLm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Xs M s * rIn F.C) hLc i k
  have hXm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω => Xs (delBufAge w F S t j ω) s i k) :=
    fun i k => tl_entm (sigmaOthers F S t j) _ hM0 (fun M => Xs M s) hXs i k
  have hRm : ∀ i k, Measurable[(sigmaOthers F S t j)] (fun ω : Ω => rIn F.C i k) := fun i k => measurable_const
  have hXb : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s) ≤ 1 / (2 * Real.sqrt s) :=
    fun ω => (lem_app_de_resolvent _ s hspos).2.2.1
  have hLb' : ∀ ω, opNorm (Xs (delBufAge w F S t j ω) s * rIn F.C) ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω => (tlb_opNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hXb ω) hr0)
  have hLb : ∀ ω i k, |(Xs (delBufAge w F S t j ω) s * rIn F.C) i k| ≤ 1 / (2 * Real.sqrt s) * r :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hLb' ω)
  have hRb : ∀ (ω : Ω) i k, |rIn F.C i k| ≤ r := fun ω i k => tlc_abs_entry_le _ i k
  have hXbd : ∀ ω i k, |Xs (delBufAge w F S t j ω) s i k| ≤ 1 / (2 * Real.sqrt s) :=
    fun ω i k => (tlc_abs_entry_le _ i k).trans (hXb ω)
  have hW := tl_int_ww (n := n) (m := m) P X hlaw e2 L2
  have hint := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hLm hRm hLb hRb _ hW
  have hpt : ∀ ω, (B : ℝ) • (e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) =
      (Xs (delBufAge w F S t j ω) s * rIn F.C) * (e2 ω • Muon.outer (X ω).2 (X ω).2) * rIn F.C := by
    intro ω
    have h := tl_B_outer_vv F.C B hB (X ω)
    have h2 : (B : ℝ) • (e2 ω • (Xs (delBufAge w F S t j ω) s *
        outer (ageV F S t j ω) (ageV F S t j ω))) =
        Xs (delBufAge w F S t j ω) s * (e2 ω • ((B : ℝ) • Muon.outer (momV F.C B (X ω))
          (momV F.C B (X ω)))) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, smul_comm]; rfl
    rw [h2, h]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
  have hsum_int : ∀ i k, Integrable (fun ω => (e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) i k) P := by
    intro i k
    refine ((hint i k).const_mul ((B : ℝ)⁻¹)).congr (Filter.Eventually.of_forall fun ω => ?_)
    have := congrFun (congrFun (hpt ω) i) k
    simp only [Matrix.smul_apply, smul_eq_mul] at this ⊢
    rw [← this]
    field_simp
  refine ⟨hsum_int, ?_⟩
  have hmean : (B : ℝ) • Muon.mean P (fun ω => e2 ω • (Xs (delBufAge w F S t j ω) s *
      outer (ageV F S t j ω) (ageV F S t j ω))) =
      Muon.mean P (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) *
        (e2 ω • Muon.outer (X ω).2 (X ω).2) * rIn F.C) := by
    rw [← tl_mean_smul]
    exact congrArg _ (funext hpt)
  rw [hmean, tl_mean_tower P (sigmaOthers F S t j) hG]
  obtain ⟨hK, hΓb⟩ := tl_gram_cond P X hlaw (sigmaOthers F S t j) hG hindc e2 e2m L2
  set Γ : Ω → Mat n n := Muon.Foundations.condExpMat (sigmaOthers F S t j) P
    (fun ω => e2 ω • (Muon.outer (X ω).2 (X ω).2 - 1)) with hΓdef
  have hΓint : ∀ i k, Integrable (fun ζ => Γ ζ i k) P := fun i k => by
    simpa only [hΓdef, Muon.Foundations.condExpMat_apply] using integrable_condExp
  have hφ : Integrable (condExp (sigmaOthers F S t j) P e2) P := integrable_condExp
  have hpull := tlc_condExpMat_pull (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hr0 hLm hRm hLb hRb
    (fun ω => e2 ω • Muon.outer (X ω).2 (X ω).2) hW
  have halg : ∀ (X0 : Mat m n) (φ : ℝ) (Γ' : Mat n n),
      (X0 * rIn F.C) * (φ • (1 : Mat n n) + Γ') * rIn F.C =
        (φ • X0) * F.C.Sin + (X0 * rIn F.C) * Γ' * rIn F.C := by
    intro X0 φ Γ'
    rw [← tl_rIn_sq F.C]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  have hae : ∀ᵐ ζ ∂P, Muon.Foundations.condExpMat (sigmaOthers F S t j) P
      (fun ω => (Xs (delBufAge w F S t j ω) s * rIn F.C) * (e2 ω • Muon.outer (X ω).2 (X ω).2) *
        rIn F.C) ζ =
      (condExp (sigmaOthers F S t j) P e2 ζ • Xs (delBufAge w F S t j ζ) s) * F.C.Sin +
        (Xs (delBufAge w F S t j ζ) s * rIn F.C) * Γ ζ * rIn F.C := by
    filter_upwards [hpull, hK] with ζ h1 h2
    rw [h1, h2]
    exact halg _ _ _
  rw [tl_mean_congr P _ _ hae]
  -- integrability
  have hX0int : ∀ i k, Integrable (fun ζ => Xs (delBufAge w F S t j ζ) s i k) P := fun i k =>
    Integrable.of_bound (((hXm i k).mono hG le_rfl).aestronglyMeasurable) (1 / (2 * Real.sqrt s))
      (Filter.Eventually.of_forall fun ζ => by
        rw [Real.norm_eq_abs]; exact hXbd ζ i k)
  have hφX : ∀ i k, Integrable (fun ζ => (condExp (sigmaOthers F S t j) P e2 ζ •
      Xs (delBufAge w F S t j ζ) s) i k) P := by
    intro i k
    have := Integrable.bdd_mul (c := 1 / (2 * Real.sqrt s)) hφ
      (((hXm i k).mono hG le_rfl).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ζ => by rw [Real.norm_eq_abs]; exact hXbd ζ i k)
    refine this.congr (Filter.Eventually.of_forall fun ζ => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  have hφXS : ∀ i k, Integrable (fun ζ => ((condExp (sigmaOthers F S t j) P e2 ζ •
      Xs (delBufAge w F S t j ζ) s) * F.C.Sin) i k) P := by
    intro i k
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun l _ => (hφX i l).mul_const _
  have hLΓR := tlc_int_LFR (mΩ := inst) P (sigmaOthers F S t j) hG
    (fun ω => Xs (delBufAge w F S t j ω) s * rIn F.C) (fun _ => rIn F.C)
    (1 / (2 * Real.sqrt s) * r) r (by positivity) hLm hRm hLb hRb Γ hΓint
  rw [tl_mean_add P _ _ hφXS hLΓR, tl_mean_mul_right P _ F.C.Sin hφX]
  refine ⟨Muon.mean P (fun ζ => (Xs (delBufAge w F S t j ζ) s * rIn F.C) * Γ ζ * rIn F.C),
    ?_, ?_⟩
  · have hbd := tl_mean_fro_le P (fun ζ => (Xs (delBufAge w F S t j ζ) s * rIn F.C) * Γ ζ * rIn F.C)
      hLΓR (1 / (2 * Real.sqrt s) * r * (Real.sqrt 2 * (Cc * w j ^ 2 / s)) * r) (by
        filter_upwards [hΓb, k2] with ζ h1 h2
        refine (tlc_fro_sandwich _ _ _).trans ?_
        have h3 : fro (Γ ζ) ≤ Real.sqrt 2 * (Cc * w j ^ 2 / s) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _))
        exact mul_le_mul (mul_le_mul (hLb' ζ) h3 (tlb_fro_nonneg _) (by positivity)) le_rfl hr0
          (by positivity))
    refine hbd.trans ?_
    have hsq1 : 1 ≤ Real.sqrt s := by
      rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs
    have hsq2 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    have hq : 1 / (2 * Real.sqrt s) * Real.sqrt 2 ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      linarith
    have hcc : 0 ≤ Cc * w j ^ 2 / s := by positivity
    calc 1 / (2 * Real.sqrt s) * r * (Real.sqrt 2 * (Cc * w j ^ 2 / s)) * r
        = (r * r) * ((1 / (2 * Real.sqrt s) * Real.sqrt 2) * (Cc * w j ^ 2 / s)) := by ring
      _ ≤ CS * (1 * (Cc * w j ^ 2 / s)) :=
          mul_le_mul hrr (mul_le_mul_of_nonneg_right hq hcc) (by positivity) hCS
      _ = _ := by ring
  · have hC : Cj w F S t j s = Muon.mean P (fun ω =>
        (condExp (sigmaOthers F S t j) P e2 ω - bj w F S t j s) • Xs (delBufAge w F S t j ω) s) := rfl
    have hH : Hj w F S t j s = Muon.mean P (fun ω => Xs (delBufAge w F S t j ω) s) := rfl
    have hsub : Muon.mean P (fun ω =>
        (condExp (sigmaOthers F S t j) P e2 ω - bj w F S t j s) • Xs (delBufAge w F S t j ω) s) =
        Muon.mean P (fun ω => condExp (sigmaOthers F S t j) P e2 ω • Xs (delBufAge w F S t j ω) s) -
          bj w F S t j s • Muon.mean P (fun ω => Xs (delBufAge w F S t j ω) s) := by
      rw [← tl_mean_smul]
      rw [← tl_mean_sub P _ _ hφX (fun i k => by
        simp only [Matrix.smul_apply, smul_eq_mul]; exact (hX0int i k).const_mul _)]
      exact congrArg _ (funext fun ω => sub_smul _ _ _)
    rw [hC, hH, hsub]
    congr 2
    abel

end TlQ

section TlY
open ProbabilityTheory

lemma tl_fro_Y {m n : ℕ} (H : Mat m n) (S : Mat n n) (hS : S.PosSemidef) (b : ℝ)
    (hb : 0 ≤ b) : fro H ≤ fro (H + b • (H * S)) := by
  have hsym : Sᵀ = S := by
    have := hS.isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  have hrow : ∀ i : Fin m, ∑ k, H i k ^ 2 ≤ ∑ k, (H + b • (H * S)) i k ^ 2 := by
    intro i
    set h : Vec n := fun k => H i k with hh
    set g : Vec n := S.mulVec h with hg
    have hent : ∀ k, (H + b • (H * S)) i k = h k + b * g k := by
      intro k
      have : (H * S) i k = g k := by
        simp only [Matrix.mul_apply, hg, Matrix.mulVec, dotProduct, hh]
        refine Finset.sum_congr rfl fun l _ => ?_
        have := congrFun (congrFun hsym k) l
        simp only [Matrix.transpose_apply] at this
        rw [← this]; ring
      simp [this, hh]
    simp only [hent]
    have hpsd : 0 ≤ ∑ k, h k * g k := by
      have := hS.dotProduct_mulVec_nonneg h
      simpa [dotProduct, hg] using this
    have e : ∑ k, (h k + b * g k) ^ 2 = ∑ k, h k ^ 2 + 2 * b * ∑ k, h k * g k + b ^ 2 * ∑ k, g k ^ 2 := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => by ring
    rw [e]
    have : 0 ≤ 2 * b * ∑ k, h k * g k := by positivity
    have : 0 ≤ b ^ 2 * ∑ k, g k ^ 2 := by positivity
    simp only [hh]
    linarith
  have hsq : fro H ^ 2 ≤ fro (H + b • (H * S)) ^ 2 := by
    rw [tlb_fro_sq, tlb_fro_sq]
    exact Finset.sum_le_sum fun i _ => hrow i
  exact (pow_le_pow_iff_left₀ (tlb_fro_nonneg _) (tlb_fro_nonneg _) two_ne_zero).mp hsq

end TlY

section TlB
open ProbabilityTheory

theorem tl_b (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (j : ℕ) (w : ℕ → ℝ), 0 ≤ w j → w j ≤ 1 →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, 1 ≤ s → 0 ≤ bj w F S t j s ∧ bj w F S t j s ≤ K * w j ^ 2 / s := by
  obtain ⟨Cc, hCc0, hCc⟩ := tl_facts CS γ hγ
  refine ⟨Cc, ?_⟩
  intro Ω inst m n B P _ F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hn2, -, -, -, -, -, -, hi, hle⟩ := hCc Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hG, -⟩ := tl_indep F S t j
  have hb : bj w F S t j s = ∫ ω, delAlpha2 w F S t j s ω ∂P := by
    unfold bj phiJ
    exact integral_condExp hG
  refine ⟨?_, ?_⟩
  · rw [hb]; exact integral_nonneg hn2
  · unfold bj phiJ
    calc ∫ ω, condExp (sigmaOthers F S t j) P (delAlpha2 w F S t j s) ω ∂P
        ≤ ∫ _ω, Cc * w j ^ 2 / s ∂P :=
          integral_mono_ae integrable_condExp (integrable_const _) hle
      _ = _ := by rw [integral_const, probReal_univ, one_smul]

end TlB

section TlPerj
open ProbabilityTheory

private lemma tl_abs_mul {x K y : ℝ} (h : x ≤ K * y) (hy : 0 ≤ y) : x ≤ |K| * y :=
  h.trans (mul_le_mul_of_nonneg_right (le_abs_self K) hy)

theorem tl_perj (CS γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (Ω : Type) [inst : MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (F : FrozenParams m n B) (S : FrozenSamples P m n B) (t : ℤ)
      (w : ℕ → ℝ) (j : ℕ), WeightClass w →
      opNorm F.C.Sout ≤ CS → opNorm F.C.Sin ≤ CS → (m : ℝ) ≤ γ * B → (n : ℝ) ≤ γ * B →
      ∀ s : ℝ, 1 ≤ s →
        0 ≤ bj w F S t j s ∧ bj w F S t j s ≤ K * w j / s ∧
        fro ((B : ℝ) • Muon.mean P (fun ω =>
            delAlpha1 w F S t j s ω • (Rs (delBufAge w F S t j ω) s *
              outer (ageU F S t j ω) (ageV F S t j ω))
          - delAlpha2 w F S t j s ω • (Xs (delBufAge w F S t j ω) s *
              outer (ageV F S t j ω) (ageV F S t j ω))) +
          bj w F S t j s • (Hmix w F S t s * F.C.Sin)) ≤ K * w j / s := by
  obtain ⟨KS, hKS⟩ := tl_S CS γ hγ
  obtain ⟨KQ, hKQ⟩ := tl_Q CS γ hγ
  obtain ⟨Kb, hKb⟩ := tl_b CS γ hγ
  obtain ⟨Kc, hKc⟩ := lem_app_drift_covariance_weights 1 one_pos CS γ hγ
  obtain ⟨Km, hKm⟩ := lem_app_drift_multiplier_ii_weights 1 one_pos CS γ hγ
  refine ⟨|KS| + |Kb| + |Kb| * |Km| * |CS| + |Kc| * |CS| + |KQ|, by positivity, ?_⟩
  intro Ω inst m n B P _ F S t w j hw hCo hCi hm hn s hs
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hw0 : 0 ≤ w j := hw.1.1 j
  have hw1 : w j ≤ 1 := hw.2.1 j
  have hCS : 0 ≤ CS := (tlb_opNorm_nonneg _).trans hCo
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast F.hB
  have hsB : 1 ≤ Real.sqrt (B : ℝ) := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hBr
  have hss : 1 ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hs
  obtain ⟨hSint, hSb⟩ := hKS Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hQint, Err, hErr, hQeq⟩ := hKQ Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨hb0, hb1⟩ := hKb Ω m n B P F S t j w hw0 hw1 hCo hCi hm hn s hs
  obtain ⟨-, hCjb, -, -⟩ := hKc Ω m n B P F S t w ⟨hw.1.1, hw.1.2.1, hw.2.1, hw.2.2⟩ hCo hCi hm hn s hs
  have hHm := hKm Ω m n B P F S t j w hw hCo hCi hm hn s hs
  have hCj := hCjb j
  -- the exact decomposition
  have hsplit : (B : ℝ) • Muon.mean P (fun ω =>
        delAlpha1 w F S t j s ω • (Rs (delBufAge w F S t j ω) s *
          outer (ageU F S t j ω) (ageV F S t j ω))
      - delAlpha2 w F S t j s ω • (Xs (delBufAge w F S t j ω) s *
          outer (ageV F S t j ω) (ageV F S t j ω))) =
      (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
          (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
      (B : ℝ) • Muon.mean P (fun ω => delAlpha2 w F S t j s ω •
          (Xs (delBufAge w F S t j ω) s * outer (ageV F S t j ω) (ageV F S t j ω))) := by
    rw [tl_mean_sub P _ _ hSint hQint, smul_sub]
  have hw2 : w j ^ 2 ≤ w j := by rw [sq]; exact mul_le_of_le_one_right hw0 hw1
  have hu0 : 0 ≤ w j / s := by positivity
  have hx1 : w j ^ 2 / s ≤ w j / s :=
    div_le_div_of_nonneg_right hw2 hspos.le
  have hx2 : w j / s ≤ 1 := by rw [div_le_one hspos]; linarith
  have hKpos : 0 ≤ |KS| + |Kb| + |Kb| * |Km| * |CS| + |Kc| * |CS| + |KQ| := by positivity
  have hKb' : Kb * w j ^ 2 / s ≤ |Kb| * (w j / s) := by
    calc Kb * w j ^ 2 / s = Kb * (w j ^ 2 / s) := by rw [mul_div_assoc]
      _ ≤ |Kb| * (w j ^ 2 / s) := mul_le_mul_of_nonneg_right (le_abs_self Kb) (by positivity)
      _ ≤ |Kb| * (w j / s) := mul_le_mul_of_nonneg_left hx1 (abs_nonneg _)
  refine ⟨hb0, ?_, ?_⟩
  · refine hb1.trans (hKb'.trans ?_)
    rw [mul_div_assoc]
    refine mul_le_mul_of_nonneg_right ?_ hu0
    have : 0 ≤ |KS| := abs_nonneg _
    have : 0 ≤ |Kb| * |Km| * |CS| := by positivity
    have : 0 ≤ |Kc| * |CS| := by positivity
    have : 0 ≤ |KQ| := abs_nonneg _
    linarith
  rw [hsplit, hQeq]
  set b := bj w F S t j s with hbdef
  have hid : (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
          (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) -
        ((b • Hj w F S t j s + Cj w F S t j s) * F.C.Sin + Err) +
        b • (Hmix w F S t s * F.C.Sin) =
      (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
          (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) +
      (-(b • ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin))) + (-(Cj w F S t j s * F.C.Sin)) + (-Err) := by
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, smul_sub]
    abel
  rw [hid]
  -- bounds on the four pieces
  have p1 : fro ((B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
          (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω)))) ≤
        |KS| * (w j / s) := by
    refine hSb.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self KS) hu0
  have hbn : b ≤ |Kb| * (w j / s) := hb1.trans hKb'
  have hHn : fro (Hj w F S t j s - Hmix w F S t s) ≤ |Km| * (w j / s) := by
    have e : Hj w F S t j s - Hmix w F S t s = (-1 : ℝ) • (Hmix w F S t s - Hj w F S t j s) := by
      rw [neg_smul, one_smul, neg_sub]
    rw [e, tlb_fro_smul, abs_neg, abs_one, one_mul]
    refine hHm.trans ?_
    calc Km * w j / (s * Real.sqrt (B : ℝ)) ≤ |Km| * w j / (s * Real.sqrt (B : ℝ)) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Km) hw0)
            (by positivity)
      _ ≤ |Km| * w j / s := by
          apply div_le_div_of_nonneg_left (by positivity) hspos
          exact le_mul_of_one_le_right hspos.le hsB
      _ = _ := by ring
  have p2 : fro (-(b • ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin))) ≤
      |Kb| * |Km| * |CS| * (w j / s) := by
    have e : -(b • ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin)) =
        (-b : ℝ) • ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin) := by
      rw [neg_smul]
    rw [e, tlb_fro_smul, abs_neg, abs_of_nonneg hb0]
    have h1 : fro ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin) ≤
        |Km| * (w j / s) * |CS| :=
      (tlb_fro_mul_le_right _ _).trans (mul_le_mul hHn (hCi.trans (le_abs_self CS))
        (tlb_opNorm_nonneg _) (by positivity))
    calc b * fro ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin)
        ≤ (|Kb| * (w j / s)) * (|Km| * (w j / s) * |CS|) :=
          mul_le_mul hbn h1 (tlb_fro_nonneg _) (by positivity)
      _ = (|Kb| * |Km| * |CS|) * ((w j / s) * (w j / s)) := by ring
      _ ≤ (|Kb| * |Km| * |CS|) * (w j / s) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc (w j / s) * (w j / s) ≤ 1 * (w j / s) :=
                mul_le_mul_of_nonneg_right hx2 hu0
            _ = _ := one_mul _
  have p3 : fro (-(Cj w F S t j s * F.C.Sin)) ≤ |Kc| * |CS| * (w j / s) := by
    have e : -(Cj w F S t j s * F.C.Sin) = (-1 : ℝ) • (Cj w F S t j s * F.C.Sin) := by
      rw [neg_smul, one_smul]
    rw [e, tlb_fro_smul, abs_neg, abs_one, one_mul]
    refine (tlb_fro_mul_le_right _ _).trans ?_
    have hc : fro (Cj w F S t j s) ≤ |Kc| * (w j / s) := by
      refine hCj.trans ?_
      calc Kc * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ))
          ≤ |Kc| * w j ^ 2 / (s * Real.sqrt s * Real.sqrt (B : ℝ)) :=
            div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Kc)
              (sq_nonneg _)) (by positivity)
        _ ≤ |Kc| * w j ^ 2 / s := by
            apply div_le_div_of_nonneg_left (by positivity) hspos
            have h1 : 1 ≤ Real.sqrt s * Real.sqrt (B : ℝ) := one_le_mul_of_one_le_of_one_le hss hsB
            calc s = s * 1 := (mul_one s).symm
              _ ≤ s * (Real.sqrt s * Real.sqrt (B : ℝ)) := mul_le_mul_of_nonneg_left h1 hspos.le
              _ = s * Real.sqrt s * Real.sqrt (B : ℝ) := by ring
        _ ≤ |Kc| * w j / s := by
            apply div_le_div_of_nonneg_right _ hspos.le
            exact mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)
        _ = _ := by ring
    calc fro (Cj w F S t j s) * opNorm F.C.Sin ≤ (|Kc| * (w j / s)) * |CS| :=
          mul_le_mul hc (hCi.trans (le_abs_self CS)) (tlb_opNorm_nonneg _) (by positivity)
      _ = _ := by ring
  have p4 : fro (-Err) ≤ |KQ| * (w j / s) := by
    have e : -Err = (-1 : ℝ) • Err := by rw [neg_smul, one_smul]
    rw [e, tlb_fro_smul, abs_neg, abs_one, one_mul]
    refine hErr.trans ?_
    calc KQ * w j ^ 2 / s ≤ |KQ| * w j ^ 2 / s :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self KQ) (sq_nonneg _))
            hspos.le
      _ ≤ |KQ| * w j / s := by
          apply div_le_div_of_nonneg_right _ hspos.le
          exact mul_le_mul_of_nonneg_left hw2 (abs_nonneg _)
      _ = _ := by ring
  set Sj := (B : ℝ) • Muon.mean P (fun ω => delAlpha1 w F S t j s ω •
          (Rs (delBufAge w F S t j ω) s * outer (ageU F S t j ω) (ageV F S t j ω))) with hSj
  set A := -(b • ((Hj w F S t j s - Hmix w F S t s) * F.C.Sin)) with hA
  set C' := -(Cj w F S t j s * F.C.Sin) with hC'
  have a1 := tlb_fro_add (Sj + A + C') (-Err)
  have a2 := tlb_fro_add (Sj + A) C'
  have a3 := tlb_fro_add Sj A
  have hfin : (|KS| + |Kb| + |Kb| * |Km| * |CS| + |Kc| * |CS| + |KQ|) * w j / s =
      (|KS| + |Kb| + |Kb| * |Km| * |CS| + |Kc| * |CS| + |KQ|) * (w j / s) := by ring
  rw [hfin]
  have hKb0 : 0 ≤ |Kb| * (w j / s) := by positivity
  linarith [p1, p2, p3, p4]

end TlPerj

section TlSum

private lemma tl_fro_zero {m n : ℕ} : fro (0 : Mat m n) = 0 := by
  unfold fro; simp

private lemma tl_fro_finsum {m n : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Mat m n) :
    fro (∑ i ∈ s, f i) ≤ ∑ i ∈ s, fro (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [tl_fro_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (tlb_fro_add _ _).trans (add_le_add_right ih _)

private lemma tl_fro_cont {m n : ℕ} : Continuous (fun a : Mat m n => fro a) := by
  unfold fro
  fun_prop

lemma tl_fro_hasSum {m n : ℕ} (f : ℕ → Mat m n) (a : Mat m n) (c : ℕ → ℝ)
    (hf : HasSum f a) (hc : Summable c) (hfc : ∀ j, fro (f j) ≤ c j)
    (hc0 : ∀ j, 0 ≤ c j) : fro a ≤ ∑' j, c j := by
  have ht := (tl_fro_cont (m := m) (n := n)).continuousAt.tendsto.comp hf
  refine le_of_tendsto ht (Filter.Eventually.of_forall fun s => ?_)
  simp only [Function.comp]
  refine (tl_fro_finsum s f).trans ?_
  exact (Finset.sum_le_sum fun j _ => hfc j).trans (hc.sum_le_tsum s (fun j _ => hc0 j))

end TlSum


/-- `thm:app-drift-mixed`(ii), snapshot `cr-2026-10-23`: the `𝓗`-bound and the `T`-bound, with one
constant `C` depending only on `(C_Σ, γ⋆)`, placed before all model data. Part (i) is L-C.9.
Source, verbatim:
```latex
\begin{theorem}[Mixed resolvent closure and tail bound]\label{thm:app-drift-mixed}
\begin{enumerate}[label=(\roman*)]
\item Under \cref{assum:app-setup-regime}, for every compact $I\subset(0,\infty)$,
\begin{equation}\label{eqn:app-drift-mixed}
\sup_{s\in I}\norm{\mathcal H(s)-T(s)}_\F\longrightarrow0 .
\end{equation}
\item In the frozen-state model under \cref{assum:data-target}, with
$\max(\Nout,\Nin)\le\gamma_\star B$, $\norm{\Sigmaout},\norm{\Sigmain}\le C_\Sigma$,
$\norm{\Ahat}_\F=1$ and weights satisfying \cref{eqn:app-drift-weights}, but
without any condition on $\norm{\Ahat}$ and for every finite dimension,
there is $C$ depending only on $(C_\Sigma,\gamma_\star)$ such that
\begin{equation}\label{eqn:app-drift-tail}
\norm{\mathcal H(s)}_\F\le\frac{C}{s}\quad(s\ge1),\qquad
\norm{T(s)}_\F\le\frac{C_\Sigma}{s}\quad(s>0).
\end{equation}
\end{enumerate}
\end{theorem}
```
-/
theorem thm_app_drift_mixed_ii (CS γ : ℝ) (hC : 0 < CS) (hγ : 0 < γ) :
    ∃ C : ℝ, ∀ (Ω : Type) [MeasurableSpace Ω] (m n B : ℕ) (P : Measure Ω)
      [IsProbabilityMeasure P] (w : ℕ → ℝ) (F : FrozenParams m n B)
      (S : FrozenSamples P m n B) (t : ℤ),
      WeightClass w → DriftBound F CS γ →
        (∀ s : ℝ, 1 ≤ s → fro (Hmix w F S t s) ≤ C / s) ∧
        (∀ s : ℝ, 0 < s → fro (Tcand w F (specOutFM F) (specInFM F) s) ≤ CS / s) := by
  obtain ⟨K, hK0, hK⟩ := tl_perj CS γ hγ.le
  refine ⟨K, ?_⟩
  intro Ω inst m n B P _ w F S t hw hDB
  refine ⟨fun s hs => ?_, fun s hs => thm_app_drift_mixed_ii_T hC hγ hw F hDB hs⟩
  obtain ⟨hCo, hCi, hmax⟩ := hDB
  have hm : (m : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_left m n)).trans hmax
  have hn : (n : ℝ) ≤ γ * B := (Nat.cast_le.2 (le_max_right m n)).trans hmax
  have hspos : 0 < s := lt_of_lt_of_le one_pos hs
  have hexact := lem_app_drift_exact_weights hw F S t s hspos
  have hsumw : Summable (fun j => K * w j / s) := (hw.1.2.1.mul_left K).div_const s
  have hper := fun j => hK Ω m n B P F S t w j hw hCo hCi hm hn s hs
  have hbS : Summable (fun j => bj w F S t j s) :=
    Summable.of_nonneg_of_le (fun j => (hper j).1) (fun j => (hper j).2.1) hsumw
  have hb : HasSum (fun j => bj w F S t j s) (bB w F S t s) := hbS.hasSum
  have hZ := hexact.add (hb.smul_const (Hmix w F S t s * F.C.Sin))
  have hbB0 : 0 ≤ bB w F S t s := tsum_nonneg fun j => (hper j).1
  have hfro := tl_fro_hasSum _ _ (fun j => K * w j / s) hZ hsumw (fun j => (hper j).2.2)
    (fun j => by have := hw.1.1 j; positivity)
  have hY := tl_fro_Y (Hmix w F S t s) F.C.Sin F.C.psdIn _ hbB0
  refine hY.trans (hfro.trans ?_)
  rw [tsum_div_const, tsum_mul_left]
  have : K * ∑' j, w j ≤ K * 1 := mul_le_mul_of_nonneg_left hw.2.2 hK0
  rw [mul_one] at this
  exact div_le_div_of_nonneg_right this hspos.le

end Muon.Drift
